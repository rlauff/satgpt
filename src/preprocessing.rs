use std::collections::{HashMap, HashSet};
use crate::{Clause, Lit};

// =========================================================================
// XOR Extraction and Gaussian Elimination
// =========================================================================

/// Represents a single XOR constraint: x1 ^ x2 ^ ... ^ xn = rhs
#[derive(Debug, Clone)]
pub struct XorConstraint {
    pub vars: Vec<usize>,
    pub rhs: bool, // true means parity is 1 (odd number of variables are true)
}

pub struct PreprocessResult {
    pub clauses: Vec<Clause>,
    pub units: Vec<Lit>,
}

#[derive(Clone, Debug)]
struct BitRow {
    chunks: Vec<u64>,
    rhs: bool,
}

impl BitRow {
    fn new(size: usize, rhs: bool) -> Self {
        let num_chunks = (size + 63) / 64;
        BitRow {
            chunks: vec![0; num_chunks],
            rhs,
        }
    }

    fn set_bit(&mut self, idx: usize) {
        let chunk = idx / 64;
        let offset = idx % 64;
        if chunk < self.chunks.len() {
            self.chunks[chunk] |= 1 << offset;
        }
    }

    fn get_bit(&self, idx: usize) -> bool {
        let chunk = idx / 64;
        let offset = idx % 64;
        if chunk < self.chunks.len() {
            (self.chunks[chunk] & (1 << offset)) != 0
        } else {
            false
        }
    }

    fn xor_with(&mut self, other: &BitRow) {
        for (c1, c2) in self.chunks.iter_mut().zip(&other.chunks) {
            *c1 ^= *c2;
        }
        self.rhs ^= other.rhs;
    }

    fn is_zero_row(&self) -> bool {
        self.chunks.iter().all(|&c| c == 0)
    }
}

pub fn preprocess(clauses: &Vec<Clause>, num_vars: usize) -> Option<PreprocessResult> {
    // 1. Identify XORs
    let (xors, indices_to_remove) = extract_xors_indices(clauses);

    if xors.is_empty() {
        return None;
    }

    // 2. Build Matrix
    let mut matrix: Vec<BitRow> = Vec::with_capacity(xors.len());
    for xor in xors.iter() {
        let mut row = BitRow::new(num_vars, xor.rhs);
        for &v in &xor.vars {
            row.set_bit(v);
        }
        matrix.push(row);
    }

    // 3. Gaussian Elimination
    let mut pivot_row_idx = 0;
    for col in 0..num_vars {
        if pivot_row_idx >= matrix.len() { break; }

        let mut pivot_found = None;
        for r in pivot_row_idx..matrix.len() {
            if matrix[r].get_bit(col) {
                pivot_found = Some(r);
                break;
            }
        }

        if let Some(r) = pivot_found {
            matrix.swap(pivot_row_idx, r);
            for i in 0..matrix.len() {
                if i != pivot_row_idx && matrix[i].get_bit(col) {
                    let (left, right) = matrix.split_at_mut(if i < pivot_row_idx { pivot_row_idx } else { i });
                    if i < pivot_row_idx {
                        left[i].xor_with(&right[0]);
                    } else {
                        right[0].xor_with(&left[pivot_row_idx]);
                    }
                }
            }
            pivot_row_idx += 1;
        }
    }

    // 4. Extract results
    let mut new_xor_clauses = Vec::new();
    let mut units = Vec::new();
    let mut replacements: HashMap<usize, (usize, bool)> = HashMap::new();
    let mut found_conflict = false;

    for row in matrix {
        if row.is_zero_row() {
            if row.rhs { found_conflict = true; break; }
            continue;
        }

        let mut vars = Vec::new();
        for (i, &chunk) in row.chunks.iter().enumerate() {
            if chunk == 0 { continue; }
            for bit in 0..64 {
                if (chunk & (1 << bit)) != 0 {
                    vars.push(i * 64 + bit);
                }
            }
        }
        
        if vars.is_empty() { continue; }

        if vars.len() == 1 {
            units.push(Lit::new(vars[0], !row.rhs));
        } else if vars.len() == 2 {
            let v1 = vars[0];
            let v2 = vars[1];
            let (target, source) = if v1 > v2 { (v1, v2) } else { (v2, v1) };
            replacements.insert(target, (source, row.rhs));
        } else if vars.len() > 8 { 
             // Avoid huge fill-in clauses, abort simplification if too messy
             return None; 
        } else {
            new_xor_clauses.extend(xor_to_cnf(&vars, row.rhs));
        }
    }

    if found_conflict {
        return Some(PreprocessResult { 
            clauses: vec![Clause { lits: vec![], learned: false }], 
            units: vec![] 
        }); 
    }

    // 5. Rebuild Clauses
    let indices_set: HashSet<usize> = indices_to_remove.into_iter().collect();
    let mut final_clauses = Vec::with_capacity(clauses.len());

    for (i, c) in clauses.iter().enumerate() {
        if !indices_set.contains(&i) {
            let mut new_lits = apply_replacements(&c.lits, &replacements);
            if simplify_clause(&mut new_lits) { continue; }
            if new_lits.is_empty() { 
                return Some(PreprocessResult { clauses: vec![Clause { lits: vec![], learned: false }], units: vec![] }); 
            }
            final_clauses.push(Clause { lits: new_lits, learned: c.learned });
        }
    }

    for c in new_xor_clauses {
        let mut new_lits = apply_replacements(&c.lits, &replacements);
        if simplify_clause(&mut new_lits) { continue; }
        if new_lits.is_empty() { 
             return Some(PreprocessResult { clauses: vec![Clause { lits: vec![], learned: false }], units: vec![] }); 
        }
        final_clauses.push(Clause { lits: new_lits, learned: false });
    }

    // Always return result if we found replacements, even if clause count is similar
    if final_clauses.len() >= clauses.len() && units.is_empty() && replacements.is_empty() {
        return None;
    }

    Some(PreprocessResult { clauses: final_clauses, units })
}

fn extract_xors_indices(clauses: &Vec<Clause>) -> (Vec<XorConstraint>, Vec<usize>) {
    let mut buckets: HashMap<Vec<usize>, Vec<usize>> = HashMap::new();
    
    let max_xor_size = 12; 

    for (idx, clause) in clauses.iter().enumerate() {
        if clause.lits.len() > max_xor_size || clause.lits.len() < 2 {
            continue;
        }
        let mut vars: Vec<usize> = clause.lits.iter().map(|l| l.var()).collect();
        vars.sort_unstable();
        vars.dedup();
        
        if vars.len() == clause.lits.len() {
            buckets.entry(vars).or_default().push(idx);
        }
    }

    let mut found_xors = Vec::new();
    let mut indices_to_remove = Vec::new();

    for (vars, indices) in buckets {
        let k = vars.len();
        let expected_count = 1 << (k - 1); 

        if indices.len() >= expected_count {
            if let Some(rhs) = check_parity(clauses, &indices) {
                found_xors.push(XorConstraint { vars, rhs });
                indices_to_remove.extend(indices);
            }
        }
    }

    (found_xors, indices_to_remove)
}

fn check_parity(all_clauses: &[Clause], indices: &[usize]) -> Option<bool> {
    let mut determined_rhs = None;

    for &idx in indices {
        let clause = &all_clauses[idx];
        let num_negated = clause.lits.iter().filter(|l| l.is_neg()).count();
        
        // Logic: An XOR clause forbids a specific parity.
        // Even parity forbidden (num_negated is even) => implied XOR parity is Odd (rhs=1)
        // Odd parity forbidden (num_negated is odd) => implied XOR parity is Even (rhs=0)
        
        let forbidden_is_odd = num_negated % 2 != 0;
        let implied_rhs = !forbidden_is_odd;

        if let Some(existing) = determined_rhs {
            if existing != implied_rhs { 
                // Inconsistent parity in bucket (or duplicate consistent clause)
                // If it's a duplicate of the same forbidden state, it's fine.
                // But check_parity here just checks global consistency.
                // If we have contradictory clauses in the bucket (e.g. forbid 000 AND forbid 001), 
                // that's not an XOR, that's a conflict or just random clauses.
                // For valid XORs, all clauses must enforce the same rhs.
                return None; 
            }
        } else {
            determined_rhs = Some(implied_rhs);
        }
    }
    determined_rhs
}

fn xor_to_cnf(vars: &[usize], rhs: bool) -> Vec<Clause> {
    let mut result = Vec::new();
    let n = vars.len();
    let total_combs: usize = 1 << n;
    let target_negations_parity = if rhs { 0 } else { 1 };
    
    for i in 0..total_combs {
        if i.count_ones() as usize % 2 == target_negations_parity {
            let mut lits = Vec::with_capacity(n);
            for (bit_idx, &v) in vars.iter().enumerate() {
                let is_neg = (i >> bit_idx) & 1 == 1;
                lits.push(Lit::new(v, is_neg));
            }
            result.push(Clause { lits, learned: false });
        }
    }
    result
}

fn apply_replacements(lits: &[Lit], map: &HashMap<usize, (usize, bool)>) -> Vec<Lit> {
    let mut new_lits = Vec::with_capacity(lits.len());
    for &lit in lits {
        let mut var = lit.var();
        let mut is_neg = lit.is_neg();
        let mut depth = 0;
        while let Some((replacement_var, invert)) = map.get(&var) {
            var = *replacement_var;
            if *invert { is_neg = !is_neg; }
            depth += 1;
            if depth > 100 { break; } 
        }
        new_lits.push(Lit::new(var, is_neg));
    }
    new_lits
}

fn simplify_clause(lits: &mut Vec<Lit>) -> bool {
    lits.sort_by_key(|l| l.to_usize());
    lits.dedup();
    for i in 0..lits.len().saturating_sub(1) {
        if lits[i].var() == lits[i+1].var() { return true; }
    }
    false
}