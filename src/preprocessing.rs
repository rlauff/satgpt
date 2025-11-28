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
    // 1. Identify XORs (Semantic Extraction)
    // We switched from syntactic counting to semantic truth-table checks
    // to handle hidden XORs (e.g. formed by AND/NAND gates).
    let (xors, indices_to_remove) = extract_semantic_xors(clauses, num_vars);

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
        } else if vars.len() > 12 { 
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
    // Remove clauses that were part of the identified semantic XORs
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

/// Extracts XOR gates by checking variable relationships semantically via truth tables.
/// This detects XORs even if they are hidden in AND/NAND structures.
fn extract_semantic_xors(clauses: &Vec<Clause>, num_vars: usize) -> (Vec<XorConstraint>, Vec<usize>) {
    let mut xors = Vec::new();
    let mut used_clauses = HashSet::new();

    // Build an adjacency list: Variable -> List of Clause Indices
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_vars];
    for (i, c) in clauses.iter().enumerate() {
        // Skip huge clauses for performance, likely not part of small local gates
        if c.lits.len() > 6 { continue; } 
        for lit in &c.lits {
            adj[lit.var()].push(i);
        }
    }

    // Iterate over every variable, treating it as a potential "output" of a gate
    for var in 0..num_vars {
        let clauses_indices = &adj[var];
        if clauses_indices.is_empty() { continue; }

        // Collect neighbors (other variables in the same clauses)
        let mut neighbors = HashSet::new();
        for &c_idx in clauses_indices {
            for lit in &clauses[c_idx].lits {
                if lit.var() != var {
                    neighbors.insert(lit.var());
                }
            }
        }

        // Filter: We only look for small gates (e.g. 2 to 4 inputs)
        // A standard 2-bit XOR has 2 inputs. 
        if neighbors.len() < 2 || neighbors.len() > 4 { continue; }

        let neighbor_vec: Vec<usize> = neighbors.into_iter().collect();

        // Perform semantic check: Does 'var' behave like XOR(neighbors)?
        if let Some(rhs) = check_semantic_xor_logic(var, &neighbor_vec, clauses_indices, clauses) {
            
            // Found a valid XOR constraint
            let mut xor_vars = neighbor_vec.clone();
            xor_vars.push(var); // The full constraint is inputs ^ output = const
            xors.push(XorConstraint { vars: xor_vars, rhs });

            // Mark involved clauses for removal.
            // We assume if the clauses fully define the XOR, they are redundant 
            // once we have the algebraic definition.
            for &idx in clauses_indices {
                let c = &clauses[idx];
                // Only remove clauses that are STRICTLY composed of these vars.
                // If a clause has other vars, it constrains something else too.
                let all_in_xor = c.lits.iter().all(|l| l.var() == var || neighbor_vec.contains(&l.var()));
                if all_in_xor {
                    used_clauses.insert(idx);
                }
            }
        }
    }

    (xors, used_clauses.into_iter().collect())
}

/// Helper function to check truth table logic.
/// Verifies if 'target' is functionally determined by 'inputs' as an XOR relationship.
fn check_semantic_xor_logic(
    target: usize, 
    inputs: &[usize], 
    relevant_clause_indices: &[usize], 
    clauses: &Vec<Clause>
) -> Option<bool> {
    let num_inputs = inputs.len();
    let limit = 1 << num_inputs;
    
    // We want to determine if: target == parity(inputs) ^ C
    // 'relation' will store (target_val ^ input_parity). This must be constant.
    let mut expected_relation: Option<bool> = None; 

    for i in 0..limit {
        // 1. Build Input Assignment and calculate input parity
        let mut input_parity = false;
        let mut current_assignment = HashMap::with_capacity(num_inputs);
        
        for (bit, &inp_var) in inputs.iter().enumerate() {
            let val = (i >> bit) & 1 == 1;
            current_assignment.insert(inp_var, val);
            if val { input_parity = !input_parity; }
        }

        // 2. Check what the clauses force 'target' to be
        let mut forced_true = false; 
        let mut forced_false = false;

        for &c_idx in relevant_clause_indices {
            let clause = &clauses[c_idx];
            
            // Check if clause is already satisfied by the inputs alone
            let mut satisfied_by_inputs = false;
            let mut target_lit: Option<Lit> = None;

            for lit in &clause.lits {
                if lit.var() == target {
                    target_lit = Some(*lit);
                } else if let Some(&val) = current_assignment.get(&lit.var()) {
                    // Lit is satisfied if (val=True & !neg) or (val=False & neg)
                    if (val && !lit.is_neg()) || (!val && lit.is_neg()) {
                        satisfied_by_inputs = true;
                        break; 
                    }
                }
            }

            if satisfied_by_inputs {
                continue; // Clause provides no info about target for this assignment
            }

            // If not satisfied by inputs, 'target' MUST satisfy this clause.
            if let Some(t_lit) = target_lit {
                if t_lit.is_neg() {
                    // Literal is '-target'. To satisfy clause, '-target' must be True => target must be False.
                    forced_false = true;
                } else {
                    // Literal is '+target'. target must be True.
                    forced_true = true;
                }
            } else {
                // Clause has no target lit, and is not satisfied by inputs.
                // This means this input combination is strictly forbidden.
                // An XOR gate must be total (defined for all inputs), so this isn't an XOR.
                return None; 
            }
        }

        // 3. Analyze forcing results
        if forced_true && forced_false {
            return None; // Conflict: Logic is UNSAT for this input combo.
        }
        if !forced_true && !forced_false {
            return None; // Under-constrained: Not a functional definition (target can be anything).
        }

        let target_val = forced_true;
        
        // Calculate the relation: target_val ^ input_parity
        // If this is constant for all rows, we have an XOR (or XNOR).
        let relation = target_val ^ input_parity; 

        if let Some(existing_rel) = expected_relation {
            if existing_rel != relation {
                return None; // Inconsistent logic (not an XOR).
            }
        } else {
            expected_relation = Some(relation);
        }
    }

    // If relation is true: target != parity => target ^ parity = 1 => Odd Parity (rhs=1)
    // If relation is false: target == parity => target ^ parity = 0 => Even Parity (rhs=0)
    expected_relation
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