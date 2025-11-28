use std::fmt;

// Import the new module
pub mod preprocessing;

// =========================================================================
// Core Types (Must be pub for benchmarking)
// =========================================================================

/// Represents a literal (a variable or its negation).
/// We map variable `v` to `2*v` (positive) and `2*v + 1` (negative).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Lit(u32);

impl Lit {
    #[inline(always)]
    pub fn new(var: usize, is_negated: bool) -> Self {
        Lit(((var << 1) as u32) | (is_negated as u32))
    }

    #[inline(always)]
    pub fn var(&self) -> usize {
        (self.0 >> 1) as usize
    }

    #[inline(always)]
    pub fn is_neg(&self) -> bool {
        (self.0 & 1) != 0
    }

    /// Fast negation: XOR with 1 flips the last bit (0 -> 1, 1 -> 0).
    #[inline(always)]
    pub fn not(&self) -> Self {
        Lit(self.0 ^ 1)
    }

    #[inline(always)]
    pub fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

// Pretty printing for debugging (e.g., "-1", "+2")
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.is_neg() { "-" } else { "+" }, self.var())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum VarValue {
    Unassigned,
    True,
    False,
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub lits: Vec<Lit>,
    #[allow(dead_code)]
    pub learned: bool,
}

/// A "Watcher" is a reference to a clause that is watching a specific literal.
/// If the blocker is True, the clause is satisfied, and we don't need to look at the Clause in heap memory.
#[derive(Debug, Copy, Clone)]
struct Watcher {
    clause_idx: u32,
    blocker: Lit, 
}

// =========================================================================
// Branching Strategy
// =========================================================================

pub trait BranchingStrategy {
    /// Decides which variable to assign next. Returns None if SAT.
    fn pick_branch(&mut self, solver: &Solver) -> Option<Lit>;
    
    // Hooks for heuristics to update their state
    fn on_conflict(&mut self, involved_vars: &[usize]);
    fn on_assign(&mut self, var: usize);
    fn on_unassign(&mut self, var: usize, old_value: bool);
}

pub struct RandomStrategy {
    rng_state: u64,
    num_vars: usize,
}

impl RandomStrategy {
    pub fn new(num_vars: usize) -> Self {
        Self {
            rng_state: 123456789, // Fixed seed for reproducibility
            num_vars,
        }
    }

    /// Xorshift algorithm: Fast, lightweight pseudo-random numbers
    fn next_rand(&mut self) -> usize {
        let mut x = self.rng_state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng_state = x;
        x as usize
    }
}

impl BranchingStrategy for RandomStrategy {
    fn pick_branch(&mut self, solver: &Solver) -> Option<Lit> {
        // 1. Pick a random start index
        let start = self.next_rand() % self.num_vars;
        
        // 2. Linear scan from start to find the first Unassigned variable.
        // This guarantees we always find a variable if one exists.
        for i in 0..self.num_vars {
            let idx = (start + i) % self.num_vars;
            if solver.assignments[idx] == VarValue::Unassigned {
                // Pick random polarity (True/False)
                let is_neg = (self.next_rand() % 2) == 0;
                return Some(Lit::new(idx, is_neg));
            }
        }
        None // All variables assigned -> SAT
    }

    // Random strategy is stateless regarding history
    fn on_conflict(&mut self, _involved_vars: &[usize]) {}
    fn on_assign(&mut self, _var: usize) {}
    fn on_unassign(&mut self, _var: usize, _old_value: bool) {}
}

// =========================================================================
// solver
// =========================================================================

#[derive(Copy, Clone)]
enum Action {
    Conflict(usize),      // A clause became empty -> Conflict
    Enqueue(Lit, usize),  // A unit clause implies a literal
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    // Map: Literal -> List of Clauses watching this literal
    watches: Vec<Vec<Watcher>>, 
    
    pub assignments: Vec<VarValue>,
    level: Vec<usize>,          // Decision level of assignment
    reason: Vec<Option<usize>>, // Clause that forced this assignment (None = Decision)
    
    trail: Vec<Lit>,       // Chronological stack of assignments
    trail_lim: Vec<usize>, // Indices in trail separating decision levels
    q_head: usize,         // Queue pointer for propagation
    num_vars: usize,       // Added num_vars to struct for easy access
    
    // We reuse these vectors during conflict analysis to avoid heap allocation overhead.
    analyze_seen: Vec<bool>,
    analyze_toclear: Vec<usize>, // Tracks which bits in 'seen' we set to true
    analyze_clause: Vec<Lit>,
}

impl Solver {
    pub fn new(num_vars: usize) -> Self {
        Solver {
            clauses: Vec::new(),
            watches: vec![Vec::new(); num_vars * 2],
            assignments: vec![VarValue::Unassigned; num_vars],
            level: vec![0; num_vars],
            reason: vec![None; num_vars],
            trail: Vec::with_capacity(num_vars),
            trail_lim: Vec::new(),
            q_head: 0,
            num_vars,
            
            // Pre-allocate buffers
            analyze_seen: vec![false; num_vars],
            analyze_toclear: Vec::with_capacity(num_vars),
            analyze_clause: Vec::with_capacity(num_vars),
        }
    }

    /// Adds a clause to the formula and sets up watchers.
    pub fn add_clause(&mut self, mut lits: Vec<Lit>) -> bool {
        if lits.is_empty() { return false; } // Empty clause = UNSAT
        
        // Normalize clause
        lits.sort_by_key(|l| l.to_usize());
        lits.dedup();

        // Handle Unit Clause (size 1) immediately
        if lits.len() == 1 {
            self.unchecked_enqueue(lits[0], None);
            return self.propagate().is_none(); 
        }

        let clause_idx = self.clauses.len() as u32;
        // Watch the first two literals. The others don't need to be watched initially.
        // We use the "other" literal as the cache blocker.
        self.watches[lits[0].not().to_usize()].push(Watcher { clause_idx, blocker: lits[1] });
        self.watches[lits[1].not().to_usize()].push(Watcher { clause_idx, blocker: lits[0] });
        
        self.clauses.push(Clause { lits, learned: false });
        true
    }

    /// Helper to clear and rebuild watches.
    /// This is needed after preprocessing modifies the clause database.
    fn rebuild_watches(&mut self) {
        // Clear all watch lists
        for w in &mut self.watches {
            w.clear();
        }

        // Re-add watchers for all clauses
        for (i, clause) in self.clauses.iter().enumerate() {
            if clause.lits.len() > 1 {
                let c_idx = i as u32;
                self.watches[clause.lits[0].not().to_usize()].push(Watcher { clause_idx: c_idx, blocker: clause.lits[1] });
                self.watches[clause.lits[1].not().to_usize()].push(Watcher { clause_idx: c_idx, blocker: clause.lits[0] });
            }
        }
    }

    /// Assigns a value to a literal and adds it to the propagation trail.
    #[inline(always)]
    fn unchecked_enqueue(&mut self, lit: Lit, reason: Option<usize>) {
        let var = lit.var();
        if self.assignments[var] != VarValue::Unassigned { return; }
        
        self.assignments[var] = if lit.is_neg() { VarValue::False } else { VarValue::True };
        self.level[var] = self.decision_level();
        self.reason[var] = reason;
        self.trail.push(lit);
    }

    #[inline(always)]
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    #[inline(always)]
    fn value_lit(assignments: &[VarValue], lit: Lit) -> VarValue {
        let v = assignments[lit.var()];
        match v {
            VarValue::Unassigned => VarValue::Unassigned,
            VarValue::True => if lit.is_neg() { VarValue::False } else { VarValue::True },
            VarValue::False => if lit.is_neg() { VarValue::True } else { VarValue::False },
        }
    }

    /// The heart of the solver: Boolean Constraint Propagation (BCP).
    /// Uses the Two-Watched Literals scheme with Blocking Literals.
    fn propagate(&mut self) -> Option<usize> {
        let mut conflict = None;

        while self.q_head < self.trail.len() {
            let p = self.trail[self.q_head];
            self.q_head += 1;

            // 'p' is True. We process clauses watching '!p' (because '!p' became False).
            let falsified_lit_idx = p.to_usize();
            
            // Take the vector out of 'self' to iterate while mutating 'self'.
            // This is a pointer swap, very cheap.
            let mut watchers = std::mem::take(&mut self.watches[falsified_lit_idx]);
            
            let mut i = 0;
            let mut j = 0; // 'j' tracks the position of watchers we keep

            while i < watchers.len() {
                let watcher = watchers[i];
                let cr_idx = watcher.clause_idx as usize;
                
                // If we already found a conflict earlier in this loop, just keep the rest and exit later
                if conflict.is_some() {
                    watchers[j] = watchers[i];
                    j += 1; i += 1; continue;
                }

                // If the blocker is True, the clause is satisfied. We don't even need to look at memory.
                if Self::value_lit(&self.assignments, watcher.blocker) == VarValue::True {
                    watchers[j] = watchers[i]; 
                    j += 1; i += 1; continue;
                }

                // Cache Miss Here: We must inspect the clause in heap memory
                let (action, stop_watching) = {
                    let clause = &mut self.clauses[cr_idx];
                    let false_lit = p.not();
                    
                    // Invariant: The watched literals are at index 0 and 1.
                    // Ensure false_lit is at index 1.
                    if clause.lits[0] == false_lit { clause.lits.swap(0, 1); }

                    // If the other watched literal (index 0) is True, clause is satisfied.
                    if Self::value_lit(&self.assignments, clause.lits[0]) == VarValue::True {
                        watchers[i].blocker = clause.lits[0]; // Update blocker for next time
                        (None, false) // Keep watching
                    } else {
                        // Look for a new literal to watch (that isn't False)
                        let mut found_new = false;
                        for k in 2..clause.lits.len() {
                            if Self::value_lit(&self.assignments, clause.lits[k]) != VarValue::False {
                                clause.lits.swap(1, k);
                                // Add to the OTHER literal's watch list
                                self.watches[clause.lits[1].not().to_usize()].push(Watcher {
                                    clause_idx: cr_idx as u32,
                                    blocker: clause.lits[0] 
                                });
                                found_new = true;
                                break;
                            }
                        }

                        if found_new {
                            (None, true) // Stop watching on this list (moved to another)
                        } else {
                            // No new watcher found.
                            // If index 0 is False, both watchers are False -> Conflict!
                            if Self::value_lit(&self.assignments, clause.lits[0]) == VarValue::False {
                                (Some(Action::Conflict(cr_idx)), false) 
                            } else {
                                // Index 0 is Unassigned -> Unit Propagation!
                                (Some(Action::Enqueue(clause.lits[0], cr_idx)), false) 
                            }
                        }
                    }
                };

                if !stop_watching {
                    watchers[j] = watchers[i];
                    j += 1;
                }

                if let Some(act) = action {
                    match act {
                        Action::Conflict(idx) => conflict = Some(idx),
                        Action::Enqueue(lit, reason) => self.unchecked_enqueue(lit, Some(reason)),
                    }
                }
                i += 1;
            }
            
            // Put the filtered list back into self.watches
            watchers.truncate(j);
            self.watches[falsified_lit_idx] = watchers;

            if let Some(c) = conflict { return Some(c); }
        }
        None
    }

    /// 1-UIP Conflict Analysis.
    /// Returns the learned clause and the backtracking level.
    fn analyze(&mut self, conflict_idx: usize) -> (Vec<Lit>, usize) {
        // Fast reset of analysis buffers (O(k) where k is variables involved)
        for &var in &self.analyze_toclear { self.analyze_seen[var] = false; }
        self.analyze_toclear.clear();
        self.analyze_clause.clear();

        let mut counter = 0; // Number of literals from current decision level
        let mut current_clause_idx = Some(conflict_idx);
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();

        loop {
            if let Some(c_idx) = current_clause_idx {
                let clause = &self.clauses[c_idx];
                for (i, &lit) in clause.lits.iter().enumerate() {
                    // Skip the literal we are resolving on (unless it's the very first iteration)
                    if i == 0 && p.is_some() && lit == p.unwrap() { continue; }
                    
                    let var = lit.var();
                    if !self.analyze_seen[var] && self.level[var] > 0 {
                        self.analyze_seen[var] = true;
                        self.analyze_toclear.push(var);
                        
                        if self.level[var] == self.decision_level() { 
                            counter += 1; 
                        } else { 
                            self.analyze_clause.push(lit); 
                        }
                    }
                }
            }

            // Find next literal on trail that is involved in conflict
            while !self.analyze_seen[self.trail[index - 1].var()] { index -= 1; }
            index -= 1;
            let current_lit = self.trail[index];
            
            p = Some(current_lit);
            current_clause_idx = self.reason[current_lit.var()];
            
            self.analyze_seen[current_lit.var()] = false; 
            counter -= 1;
            
            // If counter is 0, we found the First Unique Implication Point
            if counter == 0 { break; }
        }

        if let Some(lit) = p { self.analyze_clause.insert(0, lit.not()); }

        let backtrack_level = if self.analyze_clause.len() > 1 {
            self.analyze_clause.iter().skip(1).map(|l| self.level[l.var()]).max().unwrap_or(0)
        } else { 0 };

        (self.analyze_clause.clone(), backtrack_level)
    }

    fn backtrack(&mut self, level: usize, strategy: &mut dyn BranchingStrategy) {
        while self.decision_level() > level {
            let limit = *self.trail_lim.last().unwrap();
            while self.trail.len() > limit {
                let lit = self.trail.pop().unwrap();
                let var = lit.var();
                let old_val = self.assignments[var] == VarValue::True;
                
                self.assignments[var] = VarValue::Unassigned;
                self.reason[var] = None;
                self.level[var] = 0; 
                
                strategy.on_unassign(var, old_val);
            }
            self.trail_lim.pop();
        }
        self.q_head = self.trail.len();
    }

    /// Main CDCL Loop
    pub fn solve(&mut self, strategy: &mut dyn BranchingStrategy, verbose: bool) -> bool {
        // == PREPROCESSING STEP ==
        if verbose { println!("Running Preprocessing: Gaussian Elimination + Substitution..."); }
        
        // Pass reference. Only replace if result is Some(...) indicating actual simplification.
        if let Some(result) = preprocessing::preprocess(&self.clauses, self.num_vars) {
            if verbose {
                println!("Preprocessing successful.");
                println!("  - Original clauses: {}", self.clauses.len());
                println!("  - New clauses: {}", result.clauses.len());
                println!("  - Found Units: {}", result.units.len());
            }

            self.clauses = result.clauses;
            self.rebuild_watches(); // Rebuild watches for the new clause set
            
            // Apply found unit literals
            for lit in result.units {
                self.unchecked_enqueue(lit, None);
            }
        } else {
            if verbose { println!("Preprocessing found no simplifications. Keeping original clauses."); }
            // Do NOT rebuild watches, do NOT touch self.clauses. Fast path.
        }

        loop {
            // 1. Propagate assignments
            if let Some(conflict_idx) = self.propagate() {
                // Conflict found!
                if self.decision_level() == 0 { return false; } // Conflict at root = UNSAT

                // 2. Analyze conflict
                let (learned_clause, backtrack_level) = self.analyze(conflict_idx);
                let involved_vars: Vec<usize> = learned_clause.iter().map(|l| l.var()).collect();
                strategy.on_conflict(&involved_vars);

                // 3. Backtrack
                self.backtrack(backtrack_level, strategy);

                // 4. Learn Clause & Assert
                if !learned_clause.is_empty() {
                    let lidx = self.clauses.len() as u32;
                    let c0 = learned_clause[0];
                    let c1 = if learned_clause.len() > 1 { learned_clause[1] } else { c0 };
                    
                    if learned_clause.len() > 1 {
                        self.watches[c0.not().to_usize()].push(Watcher { clause_idx: lidx, blocker: c1 });
                        self.watches[c1.not().to_usize()].push(Watcher { clause_idx: lidx, blocker: c0 });
                    } else {
                         // Unit learned clause
                         self.watches[c0.not().to_usize()].push(Watcher { clause_idx: lidx, blocker: c0 });
                         self.watches[c0.not().to_usize()].push(Watcher { clause_idx: lidx, blocker: c0 });
                    }
                    
                    self.clauses.push(Clause { lits: learned_clause, learned: true });
                    self.unchecked_enqueue(c0, Some(lidx as usize));
                }
            } else {
                // No conflict. Pick next decision.
                match strategy.pick_branch(self) {
                    Some(lit) => {
                        self.trail_lim.push(self.trail.len());
                        self.unchecked_enqueue(lit, None);
                        strategy.on_assign(lit.var());
                    }
                    None => return true, // All assigned -> SAT
                }
            }
        }
    }
}

// =========================================================================
// Helpers for Parsing and Running
// =========================================================================

/// Parses simple string format "[1, -2, 3]" or "1 -2 3"
pub fn parse_custom_format(content: &str) -> (Vec<Vec<Lit>>, usize) {
    let mut clauses = Vec::new();
    let mut max_var_idx = 0;
    
    // Check if "p cnf" exists. If so, we should skip everything before it.
    let start_parsing = content.lines().position(|l| l.starts_with("p cnf"));
    
    // Create an iterator that either starts from "p cnf" + 1 or from the beginning
    let lines_iter = match start_parsing {
        Some(idx) => content.lines().skip(idx + 1),
        None => content.lines().skip(0),
    };

    for line in lines_iter {
        let line = line.trim();
        // Skip comments and empty lines
        if line.is_empty() || line.starts_with('c') || line.starts_with('%') || line.starts_with('0') { continue; }
        
        // Sanitize input
        let cleaned = line.replace('[', " ").replace(']', " ").replace(',', " ");
        let mut current_clause = Vec::new();
        
        for token in cleaned.split_whitespace() {
            if let Ok(val) = token.parse::<i32>() {
                if val == 0 { continue; } // ignore DIMACS trailing zeros
                let (lit, var_idx) = parse_lit(val);
                current_clause.push(lit);
                if var_idx > max_var_idx { max_var_idx = var_idx; }
            }
        }
        if !current_clause.is_empty() { clauses.push(current_clause); }
    }
    (clauses, max_var_idx + 1)
}

pub fn parse_lit(val: i32) -> (Lit, usize) {
    let var_idx = (val.abs() as usize) - 1; 
    let is_neg = val < 0;
    (Lit::new(var_idx, is_neg), var_idx)
}

/// Convenience function to parse and solve a string content
pub fn run_solver_on_content(content: &str, verbose: bool) -> bool {
    let (clauses, num_vars) = parse_custom_format(content);
    let mut solver = Solver::new(num_vars);
    for clause_lits in clauses {
        solver.add_clause(clause_lits);
    }
    let mut strategy = RandomStrategy::new(num_vars);
    solver.solve(&mut strategy, verbose)
}