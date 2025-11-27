use std::env;
use std::fs;
use std::fmt;
use std::mem;

// Basic Types & Structures

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

    #[inline(always)]
    pub fn not(&self) -> Self {
        Lit(self.0 ^ 1)
    }

    #[inline(always)]
    pub fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

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
    lits: Vec<Lit>,
    #[allow(dead_code)]
    learned: bool, 
}

// Branching Strategy

pub trait BranchingStrategy {
    fn pick_branch(&mut self, solver: &Solver) -> Option<Lit>;
    fn on_conflict(&mut self, involved_vars: &[usize]);
    fn on_assign(&mut self, var: usize);
    fn on_unassign(&mut self, var: usize, old_value: bool);
}

pub struct VsidsStrategy {
    activity: Vec<f64>,
    var_inc: f64,
    var_decay: f64,
    saved_phases: Vec<bool>,
}

impl VsidsStrategy {
    pub fn new(num_vars: usize) -> Self {
        Self {
            activity: vec![0.0; num_vars],
            var_inc: 1.0,
            var_decay: 0.95, 
            saved_phases: vec![false; num_vars], 
        }
    }

    fn var_rescale_activity(&mut self) {
        for score in &mut self.activity {
            *score *= 1e-100;
        }
        self.var_inc *= 1e-100;
    }
}

impl BranchingStrategy for VsidsStrategy {
    fn pick_branch(&mut self, solver: &Solver) -> Option<Lit> {
        let mut best_var = None;
        let mut max_activity = -1.0;

        for (v, &val) in solver.assignments.iter().enumerate() {
            if val == VarValue::Unassigned {
                let score = self.activity[v];
                if score > max_activity {
                    max_activity = score;
                    best_var = Some(v);
                }
            }
        }

        match best_var {
            Some(v) => {
                let saved_is_neg = !self.saved_phases[v]; 
                Some(Lit::new(v, saved_is_neg)) 
            }
            None => None, 
        }
    }

    fn on_conflict(&mut self, involved_vars: &[usize]) {
        for &v in involved_vars {
            self.activity[v] += self.var_inc;
        }
        self.var_inc *= 1.0 / self.var_decay;
        if self.var_inc > 1e100 {
            self.var_rescale_activity();
        }
    }
    
    fn on_assign(&mut self, _var: usize) {}

    fn on_unassign(&mut self, var: usize, old_value: bool) {
        self.saved_phases[var] = old_value;
    }
}

// Solver

/// Helper Enum to handle the result of clause analysis
#[derive(Copy, Clone)] 
enum Action {
    Conflict(usize),
    Enqueue(Lit, usize),
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    watches: Vec<Vec<usize>>,
    pub assignments: Vec<VarValue>,
    level: Vec<usize>,
    reason: Vec<Option<usize>>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    q_head: usize,
    num_vars: usize,

    // -- Optimization Buffers (Recycled Memory) --
    prop_buf: Vec<usize>,
    analyze_seen: Vec<bool>,
    analyze_toclear: Vec<usize>,
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
            
            prop_buf: Vec::with_capacity(50), 
            analyze_seen: vec![false; num_vars],
            analyze_toclear: Vec::with_capacity(num_vars),
            analyze_clause: Vec::with_capacity(num_vars),
        }
    }

    pub fn add_clause(&mut self, mut lits: Vec<Lit>) -> bool {
        if lits.is_empty() { return false; }
        
        lits.sort_by_key(|l| l.to_usize());
        lits.dedup();

        if lits.len() == 1 {
            self.unchecked_enqueue(lits[0], None);
            return self.propagate().is_none(); 
        }

        let clause_idx = self.clauses.len();
        
        self.watches[lits[0].not().to_usize()].reserve(4);
        self.watches[lits[1].not().to_usize()].reserve(4);

        self.watches[lits[0].not().to_usize()].push(clause_idx);
        self.watches[lits[1].not().to_usize()].push(clause_idx);
        
        self.clauses.push(Clause { lits, learned: false });

        true
    }

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

    /// Optimized Propagate: Zero-Allocation with Action Enum
    fn propagate(&mut self) -> Option<usize> {
        let mut conflict = None;

        while self.q_head < self.trail.len() {
            let p = self.trail[self.q_head];
            self.q_head += 1;

            let falsified_lit_idx = p.to_usize();
            
            // Swap buffer to avoid allocation
            mem::swap(&mut self.watches[falsified_lit_idx], &mut self.prop_buf);
            self.watches[falsified_lit_idx].clear();

            for i in 0..self.prop_buf.len() {
                let cr_idx = self.prop_buf[i];
                
                if conflict.is_some() {
                    self.watches[falsified_lit_idx].push(cr_idx);
                    continue;
                }

                // Use small scope to borrow clauses
                let (action, stop_watching) = {
                    let clause = &mut self.clauses[cr_idx];
                    let false_lit = p.not();
                    
                    if clause.lits[0] == false_lit { clause.lits.swap(0, 1); }

                    let val_0 = Self::value_lit(&self.assignments, clause.lits[0]);
                    if val_0 == VarValue::True {
                        (None, false) 
                    } else {
                        let mut found_new = false;
                        for k in 2..clause.lits.len() {
                            if Self::value_lit(&self.assignments, clause.lits[k]) != VarValue::False {
                                clause.lits.swap(1, k);
                                self.watches[clause.lits[1].not().to_usize()].push(cr_idx);
                                found_new = true;
                                break;
                            }
                        }

                        if found_new {
                            (None, true) 
                        } else {
                            if val_0 == VarValue::False {
                                // Conflict: return Action::Conflict (wrapping usize)
                                (Some(Action::Conflict(cr_idx)), false) 
                            } else {
                                // Unit: return Action::Enqueue (wrapping Lit + usize)
                                (Some(Action::Enqueue(clause.lits[0], cr_idx)), false) 
                            }
                        }
                    }
                };

                if !stop_watching {
                    self.watches[falsified_lit_idx].push(cr_idx);
                }

                if let Some(act) = action {
                    match act {
                        Action::Conflict(idx) => conflict = Some(idx),
                        Action::Enqueue(lit, reason) => self.unchecked_enqueue(lit, Some(reason)),
                    }
                }
            }
        }
        
        conflict
    }

    fn analyze(&mut self, conflict_idx: usize) -> (Vec<Lit>, usize) {
        for &var in &self.analyze_toclear {
            self.analyze_seen[var] = false;
        }
        self.analyze_toclear.clear();
        self.analyze_clause.clear();

        let mut counter = 0; 
        let mut current_clause_idx = Some(conflict_idx);
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();

        loop {
            if let Some(c_idx) = current_clause_idx {
                let clause = &self.clauses[c_idx];
                for (i, &lit) in clause.lits.iter().enumerate() {
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

            while !self.analyze_seen[self.trail[index - 1].var()] { index -= 1; }
            index -= 1;
            let current_lit = self.trail[index];
            p = Some(current_lit);
            current_clause_idx = self.reason[current_lit.var()];
            
            self.analyze_seen[current_lit.var()] = false; 
            counter -= 1;
            if counter == 0 { break; }
        }

        if let Some(lit) = p { 
            self.analyze_clause.insert(0, lit.not()); 
        }

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
                let old_val_bool = self.assignments[var] == VarValue::True;
                self.assignments[var] = VarValue::Unassigned;
                self.reason[var] = None;
                self.level[var] = 0; 
                strategy.on_unassign(var, old_val_bool);
            }
            self.trail_lim.pop();
        }
        self.q_head = self.trail.len();
    }

    pub fn solve(&mut self, strategy: &mut dyn BranchingStrategy) -> bool {
        loop {
            if let Some(conflict_idx) = self.propagate() {
                if self.decision_level() == 0 { return false; }

                let (learned_clause, backtrack_level) = self.analyze(conflict_idx);
                let involved_vars: Vec<usize> = learned_clause.iter().map(|l| l.var()).collect();
                strategy.on_conflict(&involved_vars);
                
                self.backtrack(backtrack_level, strategy);

                if !learned_clause.is_empty() {
                    let lidx = self.clauses.len();
                    
                    if learned_clause.len() > 1 {
                        self.watches[learned_clause[0].not().to_usize()].push(lidx);
                        self.watches[learned_clause[1].not().to_usize()].push(lidx);
                    } else if learned_clause.len() == 1 {
                         self.watches[learned_clause[0].not().to_usize()].push(lidx);
                         self.watches[learned_clause[0].not().to_usize()].push(lidx); 
                    }
                    
                    let asserting_lit = learned_clause[0];
                    self.clauses.push(Clause { lits: learned_clause, learned: true });
                    self.unchecked_enqueue(asserting_lit, Some(lidx));
                }
            } else {
                match strategy.pick_branch(self) {
                    Some(next_lit) => {
                        self.trail_lim.push(self.trail.len());
                        self.unchecked_enqueue(next_lit, None);
                        strategy.on_assign(next_lit.var());
                    }
                    None => return true, 
                }
            }
        }
    }
}

// Main & Parsing

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <path_to_formula>", args[0]);
        std::process::exit(1);
    }
    let path = &args[1];

    println!("Reading formula from: {}", path);
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    let (clauses, num_vars) = parse_custom_format(&content);
    println!("Parsed {} variables and {} clauses.", num_vars, clauses.len());

    let mut solver = Solver::new(num_vars);
    for clause_lits in clauses {
        solver.add_clause(clause_lits);
    }

    let mut strategy = VsidsStrategy::new(num_vars);
    let start_time = std::time::Instant::now();
    let result = solver.solve(&mut strategy);
    let duration = start_time.elapsed();

    println!("--------------------------------------------------");
    if result {
        println!("Result: SATISFIABLE");
        println!("Time:   {:.4}s", duration.as_secs_f64());
        println!("Assignment (positive literals only):");
        
        let mut first = true;
        for (i, val) in solver.assignments.iter().enumerate() {
            if *val == VarValue::True {
                if !first { print!(" "); }
                print!("{}", i + 1);
                first = false;
            }
        }
        println!();
    } else {
        println!("Result: UNSATISFIABLE");
        println!("Time:   {:.4}s", duration.as_secs_f64());
    }
    println!("--------------------------------------------------");
}

fn parse_custom_format(content: &str) -> (Vec<Vec<Lit>>, usize) {
    let mut clauses = Vec::new();
    let mut max_var_idx = 0;

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('#') {
            continue;
        }

        let cleaned = line.replace('[', " ").replace(']', " ").replace(',', " ");
        let mut current_clause = Vec::new();
        
        for token in cleaned.split_whitespace() {
            if let Ok(val) = token.parse::<i32>() {
                if val == 0 { continue; }
                let (lit, var_idx) = parse_lit(val);
                current_clause.push(lit);
                if var_idx > max_var_idx {
                    max_var_idx = var_idx;
                }
            }
        }
        if !current_clause.is_empty() {
            clauses.push(current_clause);
        }
    }
    (clauses, max_var_idx + 1)
}

fn parse_lit(val: i32) -> (Lit, usize) {
    let var_idx = (val.abs() as usize) - 1; 
    let is_neg = val < 0;
    (Lit::new(var_idx, is_neg), var_idx)
}