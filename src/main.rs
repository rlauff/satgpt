use std::env;
use std::fs;
use satgpt::*; // Import from the library

fn main() {
    let args: Vec<String> = env::args().collect();
    
    // Simple argument parser: find the first argument that doesn't start with "--"
    let path = args.iter().skip(1).find(|&a| !a.starts_with("--"));

    if path.is_none() {
        eprintln!("Usage: {} <path_to_formula>", args[0]);
        std::process::exit(1);
    }
    let path = path.unwrap();

    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => { eprintln!("Error reading file: {}", e); std::process::exit(1); }
    };

    println!("Solving {}", path);
    let start = std::time::Instant::now();
    
    // Call the library function
    let result = run_solver_on_content(&content);
    
    let duration = start.elapsed();

    println!("--------------------------------------------------");
    if result {
        println!("Result: SATISFIABLE");
    } else {
        println!("Result: UNSATISFIABLE");
    }
    println!("Time:   {:.4}s", duration.as_secs_f64());
    println!("--------------------------------------------------");
}

// Integration Tests
#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;

    #[test]
    fn test_satisfiable_instances() {
        let sat_dir = PathBuf::from("cnf/sat");
        if !sat_dir.exists() { return; }

        for entry in fs::read_dir(sat_dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().and_then(|s| s.to_str()) == Some("cnf") {
                println!("Testing SAT: {:?}", path);
                let content = fs::read_to_string(&path).unwrap();
                let result = run_solver_on_content(&content);
                assert!(result, "Failed: {:?} should be SAT", path);
            }
        }
    }

    #[test]
    fn test_unsatisfiable_instances() {
        let unsat_dir = PathBuf::from("cnf/unsat");
        if !unsat_dir.exists() { return; }

        for entry in fs::read_dir(unsat_dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().and_then(|s| s.to_str()) == Some("cnf") {
                println!("Testing UNSAT: {:?}", path);
                let content = fs::read_to_string(&path).unwrap();
                let result = run_solver_on_content(&content);
                assert!(!result, "Failed: {:?} should be UNSAT", path);
            }
        }
    }
}