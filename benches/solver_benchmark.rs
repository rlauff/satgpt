use criterion::{criterion_group, criterion_main, Criterion};
use satgpt::run_solver_on_content;
use std::fs;
use std::path::Path;

fn bench_cnf_folder(c: &mut Criterion) {
    let bench_dir_str = "cnf/bench";
    let bench_dir = Path::new(bench_dir_str);

    match fs::canonicalize(bench_dir) {
        Ok(abs_path) => println!("\nLooking for benchmarks in: {:?}", abs_path),
        Err(e) => {
            eprintln!("\nERROR: Could not find directory '{}'.", bench_dir_str);
            eprintln!("Current working directory: {:?}", std::env::current_dir());
            eprintln!("System Error: {}", e);
            return;
        }
    }

    let mut group = c.benchmark_group("Benchmarks");
    
    group.sample_size(10); 
    group.measurement_time(std::time::Duration::from_secs(10));

    // bench on all files found in the folder
    let entries = fs::read_dir(bench_dir).expect("Failed to read directory");
    
    let mut count = 0;
    for entry in entries {
        let entry = entry.expect("Error reading entry");
        let path = entry.path();
        
        // check if input is ok
        let is_cnf = path.extension()
            .and_then(|s| s.to_str())
            .map(|s| s.to_lowercase() == "cnf")
            .unwrap_or(false);

        if is_cnf {
            let file_name = path.file_name().unwrap().to_string_lossy().to_string();
            
            let content = fs::read_to_string(&path).expect("Failed to read file");

            group.bench_function(file_name, |b| {
                b.iter(|| {
                    // running benchmark
                    run_solver_on_content(&content,false)
                })
            });
            count += 1;
        }
    }
    
    if count == 0 {
        println!("WARNING: No .cnf files found in {:?}", bench_dir);
    }

    group.finish();
}

criterion_group!(benches, bench_cnf_folder);
criterion_main!(benches);