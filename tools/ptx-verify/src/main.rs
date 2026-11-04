use std::{env, fs, process};

mod parser;

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        return Err(
            "usage: ptx-verify INPUT.ptx OUTPUT.lean (translation only; run Lean to verify)".into(),
        );
    }
    let source = fs::read_to_string(&args[1]).map_err(|e| e.to_string())?;
    let program = parser::parse(&source)?;
    fs::write(&args[2], program.emit()).map_err(|e| e.to_string())?;
    println!(
        "translated {} instructions; no verification verdict (Lean contracts required)",
        program.code.len()
    );
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("ptx-verify: {e}");
        process::exit(2);
    }
}
