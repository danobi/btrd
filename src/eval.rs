use std::fmt;

fn print_help() {
    println!("help\t\tPrint help");
    println!("quit\t\tExit debugger");
}

pub enum EvalResult {
    Ok,
    Quit,
    Err(String),
}

impl fmt::Display for EvalResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalResult::Ok => Ok(()),
            EvalResult::Quit => write!(f, "Quit"),
            EvalResult::Err(msg) => write!(f, "{}", msg),
        }
    }
}

pub fn eval(cmd: &str) -> EvalResult {
    match cmd {
        "help" => {
            print_help();
            EvalResult::Ok
        }
        "quit" => EvalResult::Quit,
        _ => EvalResult::Err("Invalid command".to_string()),
    }
}
