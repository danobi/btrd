use anyhow::{bail, Result};
use log::{error, info};
use rustyline::error::ReadlineError;
use rustyline::{config::Config as EditorConfig, Editor, Helper};
use simplelog::{Config as LogConfig, LevelFilter, SimpleLogger};
use structopt::StructOpt;

mod ast;
mod eval;
mod parse;
mod repl;

use eval::{eval, EvalResult};
use repl::ReplHelper;

const HISTORY_FILE: &str = ".btrd_history";
const PROMPT: &str = "(btrd) ";

#[derive(StructOpt)]
struct Opt {
    /// Show debug output
    #[structopt(short, long)]
    debug: bool,
}

fn init_logging(debug: bool) -> Result<()> {
    let filter = if debug {
        LevelFilter::Info
    } else {
        LevelFilter::Error
    };

    match SimpleLogger::init(filter, LogConfig::default()) {
        Ok(_) => Ok(()),
        Err(e) => bail!("Failed to init logger: {}", e),
    }
}

fn init_editor() -> Editor<ReplHelper> {
    let config = EditorConfig::builder().auto_add_history(true).build();
    let mut editor = Editor::with_config(config);
    let validator = ReplHelper::new();
    editor.set_helper(Some(validator));

    editor
}

fn init_history<H: Helper>(editor: &mut Editor<H>) {
    let _ = editor.load_history(HISTORY_FILE);
}

fn save_history<H: Helper>(editor: &mut Editor<H>) -> Result<()> {
    match editor.save_history(HISTORY_FILE) {
        Ok(_) => Ok(()),
        Err(e) => bail!("Failed to save history: {}", e),
    }
}

fn welcome() {
    println!(
        r#"btrd (the btrfs debugger) v{}"#,
        env!("CARGO_PKG_VERSION")
    );
    println!("Type 'help' for help");
    println!();
}

fn main() -> Result<()> {
    let opts = Opt::from_args();
    init_logging(opts.debug)?;

    let mut editor = init_editor();
    init_history(&mut editor);
    welcome();

    loop {
        match editor.readline(PROMPT) {
            Ok(line) => {
                info!("read: {}", &line);

                match eval(&line) {
                    EvalResult::Ok => (),
                    EvalResult::Quit => break,
                    EvalResult::Err(e) => {
                        eprintln!("{}", e);
                        continue;
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                eprintln!("Press Ctrl-D or type 'quit' to quit");
            }
            Err(ReadlineError::Eof) => {
                println!("quit");
                break;
            }
            Err(e) => {
                error!("Unexpected error: {}", e);
                println!("quit");
            }
        }
    }

    save_history(&mut editor)?;

    Ok(())
}
