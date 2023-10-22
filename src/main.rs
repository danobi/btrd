use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{bail, Result};
use log::{error, info};
use rustyline::{config::Config as EditorConfig, error::ReadlineError, history::FileHistory, Editor, Helper};
use simplelog::{Color, ColorChoice, ConfigBuilder, Level, LevelFilter, TermLogger, TerminalMode};
use clap::Parser;

mod btrfs;
mod input;
mod lang;

use input::ReplHelper;
use lang::eval::EvalResult;
use lang::runtime::Runtime;

const HISTORY_FILE: &str = ".btrd_history";
const PROMPT: &str = "(btrd) ";

#[derive(Parser)]
struct Opt {
    /// Show debug output
    #[clap(short, long)]
    debug: bool,
    /// Run a script (instead of running the REPL)
    script: Option<PathBuf>,
}

fn init_logging(debug: bool) -> Result<()> {
    let filter = if debug {
        LevelFilter::Info
    } else {
        LevelFilter::Error
    };

    let config = ConfigBuilder::new()
        .set_level_color(Level::Info, Some(Color::Rgb(128, 128, 128)))
        .set_level_color(Level::Error, Some(Color::Red))
        .build();

    match TermLogger::init(filter, config, TerminalMode::Stderr, ColorChoice::Auto) {
        Ok(_) => Ok(()),
        Err(e) => bail!("Failed to init logger: {}", e),
    }
}

fn init_editor() -> Result<Editor<ReplHelper, FileHistory>> {
    let config = EditorConfig::builder().auto_add_history(true).build();
    let mut editor = Editor::with_config(config)?;
    let validator = ReplHelper::new();
    editor.set_helper(Some(validator));

    Ok(editor)
}

fn init_history<H: Helper>(editor: &mut Editor<H, FileHistory>) {
    let _ = editor.load_history(HISTORY_FILE);
}

fn save_history<H: Helper>(editor: &mut Editor<H, FileHistory>) -> Result<()> {
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

fn repl(sink: &mut dyn Write) -> Result<()> {
    let mut editor = init_editor()?;
    init_history(&mut editor);
    welcome();

    let mut runtime = Runtime::new(sink, true);

    loop {
        match editor.readline(PROMPT) {
            Ok(line) => {
                let decommented = input::strip_comments(&line);
                let fixed = input::fixup_input(&decommented);

                info!("read: {}", line.escape_debug());
                info!("cleaned: {}", fixed.escape_debug());

                match runtime.eval(&fixed) {
                    EvalResult::Ok => (),
                    EvalResult::Quit => break,
                    EvalResult::Err(e) => {
                        eprintln!("Error: {}", e);
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

fn script(sink: &mut dyn Write, script: &Path) -> Result<()> {
    let mut file = OpenOptions::new().read(true).open(script)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    let decommented = input::strip_comments(&contents);

    let mut runtime = Runtime::new(sink, false);
    match runtime.eval(&decommented) {
        EvalResult::Ok | EvalResult::Quit => Ok(()),
        EvalResult::Err(e) => {
            eprintln!("Error: {}", e);
            bail!("Error in script");
        }
    }
}

fn main() -> Result<()> {
    let opts = Opt::parse();
    init_logging(opts.debug)?;

    let mut stdout = std::io::stdout();

    if let Some(s) = opts.script {
        script(&mut stdout, &s)
    } else {
        repl(&mut stdout)
    }
}
