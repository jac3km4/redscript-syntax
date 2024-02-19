use std::io::{self, Write};
use std::{
    fs::{self, File},
    path::PathBuf,
};

use argh::FromArgs;
use redscript_formatter::{FormatSettings, Formattable};
use redscript_parser::parse_module;

#[derive(FromArgs)]
/// Redscript formatter CLI
struct Opts {
    /// input source file path
    #[argh(option)]
    input: PathBuf,
    /// output source file path
    #[argh(option)]
    output: PathBuf,
    /// size of the indentation
    #[argh(option, default = "2")]
    indent: u16,
    /// max significant digits in floating point numbers, defaults to unlimited
    #[argh(option)]
    max_sig_digits: Option<u8>,
}

fn main() -> anyhow::Result<()> {
    let opts = argh::from_env::<Opts>();
    let conents = fs::read_to_string(opts.input)?;
    let (module, errors) = parse_module(&conents);
    let Some(module) = module else {
        let err = errors
            .iter()
            .map(|e| e.to_string() + "\n")
            .collect::<String>();
        anyhow::bail!("{err}");
    };
    let settings = FormatSettings {
        indent: opts.indent,
        max_sig_digits: opts.max_sig_digits,
    };
    let mut out = io::BufWriter::new(File::create(&opts.output)?);
    write!(out, "{}", module.display(&settings))?;
    Ok(())
}
