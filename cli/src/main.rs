use std::io::{self, Write};
use std::{fs::File, path::PathBuf};

use argh::FromArgs;
use redscript_ast::SourceMap;
use redscript_formatter::FormatSettings;

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
    /// max line width, defaults to 80
    #[argh(option, default = "80")]
    max_width: u16,
    /// max fields in a chain, defaults to 4
    #[argh(option, default = "4")]
    max_chain_fields: u8,
    /// max calls in a chain, defaults to 2
    #[argh(option, default = "2")]
    max_chain_calls: u8,
    /// max operators in a chain, defaults to 4
    #[argh(option, default = "4")]
    max_chain_operators: u8,
    /// max total chain length, defaults to 4
    #[argh(option, default = "4")]
    max_chain_total: u8,
    /// max significant digits in floating point numbers, defaults to unlimited
    #[argh(option)]
    max_sig_digits: Option<u8>,
}

fn main() -> anyhow::Result<()> {
    let opts = argh::from_env::<Opts>();
    let map = SourceMap::from_files([opts.input])?;
    let settings = FormatSettings {
        indent: opts.indent,
        max_width: opts.max_width,
        max_chain_calls: opts.max_chain_calls,
        max_chain_fields: opts.max_chain_fields,
        max_chain_operators: opts.max_chain_operators,
        max_chain_total: opts.max_chain_total,
        trunc_sig_digits: opts.max_sig_digits,
    };
    let mut errors = vec![];

    for (id, file) in map.iter() {
        let (module, e) = redscript_formatter::format(file.source(), id, &settings);
        errors.extend(e);
        let Some(module) = module else {
            continue;
        };

        let mut out = io::BufWriter::new(File::create(&opts.output)?);
        write!(out, "{}", module)?;
    }

    for err in errors {
        eprintln!("{}", err.pretty(&map));
    }
    Ok(())
}
