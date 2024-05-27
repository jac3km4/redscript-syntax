use pretty_assertions::assert_eq;
use redscript_ast::SourceMap;
use redscript_formatter::{FormatSettings, Formattable};
use redscript_parser::parse_module;

#[test]
fn formatted_files() {
    let files = SourceMap::from_files([
        "tests/data/ControlFlow.reds",
        "tests/data/Module.reds",
        "tests/data/Operators.reds",
    ])
    .unwrap();

    for (id, file) in files.iter() {
        let (module, errors) = parse_module(file.source(), id);
        if let (Some(module), []) = (module, &errors[..]) {
            let settings = FormatSettings::default();
            let formatted = module.display(&settings).to_string();
            assert_eq!(formatted, file.source());
        } else {
            panic!("failed to parse {}: {errors:?}", file.path().display());
        }
    }
}
