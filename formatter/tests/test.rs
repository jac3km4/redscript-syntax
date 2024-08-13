use pretty_assertions::assert_eq;
use redscript_ast::SourceMap;
use redscript_formatter::{format_document, FormatSettings};

#[test]
fn formatted_files() {
    let files = SourceMap::from_files([
        "tests/data/ControlFlow.reds",
        "tests/data/Module.reds",
        "tests/data/Operators.reds",
    ])
    .unwrap();
    let settings = FormatSettings::default();
    for (id, file) in files.iter() {
        let (module, errors) = format_document(file.source(), id, &settings);
        if let (Some(module), []) = (module, &errors[..]) {
            assert_eq!(
                module.to_string(),
                file.source(),
                "{}",
                file.path().display()
            );
        } else {
            panic!("failed to parse {}: {errors:?}", file.path().display());
        }
    }
}
