use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::canonicalize;
use std::path::Path;

use crate::ast::TypedModule;
use crate::ast::{Import, Module};
use crate::constants::STD_NATIVE_MODULE;
use crate::location::Location;
use anyhow::Result;
use anyhow::{anyhow, Context};
use error::LastLayerError;
use log::debug;

pub mod parser;
// pub mod semantic_analysis;
pub mod error;
mod type_ast;
pub mod type_inference;
pub mod types;
pub mod utils;

fn get_absolute_path(path: &str) -> Result<String> {
    let path = canonicalize(path)?;
    Ok(path
        .to_str()
        .expect("Unable to convert path to string")
        .to_string())
}

/// Tries to resolve the import path to an absolute file path.
/// - entrypoint is the file which was passed to the interpreter.
/// - current_file is the file which contains the import statement.
/// - import is the import path.
///
/// The function tries to resolve the import path in the following order:
/// 0. If the import is a module ("std/foo"), then it is resolved to the standard library.
/// 1. If the import path is an absolute path ("/foo"), it is returned as is.
/// 2. If the import path is a relative path ("./foo"), it is resolved relative to the current file.
/// 3. If step 2 fails, the import path is resolved relative to the entrypoint file.
pub fn get_canonical_import_path(
    entrypoint: &Path,
    current_file: &Path,
    import: &str,
) -> Option<Box<Path>> {
    assert!(!entrypoint.is_dir() && !current_file.is_dir());

    // std standard import.
    if !import.starts_with('/') && !import.starts_with('.') {
        todo!("Not yet implemented")
    }

    if import.starts_with('/') {
        return Some(Box::from(Path::new(import)));
    }

    // Resolve relative to the current file
    let current_file_dir = current_file.parent().unwrap();
    let current_file = current_file_dir.join(import);
    if current_file.exists() {
        return Some(Box::from(current_file));
    }

    // Resolve relative to the entrypoint
    let entrypoint_dir = entrypoint.parent().unwrap();
    let entrypoint_file = entrypoint_dir.join(import);
    entrypoint_file.exists().then(|| Box::from(entrypoint_file))
}

/// Parses all files in the project (starting from entrypoint file path) and returns a map of
/// absolute file paths (which are effectively unique identifiers of the source files) to their ASTs.
///
/// - entrypoint: The path to the file from which the parsing should start.
///
/// ## Paths
/// Since the paths can be relative, we must canonicalize them. This means that imports
/// ../foo/../foo/../foo/foo.mjl and ../foo/foo.mjl will result in the same import, and will not be
/// imported twice. As a result, this must also transform all imports in modules to absolute path,
/// since other operations later use the imports path as an unique ID for the module.
///
fn parse_files(entrypoint: &str) -> Result<HashMap<String, Module>, LastLayerError> {
    let mut visited: HashSet<String> = HashSet::new();
    let mut q: VecDeque<String> = VecDeque::new();
    let mut result: HashMap<String, Module> = HashMap::new();

    q.push_back(get_absolute_path(&entrypoint).map_err(|e| {
        LastLayerError {
            error: e.to_string(),
            location: Location::new(0, 0),
            module: entrypoint.to_string(),
        }.with_context("Failed to canonicalize entrypoint path")
    })?);

    // bfs
    while !q.is_empty() {
        let current = q.pop_front().unwrap();
        debug!("Parsing file: {}", current);
        let contents = std::fs::read_to_string(current.clone())
            .with_context(|| format!("Failed to read file {}", current))
            .map_err(|e| {
                LastLayerError {
                    error: e.to_string(),
                    location: Location::new(0, 0),
                    module: current.clone(),
                }
            })?;
        let (imports, decls) = parser::parse_ast(&contents).map_err(|e| {
            LastLayerError {
                error: e.message,
                location: Location::new(e.location, e.location + 1),
                module: current.clone(),
            }
        })?;
        // Transform imports to absolute shortests paths, to make them unique.
        let mut transformed_imports = vec![];
        // TODO: For now, handle only non std imports. When location of standard library is set
        // (/usr/mjolnir/std ?), remove this filter.
        for import in imports {
            if import.path == STD_NATIVE_MODULE {
                transformed_imports.push(import);
                continue;
            }

            let import_path =
                get_canonical_import_path(Path::new(entrypoint), Path::new(&current), &import.path);
            if import_path.is_none() {
                return Err(LastLayerError {
                    error: format!("Could not find file '{}'", import.path),
                    location: import.location,
                    module: current.clone(),
                });
            }
            let import_path = canonicalize(import_path.unwrap())
                .expect("Could not canonicalize path")
                .to_str()
                .expect("Imported path is not unicode!")
                .to_string();
            if !visited.contains(&import_path) {
                visited.insert(import_path.clone());
                q.push_back(import_path.clone());
            }
            transformed_imports.push(Import {
                imported_ids: import.imported_ids.clone(),
                path: import_path,
                location: import.location,
            });
        }
        result.insert(
            current,
            Module {
                imports: transformed_imports,
                decls,
            },
        );
    }

    Ok(result)
}

/// A shorthand, where you pass a (FileId, File contents).
/// This is intended for testing only, since import paths
/// can be relative, but the parsing algorithms absolutes
/// them. It does no such thing here (this function does not
/// touch the filesystem).
pub fn fe_pass(files: HashMap<String, String>) -> Result<HashMap<String, TypedModule>> {
    let mut modules = HashMap::new();
    for (name, content) in files {
        let (imports, decls) = parser::parse_ast(&content).map_err(|_| anyhow!("Parsing failed"))?;
        modules.insert(name, Module { imports, decls });
    }
    let inferred = type_inference::type_infer_modules(modules).map_err(|_| anyhow!("Type inference failed"))?;
    let typed =
        type_ast::type_modules(inferred).map_err(|_| anyhow!("AST Typing failed"))?;
    Ok(typed)
}

/// Starting from entrypoint file, parses and typechecks it and all files that it imports.
pub fn parse_and_check_files(entrypoint: &str) -> Result<HashMap<String, TypedModule>, LastLayerError> {
    let modules = parse_files(entrypoint)?;
    let inferred = type_inference::type_infer_modules(modules)?;
    type_ast::type_modules(inferred)
}
