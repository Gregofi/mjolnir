use crate::frontend::error::LastLayerError;
use colored::{ColoredString, Colorize};

/// Describes a location in a source file as a
/// range of chars <begin, end).
#[derive(Clone, Debug, Copy)]
pub struct Location {
    pub start: usize,
    pub end: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Location {
        Location {
            start: line,
            end: column,
        }
    }
}

/// Returns (line, column) of the given location in the source.
fn find_loc(source: &str, idx: usize) -> (usize, usize) {
    let mut line = 0;
    let mut column = 0;
    for (i, c) in source.chars().enumerate() {
        if i == idx {
            return (line, column);
        }
        if c == '\n' {
            line += 1;
            column = 0;
        } else {
            column += 1;
        }
    }
    (line, column)
}

/// Every code line has before it `5  | `, this is different length
/// based on the line number (it might or might not be added)
fn prefix(mut line_number: usize, print_line: bool) -> ColoredString {
    line_number += 1;
    // There is a subtle bug here that is avoided for small sources with
    // this ugly if line_number < 10 { " " } else { "" } workaround.
    // If error spanning multiple lines happens when another digit
    // is introduced, it will not print correctly...
    // 99 |   ....
    // 100 | ....
    // It is not aligned.
    format!("{}{}  | ", if line_number < 10 { " " } else { "" },
        if print_line {
        line_number.to_string() 
    } else {
        " ".repeat((line_number.checked_ilog10().unwrap_or(0) + 1) as usize)
    }).bright_blue().bold()
}

/// Formats an error message for the given location.
/// For errors that are on one line, it underlines it via ^.
/// For errors that span multiple lines, it underlines the first and last line.
/// And prints the lines in between.
/// Example:
/// ```rust
///         a
/// ________^
/// |          +
/// |  b
/// |__^
fn print_source_error(source: &str, location: Location) {
    let (start_line, start_column) = find_loc(source, location.start);
    let (end_line, end_column) = find_loc(source, location.end);

    let lines = source.lines().collect::<Vec<_>>();
    println!("{} {}", prefix(start_line, true), lines[start_line]);

    // This is simple, we just underline the error.
    if start_line == end_line {
        println!("{}{}{}", prefix(start_line, false), " ".repeat(start_column + 1), "^".repeat(end_column - start_column).red().bold());
        return;
    }

    // This is harder, we need to do shenanigans with the lines.
    // Ie.     foo 
    // ________^
    // |        +
    // |                bar
    // |_________________^
    println!("{} {}{}", prefix(start_line, false), "_".repeat(start_column).red(), "^".red().bold());
    let mut current_line = start_line + 1;
    while current_line <= end_line {
        println!("{}{}{}", prefix(current_line, true), "|".red().bold(), lines[current_line]);
        current_line += 1;
    }
    println!("{}{}", prefix(current_line, false), format!("|{}^", "_".repeat(end_column - 1)).red().bold());
}

pub fn read_source(file: &str) -> String {
    std::fs::read_to_string(file).expect("Could not read file")
}

/// Formats the whole error message and prints it.
/// Uses colors and whatnot.
pub fn print_error(LastLayerError{ error, location, module }: LastLayerError) {
    let source = read_source(&module);
    let (start_line, start_column) = find_loc(&source, location.start);
    println!("{}: {}\n  {} {}:{}:{}",
            "error".red().bold(),
            error.bold(),
            "-->".bright_blue().bold(),
            module,
            start_line + 1,
            start_column + 1,
            );
    print_source_error(&source, location)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_loc() {
        let source = "fn main() {
println!(
\"Hello, world!\");
}";
        assert_eq!(find_loc(source, 4), (0, 4));
        assert_eq!(find_loc(source, 20), (1, 8));
    }
}
