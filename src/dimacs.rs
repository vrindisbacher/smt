use crate::sat::{clause::CnfClause, formula::CnfFormula};
use crate::var::{Lit, Var};

pub(crate) fn parse_formula_from_dimacs_str(lines: &str) -> CnfFormula<i32> {
    let mut clauses = Vec::new();

    let mut collector = Vec::new();
    let mut clause_ended = false;
    for line in lines.split("\n") {
        let trimmed = line.trim();

        // Ignore comment lines or lines starting with 'p'
        if trimmed.starts_with('c') || trimmed.starts_with('p') {
            continue;
        }

        for token in trimmed.split_whitespace() {
            if let Ok(num) = token.parse::<i32>() {
                if num == 0 {
                    // End of clause
                    clause_ended = true;
                    break;
                }

                // Check if the variable is negated
                if num < 0 {
                    // the literal must have the same name as any positive instances
                    collector.push(Lit::neg(Var::new(-num)));
                } else {
                    collector.push(Lit::pos(Var::new(num)));
                }
            }
        }
        // Add the clause to the formula
        if clause_ended {
            clauses.push(CnfClause::new(collector));
            collector = Vec::new();
            clause_ended = false;
        }
    }
    CnfFormula::new(clauses)
}
