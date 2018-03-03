module Clauses

open ProgramSemantics

let rec predicateClauses clauseOperator predicate = 
    match predicate with
    | Binary(left, operator, right) when operator = clauseOperator -> 
        List.append (predicateClauses clauseOperator left) (predicateClauses clauseOperator right)
    | _ -> [predicate]

let rec expressionClauses clauseOperator expression = 
    match expression with
    | Expression.Binary(left, operator, right) when operator = clauseOperator -> 
        List.append (expressionClauses clauseOperator left) (expressionClauses clauseOperator right)
    | _ -> [expression]
