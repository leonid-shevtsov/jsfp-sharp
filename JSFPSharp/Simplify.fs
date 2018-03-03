module Simplify

open TransformExpression
open ProgramSemantics

let simplifyOnce = transformPredicate (fun predicate -> 
    match predicate with
    | Binary(Boolean(true), Implies, x) -> x
    | Binary(_, Implies, Boolean(true)) -> Boolean(true)
    | Binary(Boolean(false), Implies, _) -> Boolean(true)
    | Binary(x, Implies, Boolean(false)) -> Not(x)
    | Not(Not(x)) -> x
    | Binary(x, Or, Boolean(false)) -> x
    | Binary(_, Or, Boolean(true)) -> Boolean(true)
    | Binary(_, And, Boolean(false)) -> Boolean(false)
    | Binary(x, And, Boolean(true)) -> x
    | Binary(x, Or, y) when y = x -> x
    | Binary(x, And, y) when y = x -> x
    | Binary(x, Or, Not(y)) when y = x -> Boolean(true)
    | Binary(x, And, Not(y)) when y = x -> Boolean(false)
    | Binary(x, And, Binary(y, Or, _)) when y = x -> x
    | Binary(x, And, Binary(_, Or, y)) when y = x -> x
    | Binary(x, Or, Binary(y, And, _)) when y = x -> x
    | Binary(x, Or, Binary(_, And, y)) when y = x -> x
    | _ -> predicate
)

let evaluateConstantsInExpressions = transformExpressionInPredicate (fun expression ->
    match expression with
    | Expression.Binary(Number(x), operator, Number(y)) -> 
        let result = 
            match operator with
            | Add -> x + y
            | Subtract -> x - y
            | Multiply -> x * y
            | Divide -> x / y
        Number(result)
    | _ -> expression
)

let evaluateConstantsInPredicate = transformPredicate (fun predicate ->
    match predicate with
    | Binary(Boolean(x), operator, Boolean(y)) -> 
        let result = 
            match operator with
            | And -> x && y
            | Or -> x || y
            | Implies -> (not x) || y
        Boolean(result)
    | Not(Boolean(x)) -> Boolean(not x)
    | Comparison(Number(x), operator, Number(y)) ->
        let result =
            match operator with
            | Greater -> x > y
            | GreaterOrEqual -> x >= y
            | Equal -> x = y
            | LessOrEqual -> x <= y
            | Less -> x < y
            | NotEqual -> x <> y
        Boolean(result)
    | _ -> predicate
)

let rec simplifyPredicate predicate =
    let simplified = predicate |> simplifyOnce |> evaluateConstantsInPredicate
    if simplified = predicate
    then
        predicate
    else
        simplifyPredicate simplified // try another iteration
