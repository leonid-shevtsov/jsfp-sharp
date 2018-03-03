module ClausalPolynomialForm

open System
open TransformExpression
open ProgramSemantics
open Clauses

let differencesToSums = transformExpression (fun expression ->
    match expression with
    | Expression.Binary(a, Subtract, b) -> Expression.Binary(a, Add, Expression.Binary(Number(-1.0), Multiply, b))
    | _ -> expression
)

let distributeProducts = transformExpression (fun expression ->
    match expression with
    | Expression.Binary(a, Multiply, Expression.Binary(b, Add, c)) -> 
        Expression.Binary(
            Expression.Binary(a, Multiply, b),
            Add,
            Expression.Binary(a, Multiply, c)
        )
    | _ -> expression
)

let polynomialClauses normalizedPolynomial = 
    List.map (expressionClauses Multiply) (expressionClauses Add normalizedPolynomial)

let isIdentifier expression =
    match expression with
    | Identifier(_) -> true
    | _ -> false

let getIdentifier expression =
    match expression with
    | Identifier(name) -> name
    | _ -> raise(Exception("check isIdentifier first"))

let isNumber expression = 
    match expression with
    | Number(_) -> true
    | _ -> false

let getNumber expression =
    match expression with
    | Number(value) -> value
    | _ -> raise(Exception("check isNumber first"))

let appendFactor termFactors newTerm =
    let factorKey = 
        newTerm
        |> List.filter isIdentifier
        |> List.map getIdentifier
        |> List.sortDescending
        |> String.concat "*"
    let factor =
        newTerm
        |> List.filter isNumber
        |> List.map getNumber
        |> List.fold (*) 1.0
    let existingFactor = if Map.containsKey factorKey termFactors then termFactors.[factorKey] else 0.0
    Map.add factorKey (existingFactor + factor) termFactors

let joinSimilarClauses polynomialClauses = 
    List.fold appendFactor Map.empty polynomialClauses

let removeZeroesFromCpf termFactors = 
   Map.filter (fun _ factor -> factor <> 0.0) termFactors

let clausalPolynomialForm expression =
    expression
    |> differencesToSums
    |> distributeProducts
    |> polynomialClauses
    |> joinSimilarClauses
    |> removeZeroesFromCpf
