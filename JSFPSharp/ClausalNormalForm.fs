module ClausalNormalForm

open System
open ProgramSemantics
open TransformExpression
open Simplify
open Clauses


let deImplify = transformPredicate (fun predicate ->
    match predicate with
    | Binary(x, Implies, y) -> Binary(Not(x), Or, y)
    | _ -> predicate
)

let moveNotsInward = transformPredicate (fun predicate ->
    match predicate with
    | Not(Binary(x, And, y)) -> Binary(Not(x), Or, Not(y))
    | Not(Binary(x, Or, y)) -> Binary(Not(x), And, Not(y))
    | Not(Not(x)) -> x
    | _ -> predicate
)

let distributeOrs = transformPredicate(fun predicate ->
    match predicate with
    | Binary(x, Or, Binary(y, And, z)) -> Binary(Binary(x, Or, y), And, Binary(x, Or, z))
    | _ -> predicate
)
let negationNormalForm predicate = 
    predicate
    |> deImplify
    |> moveNotsInward

let conjunctiveNormalForm predicate = 
    predicate
    |> negationNormalForm
    |> distributeOrs

let isNot predicate =
    match predicate with
    | Not(_) -> true
    | _ -> false

let stripNot predicate =
    match predicate with
    | Not(x) -> x
    | _ -> raise(Exception("should never happen"))

let yesNoClauses predicates =
    let yesNoMap = List.groupBy isNot predicates |> Map.ofList
    let yesClauses = 
        if Map.containsKey false yesNoMap
        then
            yesNoMap.[false] |> Set.ofList
        else
            Set.empty
    let noClauses = 
        if Map.containsKey true yesNoMap
        then
            List.map stripNot yesNoMap.[true] |> Set.ofList
        else
            Set.empty
    (yesClauses, noClauses)

// In: predicate
// Out: list of its conjuncts, and each conjunct is represented as a pair of: the list of positive disjuncts, then the list of negative disjuncts
let predicateClauses predicate = 
    List.map (fun p -> yesNoClauses (predicateClauses Or p)) (predicateClauses And predicate)

let disjunctionIsNotTriviallyTrue (yesClauses, noClauses) =
    Set.intersect yesClauses noClauses |> Set.isEmpty

let clausalNormalForm predicate =
    predicate
    |> simplifyPredicate
    |> conjunctiveNormalForm
    |> simplifyPredicate
    |> predicateClauses
    |> List.filter disjunctionIsNotTriviallyTrue
