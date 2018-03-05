module Prover

open ProgramSemantics
open Simplify
open System
open TransformExpression
open ClausalNormalForm

type ProverResult = Proved | Disproved | FailedToProve

let evaluationMethodVariableLimit = 20
let resolutionMethodIterationLimit = 1000

let rec predicateTerms predicate =
    match predicate with 
    | Binary(left, _, right) -> List.append (predicateTerms left) (predicateTerms right) |> List.distinct
    | Not(operand) -> predicateTerms operand
    | Term(name) -> [name]
    | _ -> []

let rec replaceTermInPredicate term value = transformPredicate (fun predicate ->
    match predicate with
    | Term(x) when x = term -> Predicate.Boolean(value)
    | _ -> predicate
)

let rec evaluationMethodInner statement identifiers bindings =
    match identifiers with
    | [] -> 
        let result = evaluateConstantsInPredicate statement
        match result with
        | Boolean(false) -> Proved // Refuted counter-hypothesis -> so hypothesis is proved
        | Boolean(true) -> 
            printf "Counterexample: %A\n" bindings
            Disproved
        | _ -> raise(Exception("should not happen"))
    | head :: tail ->
        if (tryReplacingIdentifier statement head true tail bindings) = Proved && 
            (tryReplacingIdentifier statement head false tail bindings) = Proved
        then
            Proved
        else
            Disproved

and tryReplacingIdentifier statement identifier value restOfIdentifiers bindings =
    let statementWithoutTerm = replaceTermInPredicate identifier value statement
    let bindingsWithTerm = Map.add identifier value bindings
    evaluationMethodInner statementWithoutTerm restOfIdentifiers bindingsWithTerm

let evaluationMethod statement identifiers =
    evaluationMethodInner statement identifiers Map.empty


let trivialSolution (yesDisjuncts, noDisjuncts) =
    if Set.isEmpty(noDisjuncts) && Set.count(yesDisjuncts) = 1
    then
        let yesDisjunct = Set.toList(yesDisjuncts) |> List.head
        match yesDisjunct with
        | Boolean(true) -> Disproved
        | Boolean(false) -> Proved
        | _ -> FailedToProve
    else
        FailedToProve

let deriveConjunctFromPair ((yes1, no1), (yes2, no2)) =
    let allYes = Set.union yes1 yes2
    let allNo = Set.union no1 no2
    let allYesWithoutNo = Set.difference allYes allNo
    let allNoWithoutYes = Set.difference allNo allYes
    (allYesWithoutNo, allNoWithoutYes)

let deriveResolutions conjuncts =
    List.allPairs conjuncts conjuncts 
    |> List.filter (fun (x,y) -> x <> y)
    |> List.map deriveConjunctFromPair

let conjunctLength (y1, n1) =
    Set.count(y1) + Set.count(n1)

let rec resolutionMethodLoop conjuncts iteration = 
    if iteration > resolutionMethodIterationLimit
    then
        FailedToProve
    else
        let derivedConjuncts = deriveResolutions conjuncts |> Set.ofList
        let newConjuncts = 
            Set.difference derivedConjuncts (Set.ofList(conjuncts))
            |> Set.toList
            |> List.sortBy conjunctLength
        match newConjuncts with
        | bestNewConjunct :: _  ->
            if conjunctLength(bestNewConjunct) = 0
            then
                Proved
            else
                let newConjuncts = bestNewConjunct::conjuncts
                resolutionMethodLoop newConjuncts (iteration+1)
        | _ -> FailedToProve

let resolutionMethod statement = 
    let clauses = clausalNormalForm statement
    match clauses with
    | [ singleClause ] -> trivialSolution singleClause
    | _ -> resolutionMethodLoop clauses 0
        
let prover facts hypothesis = 
    let counterHypothesis = Not(hypothesis)

    let provableStatement = 
        facts
        |> List.fold (fun x y -> Binary(x, And, y)) counterHypothesis
        |> simplifyPredicate

    let identifiers = predicateTerms provableStatement

    if (List.length identifiers) < evaluationMethodVariableLimit
    then
        evaluationMethod provableStatement identifiers
    else
        resolutionMethod provableStatement
