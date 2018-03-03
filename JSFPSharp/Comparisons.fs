module Comparisons

open System
open ProgramSemantics
open ClausalPolynomialForm

type FactualizedPredicate = {
    comparisonAxioms: Predicate list
    predicate: Predicate
}

let makeComparisonOneSided predicate =
    match predicate with
    | Comparison(_, _, Number(0.0)) -> predicate
    | Comparison(left, operator, right) -> 
        Comparison(
            Expression.Binary(left, Add, Expression.Binary(right, Multiply, Number(-1.0))),
            operator,
            Number(0.0)
        )
    | _ -> raise(Exception("should never happen"))

let normalizeCpf cpf = 
    let (_, factor) = cpf |> Map.toList |> List.rev |> List.head
    let normalizedCpf = Map.map (fun _ value -> value / factor) cpf
    (factor, normalizedCpf)

let flipOperator operator =
    match operator with
    | Greater -> Less
    | GreaterOrEqual -> LessOrEqual
    | Equal -> Equal
    | LessOrEqual -> GreaterOrEqual
    | Less -> Greater
    | NotEqual -> NotEqual

let separateScalar cpf = 
    let scalar = if Map.containsKey "" cpf then cpf.[""] else 0.0
    let cpfWithoutScalar = Map.remove "" cpf
    (scalar, cpfWithoutScalar)

let addendToStr (variables, factor) =
    if variables = ""
    then factor |> sprintf "%f"
    else 
        match factor with
        | 1.0 -> variables
        | -1.0 -> "-" + variables
        | _ -> sprintf "%f*%s" factor variables

let joinAddends (addend1:string) (addend2:string) =
    if addend2.[0] = '-'
    then addend1 + addend2
    else addend1 + "+" + addend2

let cpfToStr cpf =
    if Map.isEmpty cpf 
    then "0"
    else 
        cpf
        |> Map.toList
        |> List.map addendToStr
        |> List.reduce joinAddends

let operatorToString operator =
    match operator with
    | Greater -> ">"
    | GreaterOrEqual -> ">="
    | Equal -> "=="
    | LessOrEqual -> "<="
    | Less -> "<"
    | NotEqual -> "!="

let comparisonToTerm lsideName operator rsideValue =
    let operatorString = operatorToString operator
    sprintf "%s%s%f" lsideName operatorString rsideValue |> Term

let injectComparison bindings lsideName operator rsideValue =
    let notResult = 
        match operator with
        | (GreaterOrEqual | LessOrEqual | NotEqual) -> true
        | (Greater | Less | Equal) -> false

    let operatorToUse = 
        match operator with
        | (Greater | Less | Equal) -> operator
        | GreaterOrEqual -> Less
        | LessOrEqual -> Greater
        | NotEqual -> Equal    
      
    let term = comparisonToTerm lsideName operatorToUse rsideValue

    let predicate = if notResult then Not(term) else term

    let setOfBindings = 
        if Map.containsKey lsideName bindings
        then
            bindings.[lsideName]
        else 
            Set.empty
    
    let setOfBindings = Set.add (operatorToUse, rsideValue) setOfBindings    
    
    let newBindings = Map.add lsideName setOfBindings bindings
    
    (newBindings, predicate)


let recordComparison bindings predicate =
    let oneSided = makeComparisonOneSided(predicate)
    match oneSided with
    | Comparison(left, operator, _) ->
        let cpf = clausalPolynomialForm(left)
        if cpf.IsEmpty
        then
            // if left side is empty (0), expression is true if operator allows
            // equality (because right side is 0)
            (bindings, Comparison(Number(0.0), operator, Number(0.0)))
        else
            let (normalizingFactor, normalizedClauses) = normalizeCpf cpf
            let normalizedOperator = if normalizingFactor > 0.0 then operator else (flipOperator operator)
            let (scalar, nonScalar) = separateScalar normalizedClauses
            let rside = -scalar
            if Map.isEmpty nonScalar
            then
                (bindings, Comparison(Number(0.0), normalizedOperator, Number(rside)))
            else
                let stringLside = cpfToStr nonScalar
                injectComparison bindings stringLside normalizedOperator rside
    | _ -> raise(Exception("should never happen"))

let rec extractComparisons bindings predicate = 
    match predicate with 
    | Comparison(_) -> recordComparison bindings predicate
    | Binary(left, operator, right) ->
        let (leftBindings, leftFactualized) = extractComparisons bindings left
        let (rightAndLeftBindings, rightFactualized) = extractComparisons leftBindings right
        (rightAndLeftBindings, Binary(leftFactualized, operator, rightFactualized))
    | Not(operand) ->
        let (bindings, factualized) = extractComparisons bindings operand
        (bindings, Not(factualized))
    | _ -> (bindings, predicate)
   
let comparisonImplication lside ((ox, x), (oy, y)) =
    let tx = comparisonToTerm lside ox x
    let ty = comparisonToTerm lside oy y

    match (ox, oy) with
    | (Greater, Less) when x >= y -> Binary(tx, Implies, Not(ty))
    | (Greater, Less) when x < y -> Binary(Not(tx), Implies, ty)
    | (Greater, Greater) when x > y -> Binary(tx, Implies, ty)
    | (Greater, Greater) when x < y -> Binary(Not(tx), Implies, Not(ty))
    | (Less, Less) when x < y -> Binary(tx, Implies, ty)
    | (Less, Less) when x > y -> Binary(Not(tx), Implies, Not(ty))
    | (Less, Greater) when x <= y -> Binary(tx, Implies, Not(ty))
    | (Less, Greater) when x > y -> Binary(Not(tx), Implies, ty)
    | (Greater, Equal) when x >= y -> Binary(tx, Implies, Not(ty))
    | (Greater, Equal) when x < y -> Binary(Not(tx), Implies, Not(ty))
    | (Equal, Equal) -> Binary(tx, Implies, Not(ty))
    | (Equal, Greater) when x > y -> Binary(tx, Implies, ty)
    | (Equal, Greater) when x <= y -> Binary(tx, Implies, Not(ty))
    | (Equal, Less) when x < y -> Binary(tx, Implies, ty)
    | (Equal, Less) when x >= y -> Binary(tx, Implies, Not(ty))
    | _ -> raise(Exception("should never happen"))

let bindingImplications (lside, usageCases) = 
    let usageCasesList = Set.toList usageCases
    usageCasesList
    |> List.allPairs usageCasesList
    |> List.filter (fun (x,y) -> x <> y)
    |> List.map (comparisonImplication lside)

let factualizeComparisons predicate =
    let (bindings, predicate) = extractComparisons Map.empty predicate
    let axioms = bindings |> Map.toList |> List.collect bindingImplications
    
    { comparisonAxioms = axioms; predicate = predicate }
