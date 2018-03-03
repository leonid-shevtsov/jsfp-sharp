module WP

open System
open ProgramSemantics

let rec replaceIdentifierInExpression identifier value expression =
    match expression with
    | Expression.Binary(left, operator, right) -> 
        Expression.Binary(
            (replaceIdentifierInExpression identifier value left),
            operator,
            (replaceIdentifierInExpression identifier value right)
        )
    | Number(_) -> expression
    | Identifier(exprIdentifier) -> if exprIdentifier = identifier then value else expression

let rec replaceIdentifierInPredicate identifier value predicate =
    match predicate with
    | Binary(left, operator, right) -> 
        Binary(
            (replaceIdentifierInPredicate identifier value left),
            operator,
            (replaceIdentifierInPredicate identifier value right)
        )
    | Not(operand) -> Not(replaceIdentifierInPredicate identifier value operand)
    | Boolean(_) -> predicate
    | Comparison(left, operator, right) -> 
        Comparison(
            (replaceIdentifierInExpression identifier value left),
            operator,
            (replaceIdentifierInExpression identifier value right)
        )
    | Term(_) -> raise(Exception("should never happen"))

let branchWP commandWP branchCondition thenCommand elseCommand postcondition = 
    let thenPostcondition = commandWP postcondition thenCommand
    let thenPrecondition = Binary(branchCondition, Implies, thenPostcondition)
    let elsePostcondition = 
        match elseCommand with
        | Some(command) -> commandWP postcondition command
        | None -> postcondition
    let elsePrecondition = Binary(Not(branchCondition), Implies, elsePostcondition)
    Binary(thenPrecondition, And, elsePrecondition)

let loopWP commandWP invariant boundFunction loopCondition body postcondition =
    let random = new System.Random()
    let boundVar = random.Next(1000000) |> sprintf "bound_%6x" 
    let loopContinuationCondition = 
        Binary(
            // For as long as the loop goes
            Binary(loopCondition, And, invariant),
            Implies, 
            Binary(
                // The invariant is maintained after an iteration
                commandWP invariant body,
                And, 
                Binary(
                    // The bound function is greater than 0
                    Comparison(boundFunction, Greater, Number(0.0)),
                    And,
                    // The bound function reduces after each iteration
                    // (in other words, the value of BoundFunction evaluated after the body,
                    // is less than boundVar captured before the body)
                    commandWP (Comparison(boundFunction, Less, Identifier(boundVar))) body
                    |> replaceIdentifierInPredicate boundVar boundFunction
                )
            )
        )
    let loopTerminationCondition =
        Binary(
            // Once the loop is terminated
            Binary(Not(loopCondition), And, invariant),
            Implies,
            postcondition
        )
    Binary(
        invariant,
        And,
        Binary(loopContinuationCondition, And, loopTerminationCondition)
    )

let rec commandWP postcondition command =
    match command with
    | Sequence(commands) -> List.rev commands |> List.fold commandWP postcondition 
    | Assignment(identifier, value) -> replaceIdentifierInPredicate identifier value postcondition
    | Branch(condition, thenCommand, elseCommand) -> branchWP commandWP condition thenCommand elseCommand postcondition
    | Loop(invariant, boundFunction, condition, body) -> loopWP commandWP invariant boundFunction condition body postcondition

let weakestPrecondition program = 
    let commandSequence = Sequence(program.commands)
    commandWP program.postcondition commandSequence


let programCorrectnessHypothesis program =
    Binary(program.precondition, Implies, weakestPrecondition(program))
