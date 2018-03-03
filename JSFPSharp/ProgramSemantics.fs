module ProgramSemantics

open System
open JSFPGrammar

type PredicateOperator = 
    | And
    | Or
    | Implies

type ComparisonOperator =
    | Greater
    | GreaterOrEqual
    | Equal
    | LessOrEqual
    | Less
    | NotEqual

type ExpressionOperator = 
    | Add
    | Subtract
    | Multiply
    | Divide

type Expression =
    | Binary of left: Expression * operator: ExpressionOperator * right: Expression
    | Number of value: double
    | Identifier of name: string

type Predicate = 
    | Binary of left: Predicate * operator: PredicateOperator * right: Predicate
    | Not of operand: Predicate
    | Boolean of value: bool
    | Comparison of left: Expression * operator: ComparisonOperator * right: Expression
    | Term of name: string

type Command = 
    | Assignment of identifier: string * value: Expression
    | Sequence of commands: Command list
    | Branch of condition: Predicate * thenBranch: Command * elseBranch: Command option
    | Loop of invariant: Predicate * boundFunction: Expression * condition: Predicate * body: Command

type Program = {
    precondition: Predicate
    postcondition: Predicate
    commands: Command list
}

let castMult castExpression (multCtx: ImperativeLanguageParser.MultExpressionContext) =
    let operandCtxs = multCtx.expression()
    let operands = Array.map castExpression operandCtxs |> Array.toList
    let operator = 
        match multCtx.operator.Text with
        | "*" -> ExpressionOperator.Multiply
        | "/" -> ExpressionOperator.Divide
        | _ -> raise(Exception("impossible"))
    Expression.Binary(operands.Item(0), operator, operands.Item(1))

let castSum castExpression (sumCtx: ImperativeLanguageParser.SumExpressionContext) =
    let operandCtxs = sumCtx.expression()
    let operands = Array.map castExpression operandCtxs |> Array.toList
    let operator = 
        match sumCtx.operator.Text with
        | "+" -> ExpressionOperator.Add
        | "-" -> ExpressionOperator.Subtract
        | _ -> raise(Exception("impossible"))
    Expression.Binary(operands.Item(0), operator, operands.Item(1))

let castNumber (numberCtx: ImperativeLanguageParser.NumericConstantContext) =
    let value = numberCtx.GetText() |> double
    Number(value)

let castId (idCtx: ImperativeLanguageParser.IdentifierContext) =
    idCtx.GetText() |> Identifier

let rec castExpression (expressionCtx: ImperativeLanguageParser.ExpressionContext) =
    match expressionCtx with
    | :? ImperativeLanguageParser.MultExpressionContext as multCtx -> castMult castExpression multCtx
    | :? ImperativeLanguageParser.SumExpressionContext as sumCtx -> castSum castExpression sumCtx
    | :? ImperativeLanguageParser.AtomExpressionContext as atomCtx -> castExpressionAtom (atomCtx.atom())
    | _ -> raise(Exception("impossible"))

and castExpressionAtom (atomCtx: ImperativeLanguageParser.AtomContext) =
    match atomCtx with
    // | :? ImperativeLanguageParser.NegAtomContext as negCtx -> castNeg castExpressionAtom notCtx
    | :? ImperativeLanguageParser.NumericConstantContext as numberCtx -> castNumber numberCtx
    | :? ImperativeLanguageParser.IdentifierContext as idCtx -> castId idCtx
    | :? ImperativeLanguageParser.ParensExpressionContext as parensCtx -> parensCtx.expression() |> castExpression
    | _ -> raise(Exception("impossible"))

let castAnd castPredicate (andCtx: ImperativeLanguageParser.AndPredicateContext) = 
    let operandCtxs = andCtx.predicate()
    let operands = Array.map castPredicate operandCtxs |> Array.toList
    Binary(operands.Item(0), And, operands.Item(1))

let castOr castPredicate (orCtx: ImperativeLanguageParser.OrPredicateContext) =
    let operandCtxs = orCtx.predicate()
    let operands = Array.map castPredicate operandCtxs |> Array.toList
    Binary(operands.Item(0), Or, operands.Item(1))

let castImplies castPredicate (impliesCtx: ImperativeLanguageParser.ImpliesPredicateContext) =
    let operandCtxs = impliesCtx.predicate()
    let operands = Array.map castPredicate operandCtxs |> Array.toList
    Binary(operands.Item(0), Implies, operands.Item(1))

let castNot castPredicateAtom (notCtx: ImperativeLanguageParser.NotAtomContext) = 
    let operand = castPredicateAtom(notCtx.predicateAtom())
    Not(operand)

let castBool(boolCtx: ImperativeLanguageParser.BooleanConstantContext) =
    match boolCtx.GetText() with
    | "true" -> Boolean(true)
    | "false" -> Boolean(false)
    | _ -> raise(Exception("impossible"))

let castComparisonOperator operatorText = 
    match operatorText with
    | "<" -> Less
    | ">" -> Greater
    | "==" -> Equal
    | ">=" -> GreaterOrEqual
    | "<=" -> LessOrEqual
    | "!=" -> NotEqual
    | _ -> raise(Exception("impossible"))

let castComparison(comparisonCtx: ImperativeLanguageParser.ComparisonContext) = 
    let left = castExpression comparisonCtx.left
    let right = castExpression comparisonCtx.right
    let operator = castComparisonOperator comparisonCtx.operator.Text
    Comparison(left, operator, right)

let rec castPredicate(predicateContext: ImperativeLanguageParser.PredicateContext) =
    match predicateContext with
    | :? ImperativeLanguageParser.AndPredicateContext as andP -> castAnd castPredicate andP
    | :? ImperativeLanguageParser.OrPredicateContext as orP -> castOr castPredicate orP
    | :? ImperativeLanguageParser.ImpliesPredicateContext as impliesP -> castImplies castPredicate impliesP
    | :? ImperativeLanguageParser.AtomPredicateContext as atom -> castPredicateAtom(atom.predicateAtom())
    | _ -> raise(Exception("impossible"))

and castPredicateAtom(predicateAtomContext: ImperativeLanguageParser.PredicateAtomContext) = 
    match predicateAtomContext with
    | :? ImperativeLanguageParser.NotAtomContext as notP -> castNot castPredicateAtom notP
    | :? ImperativeLanguageParser.BooleanConstantContext as boolP -> castBool(boolP)
    | :? ImperativeLanguageParser.ComparisonContext as comparisonP -> castComparison(comparisonP)
    | :? ImperativeLanguageParser.ParensPredicateContext as parensP -> castPredicate(parensP.predicate())
    | _ -> raise(Exception("impossible"))


let castPredicates (predicatesCtx: ImperativeLanguageParser.PredicatesContext) =
    let predicateCtxs = predicatesCtx.predicate()
    let predicates = Array.map castPredicate predicateCtxs |> Array.toList
    List.reduce (fun a b -> Binary(a, And, b)) predicates

let castAssignment (assignCtx: ImperativeLanguageParser.AssignmentCommandContext) =
    let identifier = assignCtx.identifier.Text
    let value = assignCtx.expression() |> castExpression
    Assignment(identifier, value)

let castSequence castCommand (sequenceCtx: ImperativeLanguageParser.SequenceCommandContext) =
    let nestedCommands = sequenceCtx.commands().command() |> Array.map castCommand |> Array.toList
    Sequence(nestedCommands)

let castCondition castCommand (conditionCtx: ImperativeLanguageParser.ConditionalCommandContext) =
    let condition = conditionCtx.predicate() |> castPredicate
    let command = conditionCtx.command() |> castCommand
    Branch(condition, command, None)

let castFullCondition castCommand (conditionCtx: ImperativeLanguageParser.FullConditionalCommandContext) =
    let condition = conditionCtx.predicate() |> castPredicate
    let thenCommand = conditionCtx.thenCommand |> castCommand
    let elseCommand = conditionCtx.elseCommand |> castCommand
    Branch(condition, thenCommand, Some(elseCommand))

let castLoop castCommand (loopCtx: ImperativeLanguageParser.LoopCommandContext) =
    let invariant = loopCtx.loopComment().invariant().predicate() |> castPredicate
    let boundFunction = loopCtx.loopComment().boundFunction().expression() |> castExpression
    let condition = loopCtx.predicate() |> castPredicate
    let body = loopCtx.command() |> castCommand
    Loop(invariant, boundFunction, condition, body)
    
let rec castCommand (commandCtx: ImperativeLanguageParser.CommandContext) = 
    match commandCtx with
    | :? ImperativeLanguageParser.AssignmentCommandContext as assignCtx -> castAssignment assignCtx
    | :? ImperativeLanguageParser.SequenceCommandContext as sequenceCtx -> castSequence castCommand sequenceCtx
    | :? ImperativeLanguageParser.ConditionalCommandContext as conditionCtx -> castCondition castCommand conditionCtx
    | :? ImperativeLanguageParser.FullConditionalCommandContext as conditionCtx -> castFullCondition castCommand conditionCtx
    | :? ImperativeLanguageParser.LoopCommandContext as loopCtx -> castLoop castCommand loopCtx
    | _ -> raise(Exception("impossible"))

let castProgram(provingStructure: ImperativeLanguageParser.ProvingStructureContext) =
    let assertionComment = provingStructure.assertionComment()
    let precondition = assertionComment.preconditions().predicates() |> castPredicates
    let postcondition =  assertionComment.postconditions().predicates() |> castPredicates
    let commands = provingStructure.commands().command() |> Array.map castCommand |> Array.toList
    {
        precondition = precondition; 
        postcondition =  postcondition; 
        commands = commands
    }
