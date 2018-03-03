module TransformExpression

open ProgramSemantics

let isCommutativeP operator = 
    operator = And || operator = Or

let isCommutativeE operator = 
    operator = Add || operator = Multiply

let trySwapAndTransformP transformer predicate =
    match predicate with
    | Binary(left, operator, right) ->
        if isCommutativeP(operator)
        then
            let swapped = Binary(right, operator, left)
            let transformed = transformer swapped
            if transformed = swapped
            then
                predicate
            else
                transformed
        else
            predicate
    | _ -> predicate


// Transforms predicates recursively
let rec transformPredicate transformer predicate =
    let transformedWhole = transformer predicate
    if transformedWhole = predicate // no top-level transform - recurse
    then
        match predicate with
        | Binary(left, operator, right) ->
            let transformedSwapped = trySwapAndTransformP transformer predicate
            if transformedSwapped = predicate
            then
                let transformedLeft = transformPredicate transformer left
                let transformedRight = transformPredicate transformer right
                if transformedLeft = left && transformedRight = right
                then
                    predicate // done
                else
                    transformPredicate transformer (Binary(transformedLeft, operator, transformedRight)) // restart from top-level again
            else
                transformPredicate transformer transformedSwapped // restart from top-level again
        | Not(operand) ->
            let transformedOperand = transformPredicate transformer operand
            if transformedOperand = operand
            then
                predicate
            else    
                transformPredicate transformer (Not(transformedOperand))
        | _ -> predicate
    else
        transformPredicate transformer transformedWhole // was a top-level transform - try to transform again
 

let trySwapAndTransformE transformer expression =
    match expression with
    | Expression.Binary(left, operator, right) ->
        if isCommutativeE(operator)
        then
            let swapped = Expression.Binary(right, operator, left)
            let transformed = transformer swapped
            if transformed = swapped
            then
                expression
            else
                transformed
        else
            expression
    | _ -> expression


let rec transformExpression transformer expression =
    let transformedWhole = transformer expression
    if transformedWhole = expression // no top-level transform - recurse
    then
        match expression with
        | Expression.Binary(left, operator, right) ->
            let transformedSwapped = trySwapAndTransformE transformer expression
            if transformedSwapped = expression
            then
                let transformedLeft = transformExpression transformer left
                let transformedRight = transformExpression transformer right
                if transformedLeft = left && transformedRight = right
                then
                    expression // done
                else
                    transformExpression transformer (Expression.Binary(transformedLeft, operator, transformedRight)) // try to transform top level again
            else
                transformExpression transformer transformedSwapped
        | _ -> expression
    else
        transformExpression transformer transformedWhole // was a top-level transform - try to transform again
 
let rec transformExpressionInPredicate transformer predicate =
    match predicate with
    | Binary(left, operator, right) ->
        Binary(
            (transformExpressionInPredicate transformer left),
            operator,
            (transformExpressionInPredicate transformer right)
        )
    | Not(operand) -> Not((transformExpressionInPredicate transformer operand))
    | Comparison(left, operator, right) ->
        Comparison(
            (transformExpression transformer left),
            operator,
            (transformExpression transformer right)
        )
    | _ -> predicate
