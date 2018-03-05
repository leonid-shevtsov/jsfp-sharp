module JSFPSharp

open System.IO
open Parser
open ProgramSemantics
open WP
open Comparisons
open Prover
open Simplify

[<EntryPoint>]
let main argv =
    let pathToSource = Array.head argv
    let source = File.ReadAllText pathToSource
    let parseTree = antlrParse(source)
    match parseTree with
    | Success(parseTree) -> 
        let programCorrectnessHypothesis =
            parseTree 
            |> castProgram 
            |> programCorrectnessHypothesis 

        printf "Program correctness hypothesis: %A\n" programCorrectnessHypothesis

        let factualizedPredicate = 
            programCorrectnessHypothesis
            |> factualizeComparisons

        printf "With factualized comparisons: %A\n" (simplifyPredicate factualizedPredicate.predicate)
        printf "Comparison axioms: %A\n" factualizedPredicate.comparisonAxioms
        
        let proveResult = prover factualizedPredicate.comparisonAxioms factualizedPredicate.predicate

        printf "%A\n" proveResult
        
        0 
    | Error -> 
        printf "Failed to parse\n"
        1
