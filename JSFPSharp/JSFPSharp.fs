module JSFPSharp

open Parser
open ProgramSemantics
open WP
open Comparisons
open Prover

let test = antlrParse("""
    
        /* PRE: z==1;
        POST: y==1 */

    if (z>0) {
      x=z;
    } else {
      x=w+1
    };

    y=x;

        
        """).Value

[<EntryPoint>]
let main _ =
    let factualizedPredicate = 
      test 
      |> castProgram 
      |> programCorrectnessHypothesis 
      |> factualizeComparisons
    
    let proveResult = prover factualizedPredicate.comparisonAxioms factualizedPredicate.predicate

    printf "%A" proveResult
    
    // let testPredicate = Binary(Boolean(true), Implies, Binary(Term("x"), And, Comparison(Number(0.0), Less, Number(1.0))))
    // simplifyPredicate testPredicate |> printfn "%A" 
    0 // return an integer exit code
