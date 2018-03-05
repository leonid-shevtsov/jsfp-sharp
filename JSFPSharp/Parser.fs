module Parser

open JSFPGrammar
open Antlr4.Runtime

type ParsingResult =
    | Success of provingStructure: ImperativeLanguageParser.ProvingStructureContext
    | Error

let antlrParse (sourceCode: string) =
    let inputStream = new AntlrInputStream(sourceCode)
    let lexer = new ImperativeLanguageLexer(inputStream)
    let tokens = new CommonTokenStream(lexer)
    let parser = new ImperativeLanguageParser(tokens)
    if parser.NumberOfSyntaxErrors = 0
    then
        Success(parser.provingStructure())
    else
        Error
