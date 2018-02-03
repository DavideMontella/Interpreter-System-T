use "lambda.sml";
use "lexer.sml";

Control.Print.printDepth := 100;

signature PARSER =
   sig
      structure E: sig type Expression end

      exception Lexical of string
      exception Syntax of string

      val parse: string -> E.Expression
   end

functor Parser(Expression:EXPRESSION): PARSER =
	struct
		structure E = Expression
		open E
		open Lexer
		
		datatype Token = TokOPENBR   |
						TokCLOSEBR   |
						TokTRUE   |
						TokFALSE   |
						TokIF   |
						TokTHEN   |
						TokELSE   |
						TokOPENSQ   |
						TokCLOSESQ   |
						TokCOMMA   |
						TokREC   |
						TokIDENT of string   |
						TokEQUALS   |
						TokNIL   |
						TokCOLCOL   |
						TokIN   |
						TokEND   |
						TokFN   |
						TokARROW   |
						TokNUMBER of int

		exception Lexical of string
		exception Syntax of string
	
		(* Parser *)	
	
		fun IsIdent(s) = not(List.exists (not o Char.isAlpha) (explode s))

		fun IsNumber(s) = not(List.exists (not o Char.isDigit) (explode s))

		fun MakeToken("(") = TokOPENBR
			| MakeToken(")") = TokCLOSEBR
			| MakeToken("true") = TokTRUE
			| MakeToken("false") = TokFALSE
			| MakeToken("if") = TokIF
			| MakeToken("then") = TokTHEN
			| MakeToken("else") = TokELSE
			| MakeToken("[") = TokOPENSQ
			| MakeToken(",") = TokCOMMA
			| MakeToken("]") = TokCLOSESQ
			| MakeToken("rec") = TokREC
			| MakeToken("=") = TokEQUALS
			| MakeToken("nil") = TokNIL
			| MakeToken("::") = TokCOLCOL
			| MakeToken("in") = TokIN
			| MakeToken("end") = TokEND
			| MakeToken("fn") = TokFN
			| MakeToken("=>") = TokARROW
			| MakeToken(s) = if IsNumber(s) then TokNUMBER(valOf (Int.fromString(s)))
							else if IsIdent(s) then TokIDENT(s)
							else raise Lexical(s)

		exception SyntaxError of Token list

		(*
			ParseExpr effettua il parsing della token list, quindi scandisce la lista di token dalla testa 
			alla coda
			- Parentesi aperta:
				chiama ParseExpr sul resto della token list
		*)

		fun ParseExpr(TokOPENBR :: rest): Expression * Token list =
				(case ParseExpr(rest) of
					(E, TokCLOSEBR :: tail) => ParseExprTail(E, tail)
					| (_, tail) => raise SyntaxError(tail)
				)   
          
			| ParseExpr(TokNUMBER(i) :: rest) = ParseExprTail(NUMBERexpr(i), rest)
		
			| ParseExpr(TokNIL :: rest) = ParseExprTail(LISTexpr [], rest)
		
			| ParseExpr(TokTRUE :: rest) = ParseExprTail(BOOLexpr(true), rest)
		
			| ParseExpr(TokFALSE :: rest) = ParseExprTail(BOOLexpr(false), rest)
		
			| ParseExpr(TokIDENT(ident) :: rest) = ParseExprTail(IDENTexpr(ident), rest)
		
			| ParseExpr(TokOPENSQ :: TokCLOSESQ :: rest) = ParseExprTail(LISTexpr(nil), rest)
		
			| ParseExpr(TokOPENSQ :: rest) =
				(case ParseList(rest) of
					(Es, TokCLOSESQ :: tail) => ParseExprTail(LISTexpr(Es), tail)
					| (_, tail) => raise SyntaxError(tail)
				)   
			
			| ParseExpr(TokLET :: TokIDENT(ident) :: TokEQUALS :: rest) =
				(case ParseExpr(rest) of
					(binding, TokIN :: tail) =>
						(case ParseExpr(tail) of
							(scope, TokEND :: tail') => ParseExprTail(DECLexpr(ident, binding, scope), tail')
							| (_, tail') => raise SyntaxError(tail')
						)
					| (_, tail) => raise SyntaxError(tail)
				)
			
			| ParseExpr(TokIF :: rest) =
				(case ParseExpr(rest) of
					(ifpart, TokTHEN :: tail) =>
						(case ParseExpr(tail) of
							(thenpart, TokELSE :: tail') =>
								let val (elsepart, tail'') = ParseExpr(tail')
								in  ParseExprTail(CONDexpr(ifpart, thenpart, elsepart), tail'')
								end   
							| (_, tail) => raise SyntaxError(tail)
						)
					| (_, tail) => raise SyntaxError(tail)
				)   
             
             | ParseExpr(TokFN :: TokIDENT(ident) :: TokARROW :: rest) =
             	let val (body, tail) = ParseExpr(rest)
             	in  ParseExprTail(LAMBDAexpr(ident, body), tail)
             	end
             
             | ParseExpr(junk) = raise SyntaxError(junk)
             
             (*
             
             *)

             and ParseExprTail(E, TokEQUALS :: tail) =
             	let val (E', tail') = ParseExpr(tail)
             	in  ParseExprTail(EQexpr(E, E'), tail')
             	end
             	
             | ParseExprTail(E, TokCOLCOL :: tail) =
             	let val (E', tail') = ParseExpr(tail)
             	in  ParseExprTail(CONSexpr(E, E'), tail')
             	end
             
             | ParseExprTail(E, TokOPENBR :: rest) =
             	(case ParseExpr(rest) of
             		(E', TokCLOSEBR :: tail) => ParseExprTail(APPLexpr(E, E'), tail)
             		| (_, tail) => raise SyntaxError(tail)
             	)
             
             | ParseExprTail(E, tail) = (E, tail)
             
             
             and ParseList(tokens) =
             	(case ParseExpr(tokens) of
             		(E, TokCOMMA :: rest) =>
             			let val (E', tail) = ParseList(rest)
             			in  (E :: E', tail)
             			end
             		| (E, tail) => ([E], tail)
             	)

		(*
			- riceve una stringa in input
			- chiama il lexer su input, e ottiene una lista di stringhe
			- usa map che applica MakeToken a ogni stringa della lista, e ottiene la lista di token
			- applica ParseExpr alla lista di token, e ottiene una coppia (Expression, list)
				- se la lista è vuota, allora ritorna l'expression
				- altrimenti lancia un'eccezione
 		*)

		fun parse(input) =
			let val LexStrings = Lexer.lex("", explode input)
			in  (case ParseExpr(map MakeToken LexStrings) of
					(E, nil) => E
					| (_, junk) => raise SyntaxError(junk)
				)
			end
   end;
