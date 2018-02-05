use "lambda.sml";
use "lexer.sml";

Control.Print.printDepth := 100;

signature PARSER =
   sig
      structure E: sig type Expression end
		type Token
      exception SyntaxErr of string
		val MakeToken : string -> Token
		val ParseExpr : Token list -> E.Expression * (Token list)
      val parse: string -> E.Expression
   end

functor Parser(Expression:EXPRESSION): PARSER =
	struct
		structure E = Expression
		open E
		open Lexer
		
		datatype Token = TokOPENBR   |
						TokSUCC |
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
						TokFN   |
						TokARROW   |
						TokNUMBER of int

		exception SyntaxErr of string
	
		(* Parser *)	
	
    (*
      Input: una stringa (s)
      Output: un booleano
      Restituisce true se s è composta da sole lettere, minuscole o maiuscole, altrimenti false.
    *)
		fun IsIdent(s) = not(List.exists (not o Char.isAlpha) (explode s))

    (*
      Input: stringa (s)
      Output: booleano
      Restituisce true se s è composta da soli numeri, altrimenti false.
    *)
		fun IsNumber(s) = not(List.exists (not o Char.isDigit) (explode s))

		fun   MakeToken("(") = TokOPENBR
			| MakeToken(")") = TokCLOSEBR
			| MakeToken("true") = TokTRUE
			| MakeToken("false") = TokFALSE
			| MakeToken("succ") = TokSUCC
			| MakeToken("if") = TokIF
			| MakeToken("then") = TokTHEN
			| MakeToken("else") = TokELSE
			| MakeToken("rec") = TokREC
			| MakeToken("[") = TokOPENSQ
			| MakeToken("]") = TokCLOSESQ
			| MakeToken(",") = TokCOMMA
			| MakeToken("=") = TokEQUALS
			| MakeToken("fn") = TokFN
			| MakeToken("=>") = TokARROW
			| MakeToken(s) = if IsNumber(s) then TokNUMBER(valOf (Int.fromString(s)))
							else if IsIdent(s) then TokIDENT(s)
							else raise SyntaxErr(s)


		
		fun ParseExpr(TokOPENBR :: rest): Expression * Token list =
				let val (E, TokCLOSEBR :: tail) = ParseExpr(rest)
				in ParseExprTail(E, tail)
				end
          
			| ParseExpr(TokNUMBER(i) :: rest) = ParseExprTail(NUMBERexpr(i), rest)
				
			| ParseExpr(TokTRUE :: rest) = ParseExprTail(BOOLexpr(true), rest)
		
			| ParseExpr(TokFALSE :: rest) = ParseExprTail(BOOLexpr(false), rest)
		
			| ParseExpr(TokIDENT(ident) :: rest) = ParseExprTail(IDENTexpr(ident), rest)

			| ParseExpr(TokSUCC :: rest) =
				let val (number, tail') = ParseExpr(rest)
				in ParseExprTail(SUCCexpr(number), tail')
				end			
			
			| ParseExpr(TokREC :: TokOPENSQ :: rest) =	
				let val (EsRec, TokCLOSESQ :: tail) = ParseList(rest)
					val (ArgRec, tail') = ParseExpr(tail)
				in ParseExprTail(RECAPPLexpr(EsRec,ArgRec), tail')
				end
		
			| ParseExpr(TokIF :: rest) =
				let val (ifpart, TokTHEN :: tail) = ParseExpr(rest)
					val (thenpart, TokELSE :: tail') = ParseExpr(tail)
					val (elsepart, tail'') = ParseExpr(tail')
				in  ParseExprTail(CONDexpr(ifpart, thenpart, elsepart), tail'')
				end   
             
			| ParseExpr(TokFN :: TokIDENT(ident) :: TokARROW :: rest) =
				let val (body, tail) = ParseExpr(rest)
				in  ParseExprTail(LAMBDAexpr(ident, body), tail)
				end


		and ParseExprTail(E, TokEQUALS :: tail) =
				let val (E', tail') = ParseExpr(tail)
				in  ParseExprTail(EQexpr(E, E'), tail')
				end
       
			| ParseExprTail(E, TokOPENBR :: rest) =
       			let val (E', TokCLOSEBR :: tail) = ParseExpr(rest)
       			in ParseExprTail(APPLexpr(E, E'), tail)
       			end

			| ParseExprTail(E, tail) = (E, tail)
       

		and ParseList(tokens) =
			(case ParseExpr(tokens) of
				(E, TokCOMMA :: rest) =>
					let val (E', tail) = ParseList(rest)
					in  (E :: E', tail)
					end
				| (E, tail) => ([E], tail)
			)


		fun parse(input) =
			let val LexStrings = Lexer.lex("", explode input)
				val (E, nil) = ParseExpr(map MakeToken LexStrings)
			in E
			end
   end;
