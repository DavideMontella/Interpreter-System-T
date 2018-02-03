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

<<<<<<< HEAD
		(* Lexer *)

    (*
      Input: un carattere (sym)
      Output: booleano
      Restituisce true se sym è un carattere simbolico tra quelli definiti qui sotto, altrimenti false.
    *)
		fun symbolic(sym) = List.exists (fn x => x = sym) ["(", ")", "[", "]", ","]

    (*
      Input: una stringa (accum) e una lista di caratteri (this :: (rest : char list)).
      Output: lista di caratteri.
      Casi possibili:
        - se accum è un whitespace character (space, newline, ...), allora:
            -> se accum è la stringa vuota, allora richiama lex con argomenti accum e la lista di caratteri senza l'elemento in testa (ovvero 
               this)
            -> altrimenti aggiunge accum in testa al risultato della chiamata lex("", rest)
        - se accum inizia con un carattere alfanumerico e this non è alfanumerico (o viceversa), allora:
            -> se accum è la stringa vuota, allora richiama lex con argomenti this (convertito a stringa) e rest
            -> altrimenti aggiunge accum in testa al risultato della chiamata a lex con gli stessi argomenti appena descritti
        - se this o accum sono simbolici, allora:
            identico al caso precedente
        - altrimenti:
            -> se rest non è la lista vuota, allora chiama lex con argomenti la concatenazione di accum e this e, come secondo argomento, rest
            -> altrimenti se accum è la stringa vuota, ritorna la lista vuota, altrimenti la lista contenente accum.

    *)
		fun lex(accum, this :: (rest : char list)) =
			if Char.isSpace this then
				(if accum = "" then lex("", rest)
				else accum :: lex("", rest))
			else if (Char.isAlphaNum (String.sub(accum,0)) <> Char.isAlphaNum this) then
				(if accum = "" then lex(Char.toString(this), rest)
				else accum :: lex(Char.toString(this), rest))
			else if symbolic(Char.toString(this)) orelse symbolic(accum) then
				(if accum = "" then lex(Char.toString(this), rest)
				else accum :: lex(Char.toString(this), rest))
			else lex(accum^Char.toString(this), rest)   |
			
			lex(accum, nil) = if accum = "" then [] else [accum]
	
		(* end Lexer*)

      exception Lexical of string
      
      (*
        Input: un carattere (s)
        Output: booleano
        Ritorna true se s non è una lettera, nè minuscola nè maiuscola, altrimenti false.
      *)
      fun BadLetter(s : char) = (s < #"a" orelse s > #"z")
      	andalso (s < #"A" orelse s > #"Z")
      
      (*
        Input: una stringa s
        Output: booleano
        Ritorna true se s contiene solo lettere (a-z, A-Z), altrimenti false.
      *)
      fun IsIdent(s) = not(List.exists BadLetter (explode s))

      (*
        Input: una stringa s
        Output: booleano
        Ritorna true se s rappresenta un numero, altrimenti false.
      *)
      fun IsNumber(s) = not(List.exists (fn chr : char => chr < #"0" orelse chr > #"9")
                                   (explode s)
                           )

      (*
        Input: una stringa (digits)
        Output: intero
        Chiama ricorsivamente MakeNumber sulla lista di caratteri che compongono digits. 
        Ad ogni chiamata toglie un elemento dalla testa di digits e lo inserisce con la rispettiva potenza di 10 nel numero che costruisce.
      *)
      fun MakeNumber(digits) =
         let fun MakeNumber'(d :: drest, result) =
                    MakeNumber'(drest, result * 10 + ord(d) - ord(#"0"))   |
                 MakeNumber'(nil, result) = result
         in  MakeNumber'(explode digits, 0)
         end


      (*
        Come dice il nome, crea un token. Da notare TokNUMBER di tipo int e TokIDENT di tipo string.
      *)
      fun MakeToken("(") = TokOPENBR   |
          MakeToken(")") = TokCLOSEBR   |
          MakeToken("true") = TokTRUE   |
          MakeToken("false") = TokFALSE   |
          MakeToken("if") = TokIF   |
          MakeToken("then") = TokTHEN   |
          MakeToken("else") = TokELSE   |
          MakeToken("[") = TokOPENSQ   |
          MakeToken(",") = TokCOMMA   |
          MakeToken("]") = TokCLOSESQ   |
          MakeToken("rec") = TokREC   |
          MakeToken("=") = TokEQUALS   |
          MakeToken("nil") = TokNIL   |
          MakeToken("::") = TokCOLCOL   |
          MakeToken("in") = TokIN   |
          MakeToken("end") = TokEND   |
          MakeToken("fn") = TokFN   |
          MakeToken("=>") = TokARROW   |
          MakeToken(s) = if IsNumber(s) then TokNUMBER(MakeNumber s)
                         else if IsIdent(s) then TokIDENT(s)
                         else raise Lexical(s)

				(* Parsing *)
      exception SyntaxError of Token list

      fun syntaxError(x) = raise SyntaxError(x)

      (*

      *)
      fun ParseExpr(TokOPENBR :: rest): Expression * Token list =
             (case ParseExpr(rest) of
                 (E, TokCLOSEBR :: tail) => ParseExprTail(E, tail)   |
                 (_, tail) => syntaxError(tail)
             )   |

          ParseExpr(TokNUMBER(i) :: rest) =
             ParseExprTail(NUMBERexpr(i), rest)  |

          ParseExpr(TokNIL :: rest) =
             ParseExprTail(LISTexpr [], rest)  |

          ParseExpr(TokTRUE :: rest) =
             ParseExprTail(BOOLexpr(true), rest)  |

          ParseExpr(TokFALSE :: rest) =
             ParseExprTail(BOOLexpr(false), rest)  |

          ParseExpr(TokIDENT(ident) :: rest) =
             ParseExprTail(IDENTexpr(ident), rest)   |

          ParseExpr(TokOPENSQ :: TokCLOSESQ :: rest) =
             ParseExprTail(LISTexpr(nil), rest)   |

          ParseExpr(TokOPENSQ :: rest) =
             (case ParseList(rest) of
                 (Es, TokCLOSESQ :: tail) =>
                    ParseExprTail(LISTexpr(Es), tail)   |

                 (_, tail) => syntaxError(tail)
             )   |

          ParseExpr(TokLET :: TokIDENT(ident) :: TokEQUALS :: rest) =
             (case ParseExpr(rest) of
                (binding, TokIN :: tail) =>
                   (case ParseExpr(tail) of
                       (scope, TokEND :: tail') =>
                          ParseExprTail(DECLexpr(ident, binding, scope),
                                        tail')   |
                       (_, tail') => syntaxError(tail')
                   )   |
                (_, tail) => syntaxError(tail)
             )   |

          ParseExpr(TokIF :: rest) =
             (case ParseExpr(rest) of
                (ifpart, TokTHEN :: tail) =>
                   (case ParseExpr(tail) of
                      (thenpart, TokELSE :: tail') =>
                         let val (elsepart, tail'') = ParseExpr(tail')
                         in  ParseExprTail(CONDexpr(ifpart, thenpart, elsepart),
                                           tail'')
                         end   |
                      (_, tail) => syntaxError(tail)
                   )   |

                (_, tail) => syntaxError(tail)
             )   |

          ParseExpr(TokFN :: TokIDENT(ident) :: TokARROW :: rest) =
             let val (body, tail) = ParseExpr(rest)
             in  ParseExprTail(LAMBDAexpr(ident, body), tail)
             end   |

          ParseExpr(junk) = syntaxError(junk)

          and ParseExprTail(E, TokEQUALS :: tail) =
                 let val (E', tail') = ParseExpr(tail)
                 in  ParseExprTail(EQexpr(E, E'), tail')
                 end   |

              ParseExprTail(E, TokCOLCOL :: tail) =
                 let val (E', tail') = ParseExpr(tail)
                 in  ParseExprTail(CONSexpr(E, E'), tail')
                 end   |

              ParseExprTail(E, TokOPENBR :: rest) =
                 (case ParseExpr(rest) of
                     (E', TokCLOSEBR :: tail) =>
                        ParseExprTail(APPLexpr(E, E'), tail)   |
                     (_, tail) => syntaxError(tail)
                 )   |

              ParseExprTail(E, tail) = (E, tail)

          and ParseList(tokens) =
                 (case ParseExpr(tokens) of
                     (E, TokCOMMA :: rest) =>
                        let val (E', tail) = ParseList(rest)
                        in  (E :: E', tail)
                        end   |

                     (E, tail) => ([E], tail)
                 )

      exception Syntax of string

      (*
        input: stringa
        output: espressione

      *)
      fun parse(input) =
         let val LexStrings = lex("", explode input)
         in  (case ParseExpr(map MakeToken LexStrings) of
                 (E, nil) => E   |
                 (_, junk) => syntaxError(junk)
             ) 
         end
=======
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
>>>>>>> affbb931cc7584ef4d58fa156a8ea1593ace0181
   end;
