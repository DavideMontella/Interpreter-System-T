use "interp.sml";

Control.Print.printDepth := 100;

functor Parser(Expression:EXPRESSION): PARSER =
	struct
		structure E = Expression
		open E
		
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

		(* Lexer *)

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
        Ritorna true se s è non è una lettera, minuscola o maiuscola.
      *)
      fun BadLetter(s : char) = (s < #"a" orelse s > #"z")
      	andalso (s < #"A" orelse s > #"Z")
      
      (*
        Input: una stringa s
        Output: booleano
        Ritorna true se s contiene solo lettere (a-z, A-Z)
      *)
      fun IsIdent(s) = not(List.exists BadLetter (explode s))

      (*
        
      *)
      fun IsNumber(s) = not(List.exists (fn chr : char => chr < #"0" orelse chr > #"9")
                                   (explode s)
                           )

      fun MakeNumber(digits) =
         let fun MakeNumber'(d :: drest, result) =
                    MakeNumber'(drest, result * 10 + ord(d) - ord(#"0"))   |
                 MakeNumber'(nil, result) = result
         in  MakeNumber'(explode digits, 0)
         end

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
   end;
