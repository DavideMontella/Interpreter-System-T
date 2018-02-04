use "lambda.sml";
use "lexer.sml";

Control.Print.printDepth := 100;

signature PARSER =
   sig
      structure E: sig type Expression end
		type Token
      exception Lexical of string
      exception Syntax of string
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
						TokFN   |
						TokARROW   |
						TokNUMBER of int

		exception Lexical of string
		exception Syntax of string
	
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
			| MakeToken("fn") = TokFN
			| MakeToken("=>") = TokARROW
			| MakeToken(s) = if IsNumber(s) then TokNUMBER(valOf (Int.fromString(s)))
							else if IsIdent(s) then TokIDENT(s)
							else raise Lexical(s)

		exception SyntaxError of Token list

		(*
			ParseExpr effettua il parsing della token list, quindi scandisce la lista di token dalla testa 
			alla coda
			- Parentesi tonda aperta:
				chiama ParseExpr sul resto della token list:
          -> se incontra una parentesi tonda chiusa (eventualmente ci sono altre chiamate a funzione prima di entrare in questo caso), allora 
             chiama ParseExprTail con argomenti un'espressione E e il resto della token list.
          -> altrimenti non c'è niente dopo la parentesi aperta, quindi alza un'eccezione.
      - I casi number, nil, true, ident e opensq immediatamente seguito da colsesq sono semplici.
      - Parentesi quadra aperta (opensq):
        chiama ParseList sul resto della token list:
          -> se incontra una parentesi quadra chiusa (come nel caso della tonda, possono esserci altre chiamate), allora chiama ParseExprTail
             con argomenti la lista delle espressioni Es e il resto della lista dei token.
          -> altrimenti non c'è niente dopo la parentesi aperta, quindi alza un'eccezione.
      - Let formattato correttamente (seguito da nome di variabile, uguale e resto della lista dei token):
        Chiama ParseExpr sul resto della lista dei token:
          -> se incontra un in, allora richiama come al solito ParseExpr sul resto della lista dei token, altrimenti alza un'eccezione.
          -> se incontra un end (come sempre, possono esserci altre chiamate a funzione), allora chiama ParseExpreTail con argomenti il nome 
             della variabile (ident) seguito dalle due espressioni (binding e scope) e il resto della lista dei token, altrimenti alza 
             un'eccezione.
          -> altrimenti il let non è correttamente formattato, quindi alza un'eccezione.
      - If:
        chiama parseExpr sul resto della lista dei token. Il modo di operare è lo stesso dei casi precedenti, controlla che gli annidamenti siano rispettati. In particolare il caso della lettura del token else porta alla chiamata di ParseExprTail con argomenti l'espressione a sua volta costituita dalla terna di espressioni l'if-then-else ed il resto della lista di token, come secondo arogmento. Da notare che il then è obbligatorio, altrimenti viene alzata un'eccezione, mentre l'else non lo è.
      - Fn:
        Deve essere correttamente formattato (come fn x => M). Ident rappresenta il nome del parametro, x nel nostro esempio, mentre body (vedere il codice qui sotto) rappresenta l'espressione che segue la freccia =>. Viene richiamata ParseExprTail con argomenti l'espressione costituita da x ed M (nel nostro esempio) ed il resto della lista dei token.
      - Altrimenti, alza un'eccezione (junk).
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
          Input: un'espressione (E) e una lista di token
          Output: 
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
