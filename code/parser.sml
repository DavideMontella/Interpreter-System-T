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
        chiama parseExpr sul resto della lista dei token. Il modo di operare è lo stesso dei casi precedenti, controlla che gli annidamenti siano rispettati. In particolare il caso della lettura del token else porta alla chiamata di ParseExprTail con argomenti l'espressione a sua volta costituita dalla terna di espressioni l'if-then-else ed il resto della lista di token, come secondo arogmento. Da notare che sia il then che l'else sono obbligatori, altrimenti viene alzata un'eccezione.
      - Fn:
        Deve essere correttamente formattato (come fn x => M). Ident rappresenta il nome del parametro, x nel nostro esempio, mentre body (vedere il codice qui sotto) rappresenta l'espressione che segue la freccia =>. Viene richiamata ParseExprTail con argomenti l'espressione costituita da x ed M (nel nostro esempio) ed il resto della lista dei token.
      - Altrimenti, alza un'eccezione (junk).
		*)
		
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

       (*
          Input: un'espressione (E) e una lista di token
          Output: coppia contenente un'espressione e una lista di token.
          - se la lista di token inizia con =, allora chiama ParseExpr con argomento la lista restante di token, senza il token in testa, e richiama ParseExprTail con argomenti l'espressione (coppia di espressioni) EQexpr(E,E') ed il resto della lista di token.
          - se la lista di token inizia con l'operatore ::, il caso è analogo al precedente.
          - se la lista di token inizia con una parentesi tonda aperta, allora chiama ParseExpr (in modo analogo a quanto visto prima) e 
            controlla che vi sarà la corrispondente parentesi tonda chiusa, per poi richiamare ParseExprTail con argomenti l'applicazione APPLexpr(E,E') e il resto della lista di token. In caso contrario alza un'eccezione.
          - altrimenti ritorna l'input invariato.
          NOTA: le funzioni ParseExpr e ParseExprTail sono mutuamente ricorsive e, tramite chiamate reciproche, permettono di valutare la corretta formattazione del testo e di identificare i vari costrutti del linguaggio, come if-then-else, il let, l'applicazione, ecc.
       *)
		and ParseExprTail(E, TokEQUALS :: tail) =
				let val (E', tail') = ParseExpr(tail)
				in  ParseExprTail(EQexpr(E, E'), tail')
				end
       
			| ParseExprTail(E, TokOPENBR :: rest) =
       			let val (E', TokCLOSEBR :: tail) = ParseExpr(rest)
       			in ParseExprTail(APPLexpr(E, E'), tail)
       			end

			| ParseExprTail(E, tail) = (E, tail)
       
       (*
          Input: lista di token (tokens)
          Output: coppia contenente una lista di espressioni e una lista di token
          Chiama ParseExpr su tokens e controlla il risultato, che è una coppia contenente un'espressione e una lista di token:
          - se la lista di token inizia con una virgola, allora richiama ParseList sulla lista restante privata della virgola iniziale e 
            ritorna una coppia contenente la lista delle espressioni parsate (rispettando l'ordine iniziale) e la restante lista di token
          - altrimenti ritorna una coppia che ha come primo elemento la lista contenente E e come secondo elemento la restante lista di token.
       *)
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
				val (E, nil) = ParseExpr(map MakeToken LexStrings)
			in E
			end
   end;
