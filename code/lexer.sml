signature LEXICAL =
	sig
		val lex : string * (char list) -> string list
	end 

structure Lexer : LEXICAL =
	struct
		(* Lexer *)
		
		(*
		lex è il nostro lexer, prende una stringa accum e una lista di caratteri, sia this la testa della lista
			- parse per prima cosa chiama lex("", explode input), cioè trasforma il termine passato in 
				input in una lista di caratteri
			- lex scorre dalla testa alla coda la lista di caratteri e usa accum per 'accumulare' un token
			- ritorna la lista di token
			- la funzione opera per casi:
				- se il carattere 'this' in testa alla lista è uno spazio
					allora se la parola accumulata è vuota, chiama lex sul resto della lista
					altrimenti inserisce la parola accumulata il testa alla lista e chiama lex con
						un primo argomento stringa vuota
				- se accum è vuoto allora, chiama lex con la stringa this
				- se accum è alphaNum e this è punteggiatura, o vicevera, allora aggiunge accum alla lista
					e chiama lex con argomento this
				- se accum o this sono simbolici, allora aggiunge accum alla lista e chiama lex con this
				- altrimenti concatena accum e this, e chiama lex con questa nuova stringa
			- il caso base di lex viene raggiunto quando list diventa vuota, quindi aggiunge l'ultima stringa
				accumulata, e ritornando dalle chiamate ricorsive le stringhe vengono aggiunte in testa
		*)

		fun symbolic(sym) = List.exists (fn x => x = sym) ["(", ")", "[", "]", ",", "+", "-", "*"]

		fun lex(accum, this :: (rest : char list)) =
			if Char.isSpace this then
				(if accum = "" then lex("", rest)
				else accum :: lex("", rest))
			else if accum = "" then lex(Char.toString(this), rest)
			else if (Char.isAlphaNum (String.sub(accum,0)) <> Char.isAlphaNum this) then
				(accum :: lex(Char.toString(this), rest))
			else if symbolic(Char.toString(this)) orelse symbolic(accum) then
				(accum :: lex(Char.toString(this), rest))
			else lex(accum^Char.toString(this), rest)   
			
		| lex(accum, nil) = if accum = "" then [] else [accum]
	
		(* end Lexer*)
	end;
