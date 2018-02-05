signature LEXICAL =
	sig
		val lex : string * (char list) -> string list
	end 

structure Lexer : LEXICAL =
	struct
		(* Lexer *)

		(*
			Input: un carattere (sym)
			Output: booleano
			Restituisce true se sym è un carattere simbolico tra quelli definiti qui sotto.
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
