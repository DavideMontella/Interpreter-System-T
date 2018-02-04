use "parser.sml";
use "checker.sml";
use "eval.sml";

signature INTERPRETER=
   sig
      val interpret: string -> string
      val eval: bool ref
      and tc  : bool ref
   end;

				  
(* Un funtore è una sorta di funzione che prende come argomenti delle strutture e le utilizza indipendetemente 
da come sono state implementate con la sola condizione che abbiano la segnatura aspettata
	- interp, chiama in sequenza
		- parse per fare il parsing della stringa
		- typecheck per fare il typechecking della Expression ottenuta dal parser, ritorna il tipo ty e
			un booleano ok, settato a true se il typecheck è andato a buon fine
		- prType dovrebbe convertire il tipo ty in una stringa che corrisponde al tipaggio in sml,
			ex. quindi se il nostro termine è di tipo INT, lo converte in una stringa "int"
		- se il termine è tipabile (quindi ok è true), allora chiama evaluate sull'Expression ottenuta dal
			parser
		- printValue lo stampa 
		
		quindi la funzione ritorna la stringa ottenuta da prValue e la stringa ottenuta da prType
			
*)
functor Interpreter
   (structure Ty: TYPE
    structure Value : VALUE
    structure Parser: PARSER
    structure TyCh: TYPECHECKER
    structure Evaluator:EVALUATOR
         sharing Parser.E = TyCh.Exp = Evaluator.Exp 
       and type Value.Exp = Parser.E.Expression
         and TyCh.Type = Ty
         and Evaluator.Val = Value
   ): INTERPRETER=

struct
  val eval = ref true    (* toggle for evaluation *)
  and tc  = ref true    (* toggle for type checking *)
  fun interpret(str)=
    let val abstsyn= Parser.parse str
        val (typestr,ok)= 
                     if !tc then 
                       let val (ty, ok) = TyCh.typecheck abstsyn
                        in (Ty.prType(ty),ok)
                       end
                     else ("(disabled)",false)
        val valuestr= if !eval andalso ok then 
                         Value.printValue(Evaluator.evaluate abstsyn)
                      else "(disabled)"
             
    in  valuestr ^ " : " ^ typestr 
    end

end;


