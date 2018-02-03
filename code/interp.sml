use "parser.sml";
use "checker.sml";
use "eval.sml";

signature INTERPRETER=
   sig
      val interpret: string -> string
      val eval: bool ref
      and tc  : bool ref
   end;

				  
(* Un funtore è una sorta di funzione che prende come argomenti delle strutture e le utilizza indipendetemente da come sono state implementate con la sola condizione che abbiano la segnatura aspettata*)
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


