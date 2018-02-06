use "lib.sml";

signature EXPRESSION =
   sig
      datatype Expression =
         BOOLexpr of bool   |
         EQexpr of Expression * Expression   |
         CONDexpr of Expression * Expression * Expression   |
         SUCCexpr of Expression |
         RECexpr of Expression list * Expression |
         IDENTexpr of string   |
         LAMBDAexpr of string * Expression   |
         APPLexpr of Expression * Expression   |
         NUMBERexpr of int
   end;
   
signature ENVIRONMENT =
   sig
      type 'object Environment

      exception Retrieve of string

      val emptyEnv: 'object Environment
      val declare: string * 'object * 'object Environment -> 'object Environment
      val retrieve: string * 'object Environment -> 'object
      val fold: (('object * 'result) -> 'result) -> 'result -> 
                   'object Environment -> 'result
      val map: ('object -> 'newobject) -> 'object Environment -> 
                 'newobject Environment
  
      val plus: 'obj Environment * 'obj Environment -> 'obj Environment

   end;   

functor Expression(): EXPRESSION =
   struct
      type 'a pair = 'a * 'a

      datatype Expression =
         BOOLexpr of bool   |
         EQexpr of Expression pair   |
         CONDexpr of Expression * Expression * Expression   |
         SUCCexpr of Expression |
         RECexpr of Expression list * Expression |
         IDENTexpr of string   |
         LAMBDAexpr of string * Expression   |
         APPLexpr of Expression * Expression   |
         NUMBERexpr of int
   end;

functor Environment():ENVIRONMENT =
struct
   type 'a Environment = (string *  'a )list

   exception Retrieve of string;
   
   val emptyEnv = [];
   (*Aggiunge all'ambiente e la coppia (s,obj)*)
   fun declare(s:string,obj:'a,e:'a Environment)=
       (s,obj)::e
   (*
	 Data una variabile e un ambiente retrieve ti restituisce il valore della variabile.
   *)
   fun retrieve(s,[])= raise Retrieve(s)
   |   retrieve(s,(s',obj)::rest) =
           if s=s' then obj else retrieve(s,rest)
   (*
	  Prende in input una funzione ed una lista di coppie (chiave,valore) e restituisce la stessa lista con la differenza che ad ogni valore è stata applicata la funzione presa in input
   *)
   fun map f [] = []
     | map f ((hd as (key,obj))::tl)= (key, f(obj)) :: map f tl

   fun fold f r [] = r
     | fold f r ((hd as (key,obj))::tl)= f(obj,fold f r tl)

   fun plus(E1,E2) = E2 @ E1


end;

