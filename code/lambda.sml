use "./libs/lib.sml";

signature EXPRESSION =
   sig
      datatype Expression =
         BOOLexpr of bool   |
         EQexpr of Expression * Expression   |
         CONDexpr of Expression * Expression * Expression   |
         CONSexpr of Expression * Expression   |
         LISTexpr of Expression list   |
         DECLexpr of string * Expression * Expression   |
         RECDECLexpr of string * Expression * Expression   |
         IDENTexpr of string   |
         LAMBDAexpr of string * Expression   |
         APPLexpr of Expression * Expression   |
         NUMBERexpr of int

(*
      val prExp: int -> Expression -> string *)
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

functor Expression(structure List: LISTUTIL
                   structure Print: PRINTUTIL): EXPRESSION =
   struct
      type 'a pair = 'a * 'a

      datatype Expression =
         BOOLexpr of bool   |
         EQexpr of Expression pair   |
         CONDexpr of Expression * Expression * Expression   |
         CONSexpr of Expression pair   |
         LISTexpr of Expression list   |
         DECLexpr of string * Expression * Expression   |
         RECDECLexpr of string * Expression * Expression   |
         IDENTexpr of string   |
         LAMBDAexpr of string * Expression   |
         APPLexpr of Expression * Expression   |
         NUMBERexpr of int
	(*
		Prende un termine del linguaggio in input e lo restituisce sottoforma di stringa.
	*)
      fun pr(BOOLexpr true) = " true"
        | pr(BOOLexpr false) = " false"
        | pr(EQexpr p) = printPair "=" p
        | pr(CONDexpr(e1,e2,e3))=
           " if" ^ pr(e1) ^ " then" ^ pr(e2) ^
           " else" ^ pr(e3)
        | pr(CONSexpr p) = printPair "::" p
        | pr(LISTexpr l) = prList l
        | pr(DECLexpr(f,e1,e2))=
           " let " ^ f ^ "=" ^ pr(e1) ^
           " in" ^ pr e2 ^ " end"
        | pr(RECDECLexpr(f,e1,e2))=
           " let rec " ^ f ^ "=" ^ pr(e1) ^
           " in" ^ pr e2 ^ " end"
        | pr(IDENTexpr f)= " " ^ f
        | pr(LAMBDAexpr(x,e))= " fn " ^ x ^ "=>" ^ pr(e)
        | pr(APPLexpr(e1,e2))= pr e1 ^ pr e2
        | pr(NUMBERexpr i)= " " ^ Print.intToString i
      and printPair operator (e1,e2) = pr e1 ^ " " ^ operator ^
            pr e2
      and prList l = "[" ^ prList' l ^ "]"
      and prList' [] = ""
        | prList' [e] = pr e
        | prList'(hd::tl)= pr hd ^ "," ^ prList' tl
(*

      fun prExp n e =
          let val s = pr e
              val Size = size s
           in if Size <= n then s
              else
                 let val slist = explode s
                     val half = (n-3)div 2
                     val initial = List.prefix(slist,half)
                     val final = rev(List.prefix(rev slist,half))
                  in implode(initial @ (explode "...") @ final)
                 end
          end *)
   end;

functor Environment():ENVIRONMENT =
struct
   type 'a Environment = (string *  'a )list

   exception Retrieve of string;
   
   val emptyEnv = [];

   fun declare(s:string,obj:'a,e:'a Environment)=
       (s,obj)::e

   fun retrieve(s,[])= raise Retrieve(s)
   |   retrieve(s,(s',obj)::rest) =
           if s=s' then obj else retrieve(s,rest)

   fun map f [] = []
     | map f ((hd as (key,obj))::tl)= (key, f(obj)) :: map f tl

   fun fold f r [] = r
     | fold f r ((hd as (key,obj))::tl)= f(obj,fold f r tl)

   fun plus(E1,E2) = E2 @ E1


end;

