use "lambda.sml";

signature VALUE =
   sig
      structure Environment : sig type 'a Environment end
      type Value and Env and Exp
      exception Value

      val mkValueNumber: int -> Value
          and unValueNumber: Value -> int

      val mkValueBool: bool -> Value
          and unValueBool: Value -> bool

      val ValueNil: Value
      val mkValueCons: Value * Value -> Value
          and unValueHead: Value -> Value
          and unValueTail: Value -> Value

      val mkValueClos: string * Exp * Env * Env -> Value
          and unValueClos: Value -> string * Exp * Env * Env

      val mkEnv: Value Environment.Environment -> Env
          and unEnv: Env -> Value Environment.Environment

      val Rec: Env -> Env

      exception EqValue
      val eqValue: Value * Value -> bool
      val printValue: Value -> string
   end;


signature EVALUATOR =
   sig
      structure Exp: sig type Expression end
      structure Val: sig type Exp and Value end
            sharing type Val.Exp = Exp.Expression
      exception Unimplemented
      exception RuntimeError of string
      val evaluate: Exp.Expression -> Val.Value
   end;
                    
(*
	funtore che ritorna l'evaluator, prende le strutture dei valori, degli ambienti e delle espressioni
		- ha una sola funzione evaluate che prende un'espressione e ritorna un valore,
			effettua valutazione eager statica
			- questa chiama una funzione locale evaluate con argomenti l'espressione e un ambiente vuoto
		- la funzione locale evaluate, funziona per casi su tutte le possibili espressioni
			- casi base:
				- espressioni booleane e intere, ritornano risprettivamente NUMBERvalue e BOOLvalue, chiamando
					rispettivamente mkValueNumber e mkValueBool
			- uguaglianza, quindi coppia di espressioni, le valuta entrambe, chiama eqValue, 
				per effettuare il confronto dei valori ottenuti, e costruisce il BOOLvalue corrispondente
			- if cond then ex1 else ex2, valuta cond, se è true, valuta ex1 altrimenti valuta ex2
			- cons, valuta i due termini, e ritorna un cons che rappresenta una concatenzione dei due valori
				ottenuti (non una lista)
			- lista
				- vuota, quindi ValueNil
				- viene convertita in una concatenzione (cons), valutandone da testa a coda tutti glie elementi
			- ## let, da verificare
			- ## rec, da verificare
			- variabile, valuta la variabile nell'ambiente associato
			- applicazione, valuta entrambe le espressioni, "spacchetta" la prima espressione, che deve essere
				una chiusura, quindi 
			
				
		
*)                    
                    
functor Evaluator
  (structure Expression: EXPRESSION
   structure Env: ENVIRONMENT
   structure Value: VALUE
             sharing type Value.Exp = Expression.Expression
             sharing Value.Environment = Env
  ):EVALUATOR=

   struct
      structure Exp= Expression
      structure Val= Value
      type Env = Val.Value Env.Environment

      exception Unimplemented
      exception RuntimeError of string
      local
         open Expression Value
         fun evaluate(E, exp) =
            case exp
              of BOOLexpr b => mkValueBool b
               | NUMBERexpr i => mkValueNumber i
               | EQexpr(e1,e2)=> 
                    let val v1 = evaluate(E,e1)
                        val v2 = evaluate(E,e2)
                     in mkValueBool(eqValue(v1,v2))
                    end
               | CONDexpr(e1,e2,e3)=> 
                    let val v1 = evaluate(E, e1)
                     in if eqValue(v1,mkValueBool true) then evaluate(E,e2)
                        else evaluate(E, e3)
                    end
               | CONSexpr(e1, e2) =>
                    let val v1 = evaluate(E, e1)
                        val v2 = evaluate(E, e2)
                     in mkValueCons(v1,v2)
                    end
               | LISTexpr [] => ValueNil
               | LISTexpr (hd::tl)=> 
                    evaluate(E, CONSexpr(hd, LISTexpr tl))
               | DECLexpr(id,e1,e2) => 
                    let val v1 = evaluate(E,e1)
                        val E' = Env.declare(id,v1,E)
                     in evaluate(E', e2)
                    end
               | RECDECLexpr(f,e1,e2) => 
                    let val v1 = evaluate(E, e1)
                        val ? = unValueClos v1
                                handle Value=> raise RuntimeError(
                           "recursively  defined value is not a function")
                        val Env0 = mkEnv(Env.declare(f,v1,Env.emptyEnv))
                        val recE0 = Rec Env0
                        val newE = Env.plus(E, unEnv recE0)
                     in evaluate(newE,e2)
                    end

               | IDENTexpr id=> 
                    Env.retrieve(id,E)
               | APPLexpr(e1,e2)=> 
                   let val v1 = evaluate(E,e1)
                       val v2 = evaluate(E,e2)
                       val (id',exp',Env',Env'')= unValueClos v1
                       val recE'= Env.plus(unEnv Env', unEnv(Rec Env''))
                    in evaluate(Env.declare(id',v2,recE'), exp')
                   end
               | LAMBDAexpr(x,e) => 
                   mkValueClos(x,e,mkEnv E, mkEnv Env.emptyEnv)
                   


      in
         val evaluate = fn(e) => evaluate(Env.emptyEnv,e)
      end
   end;




functor Value(structure Env: ENVIRONMENT
              structure Exp : EXPRESSION
              structure Print: PRINTUTIL): VALUE =
   struct
      type 'a pair = 'a * 'a

      type Exp = Exp.Expression
      structure Environment= Env

      datatype Value = NUMBERvalue of int   |
                       BOOLvalue of bool   |
                       NILvalue   |
                       CONSvalue of Value pair |
		       		   CLOS of string *  Exp *  Env * Env
           and Env   = ENV of Value Env.Environment

      exception Value

      val mkValueNumber = NUMBERvalue
      val mkValueBool = BOOLvalue

      val ValueNil = NILvalue
      val mkValueCons = CONSvalue

      val mkValueClos = CLOS
      val mkEnv       = ENV


      fun unValueNumber(NUMBERvalue(i)) = i   |
          unValueNumber(_) = raise Value

      fun unValueBool(BOOLvalue(b)) = b   |
          unValueBool(_) = raise Value

      fun unValueHead(CONSvalue(c, _)) = c   |
          unValueHead(_) = raise Value

      fun unValueTail(CONSvalue(_, c)) = c   |
          unValueTail(_) = raise Value

      fun unValueClos(CLOS q) = q |
          unValueClos(_) = raise Value

      fun unEnv(ENV e) = e
        
     
      exception EqValue

      fun eqValue(NUMBERvalue v,NUMBERvalue v') = v=v' |
          eqValue(BOOLvalue v, BOOLvalue v') = v=v' |
          eqValue(NILvalue,NILvalue) = true |
          eqValue(CONSvalue(v1,v2),CONSvalue(v1',v2'))= 
             eqValue(v1,v1') andalso eqValue(v2,v2') |
          eqValue (_,_) = false
          

          
                 

      (* unfolding of environments for recursion*)

      fun Rec(E as (ENV env))=
          let fun unfold(CLOS(id',exp',E',E'')) = CLOS(id',exp',E',E)
                | unfold (v) = v
           in ENV(Env.map unfold env)
          end
          


				(* Pretty-printing *)
      fun printValue(NUMBERvalue(i)) = " " ^ Print.intToString(i)   |
          printValue(BOOLvalue(true)) = " true"   |
          printValue(BOOLvalue(false)) = " false"   |
          printValue(NILvalue) = "[]"   |
          printValue(CONSvalue(cons)) = "[" ^ printValueList(cons) ^ "]" |
          printValue(CLOS(id,_,_,_)) = "<" ^ id ^ ",_,_,_>"
          
          and printValueList(hd, NILvalue) = printValue(hd)   |
              printValueList(hd, CONSvalue(tl)) =
                 printValue(hd) ^ ", " ^ printValueList(tl)   |
              printValueList(_) = raise Value
          
   end;
