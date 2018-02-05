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

      val mkValueClos: string * Exp * Env * Env -> Value
          and unValueClos: Value -> string * Exp * Env * Env

      val mkEnv: Value Environment.Environment -> Env
          and unEnv: Env -> Value Environment.Environment

      val Rec: Env -> Env

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
               | SUCCexpr(ex) => 
               		let val v = evaluate(E, ex)
               		in mkValueNumber(unValueNumber(v)+1)
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
               | RECAPPLexpr(m::n::e1,e2) => 
               		let val arg = evaluate(E, e2)
               		in
						if 0 = unValueNumber(arg) then evaluate(E,m)
						else evaluate(E, APPLexpr(
										APPLexpr(n, RECAPPLexpr(m::n::e1, NUMBERexpr(unValueNumber(arg) -1)))
										, NUMBERexpr(unValueNumber(arg) -1)
									))
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
              structure Exp : EXPRESSION): VALUE =
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
      val mkValueBool	= BOOLvalue
      val ValueNil 		= NILvalue
      val mkValueCons	= CONSvalue
      val mkValueClos	= CLOS
      val mkEnv      	= ENV

      fun unValueNumber(NUMBERvalue(i)) = i
      fun unValueBool(BOOLvalue(b)) 	= b
      fun unValueClos(CLOS q) 			= q
      fun unEnv(ENV e) 					= e
        
     
     (*
     	esegue il confronto di uguaglianza su coppie:
     		- interi
     		- booleani
     		- liste vuote
     		- concatenazioni, confrontando gli elementi con stessa posizione nelle due concatenazioni 
     		- altrimenti non sono confrontabili, quindi false
     *)
     

      fun eqValue(NUMBERvalue v,NUMBERvalue v') = v=v' |
          eqValue(BOOLvalue v, BOOLvalue v') = v=v' |
          eqValue(NILvalue,NILvalue) = true |
          eqValue(CONSvalue(v1,v2),CONSvalue(v1',v2'))= 
          eqValue(v1,v1') andalso eqValue(v2,v2') |
          eqValue (_,_) = false

      fun Rec(E as (ENV env))=
          let fun unfold(CLOS(id',exp',E',E'')) = CLOS(id',exp',E',E)
                | unfold (v) = v
           in ENV(Env.map unfold env)
          end
          
		(*
			Converte i valori in stringhe
			- ######## la chiusura è incasinata e non so perchè
		*)

				(* Pretty-printing *)
      fun printValue(NUMBERvalue(i)) = " " ^ Int.toString(i)   |
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
