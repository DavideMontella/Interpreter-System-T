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

      local
         open Expression Value
         fun evaluate(E, exp) =
            case exp
              of BOOLexpr b => mkValueBool b
               | NUMBERexpr i => mkValueNumber i
			   | SUMexpr(e1, e2) =>
                    let val e1' = evaluate(E, e1)
                        val e2' = evaluate(E, e2)
                    in
                       mkValueNumber(unValueNumber e1' + unValueNumber e2')
                    end
			   | PRODexpr(e1, e2) =>
                    let val e1' = evaluate(E, e1)
                        val e2' = evaluate(E, e2)
                    in
                       mkValueNumber(unValueNumber e1' * unValueNumber e2')
                    end

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
               | RECexpr(m::n::e1,e2) => 
               		let val arg = evaluate(E, e2)
               		in
						if 0 = unValueNumber(arg) then evaluate(E,m)
						else evaluate(E, APPLexpr( APPLexpr(n, 
										RECexpr(m::n::e1, NUMBERexpr(unValueNumber(arg)-1))),
										NUMBERexpr(unValueNumber(arg)-1)))
					end
               | IDENTexpr id=> Env.retrieve(id,E)
               | APPLexpr(e1,e2)=> 
                   let val v1 = evaluate(E,e1)
                       val v2 = evaluate(E,e2)
                       val (id',exp',Env',Env'')= unValueClos v1
                       val recE'= Env.plus(unEnv Env', unEnv(Rec Env''))
                    in evaluate(Env.declare(id',v2,recE'), exp')
                   end
               | LAMBDAexpr(x,e) => mkValueClos(x,e,mkEnv E, mkEnv Env.emptyEnv)
                   
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
		       		   CLOS of string *  Exp *  Env * Env
           and Env   = ENV of Value Env.Environment

      exception Value

      val mkValueNumber = NUMBERvalue
      val mkValueBool	= BOOLvalue
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
          eqValue (_,_) = false

      fun Rec(E as (ENV env))=
          let fun unfold(CLOS(id',exp',E',E'')) = CLOS(id',exp',E',E)
                | unfold (v) = v
           in ENV(Env.map unfold env)
          end

      fun printValue(NUMBERvalue(i)) = " " ^ Int.toString(i)   |
          printValue(BOOLvalue(true)) = " true"   |
          printValue(BOOLvalue(false)) = " false"   |
          printValue(CLOS(id,_,_,_)) = "<" ^ id ^ ",_,_,_>"          
   end;
