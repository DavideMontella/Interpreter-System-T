use "lambda.sml";

                  (* type checking *)
signature TYPE =
   sig
      eqtype tyvar
      val freshTyvar: unit -> tyvar
      type Type 
      type TypeScheme
  
      val tyvarsTy: Type -> tyvar list
      and tyvarsTySch: TypeScheme -> tyvar list

      val instance: TypeScheme -> Type

	(*constructors and decstructors*)
      exception Type
      val mkTypeInt: unit -> Type
          and unTypeInt: Type -> unit

      val mkTypeBool: unit -> Type
          and unTypeBool: Type -> unit

      val mkTypeList: Type -> Type
          and unTypeList: Type -> Type

      val mkTypeArrow:  Type * Type -> Type
          and unTypeArrow: Type -> Type * Type

      val mkTypeTyvar: tyvar -> Type
          and unTypeTyvar: Type -> tyvar

      val mkTypeScheme: tyvar list * Type -> TypeScheme
          and unTypeScheme: TypeScheme -> tyvar list * Type

      type subst
      val Id: subst                     (* the identify substitution;   *)
      val mkSubst: tyvar*Type -> subst 	(* make singleton substitution; *)
      val on : subst * Type -> Type     (* application;                 *)
      val onScheme: subst * TypeScheme -> TypeScheme
	
      val oo : subst * subst -> subst   (* composition *)

      val prType: Type->string          (* printing *)
   end

signature TYPEENV=
 sig
  structure Type : sig type Type and TypeScheme and subst end
  type typeenv
  exception Retrieve of string
  val emptyEnv: typeenv
  val declare: string * Type.TypeScheme * typeenv -> typeenv
  val retrieve: string * typeenv -> Type.TypeScheme
  val close: typeenv * Type.Type -> Type.TypeScheme
  val onTE: Type.subst * typeenv -> typeenv
 end
  


signature TYPECHECKER =
   sig
      structure Exp: sig type Expression end
      structure Type: sig type Type end
      exception NotImplemented of string
      val typecheck: Exp.Expression -> Type.Type * bool
   end;
                        (* the type checker *)   
signature UNIFY=
   sig
      structure Type: sig type Type and subst end
      exception NotImplemented of string
      exception Unify
      val unify: Type.Type * Type.Type -> Type.subst
   end;

functor TypeCheckerRecovery(structure Ex: EXPRESSION
                            structure Ty: TYPE
                            structure List: LISTUTIL): 
  sig 
   val report: Ex.Expression * int * Ty.subst * string list ->
               Ty.subst * Ty.Type * bool
  end=

struct
  exception Recovery of int
  val messages= [
(1, fn[t2]=> 
"expected the second operand to cons to be of list type" ^
"\n   found :   " ^  t2
|        _ => raise Recovery 1),

(2, fn[t1,t2]=>
"the type of the first list element differs from the type of the others " ^
"\n   first element  :   " ^  t1 ^
"\n   other elements :   " ^  t2
|        _ => raise Recovery 2),

(3, fn[t1,t2]=>
"left and right hand sides of = have different types" ^
"\n  left-hand side  :  " ^  t1 ^
"\n  right-hand side :  " ^  t2
|        _ => raise Recovery 3),

(4, fn[t1]=>
"expected boolean expression between `if' and `then';" ^
"\n  found:  " ^  t1
|        _ => raise Recovery 4),

(5, fn[t2,t3]=>
"`then' and `else' branches have different types" ^
"\n  `then' branch :  " ^  t2 ^
"\n  `else' branch :  " ^  t3
|        _ => raise Recovery 5),

(6, fn[t1,t2]=>
"the domain type of the function differs from the type of the argument " ^
"\nto which it is applied" ^
"\n  function domain type : " ^  t1 ^
"\n  argument        type : " ^  t2
|        _ => raise Recovery 6),

(7, fn[t1]=>
"I expected this expression, which is an argument " ^
"\nto a numeric operator, to have type int; but I " ^
"\nfound : " ^  t1
|        _ => raise Recovery 7),

(8, fn [x] =>
"the identifier " ^ x ^ " has not been declared"
|        _ => raise Recovery 8),

(9, fn [t] =>
"although the above expression occurs in " ^
"\napplication position, I have found it to " ^
"\nhave type :  " ^ t
|        _ => raise Recovery 9)



]

  fun report(exp, i, S, stringlist) =
      let val msgf = List.lookup messages i
                    handle List.Lookup => raise Recovery(i)
          val sep = "\n----------------\n"
          val freshty = Ty.mkTypeTyvar (Ty.freshTyvar())
          val msg   = "Type Error in expression:\n   " ^ 
                      "\nClue: " ^  msgf stringlist ^ "\n"
  (*        val msg   = "Type Error in expression:\n   " ^ Ex.prExp 60 exp ^
                      "\nClue: " ^  msgf stringlist ^ "\n"
*)
       in sep ^ "\n" ^ msg;
          (S,freshty,false)
      end
end;



functor TypeChecker
  (structure Ex: EXPRESSION
   structure Ty: TYPE
   structure TyEnv: TYPEENV
   structure Unify: UNIFY 
      sharing Unify.Type = Ty = TyEnv.Type
   structure List: LISTUTIL
  ): TYPECHECKER=
struct
  infixr on         val (op on) = Ty.on
  infixr onscheme   val op onscheme = Ty.onScheme
  infixr onTE       val op onTE = TyEnv.onTE
  infixr oo         val op oo = Ty.oo

  structure Exp = Ex
  structure Type = Ty
  structure Recovery= TypeCheckerRecovery(
    structure Ex = Ex
    structure Ty = Ty
    structure List = List)

  exception NotImplemented of string
  exception Recover of Ex.Expression * int * Ty.subst * string list ;

  fun tc (TE: TyEnv.typeenv, exp: Ex.Expression): 
        Ty.subst *Ty.Type * bool =
   (case exp of
      Ex.BOOLexpr b => (Ty.Id,Ty.mkTypeBool(),true)
    | Ex.NUMBERexpr _ => (Ty.Id,Ty.mkTypeInt(),true)
    | Ex.LISTexpr [] =>
         let val new = Ty.freshTyvar ()
          in (Ty.Id,Ty.mkTypeList(Ty.mkTypeTyvar  new),true)
         end
    | Ex.LISTexpr(e::es) => tc (TE, Ex.CONSexpr(e,Ex.LISTexpr es))
    | Ex.CONSexpr(e1,e2) =>
       (let val (S1,t1,ok1) = tc(TE, e1)
            val (S2,t2,ok2) = tc(S1 onTE TE, e2)
            val new = Ty.freshTyvar ()
            val newt= Ty.mkTypeTyvar new
            val t2' = Ty.mkTypeList newt
            val S3 = Unify.unify(t2, t2')
                     handle Unify.Unify=> 
                     raise Recover(e2, 1, (S2 oo S1), [Ty.prType t2])
            val S4 = Unify.unify(S3 on newt,(S3 oo S2) on t1)
                     handle Unify.Unify=>
                     raise Recover(exp, 2, (S3 oo S2 oo S1), 
                       [Ty.prType ((S3 oo S2) on t1), Ty.prType (S3 on newt)])
         in (S4 oo S3 oo S2 oo S1, (S4 oo S3) on t2, ok1 andalso ok2)
        end handle Recover q => Recovery.report q)
    | Ex.EQexpr(e1,e2)=> 
       (let val (S1,t1,ok1) = tc(TE,e1)
            val (S2,t2,ok2) = tc(S1 onTE TE, e2)
            val S3 = Unify.unify(S2 on t1, t2)
                     handle Unify.Unify=>
                     raise Recover(exp, 3, (S2 oo S1), [Ty.prType (S2 on t1), 
                          Ty.prType t2])
         in (S3 oo S2 oo S1, Ty.mkTypeBool(), ok1 andalso ok2)
        end  handle Recover q=> Recovery.report q)
    | Ex.CONDexpr(b,e1,e2)=> 
        (let val (S1,t1,ok1) = tc(TE,b)
             val S1' = Unify.unify(t1,Ty.mkTypeBool())
                       handle Unify.Unify=>
                       raise Recover(exp, 4, S1, [Ty.prType t1])
             val (S2,t2,ok2) = tc(S1 onTE TE, e1)
             val (S3,t3,ok3) = tc((S2 oo S1) onTE TE, e2)
             val S3' = Unify.unify(S3 on t2,t3)
                       handle Unify.Unify=>
                       raise Recover(exp, 5, (S3 oo S2 oo S1' oo S1), 
                       [Ty.prType (S3 on t2), Ty.prType t3])
          in (S3' oo S3 oo S2 oo S1' oo S1, 
              (S3' oo S3) on t2,
              ok1 andalso ok2 andalso ok3)
         end handle Recover q=> Recovery.report q)
    | Ex.DECLexpr(x,e1,e2) => 
         let val (S1,t1,ok1) = tc(TE,e1);
             val typeScheme = TyEnv.close(S1 onTE TE,t1)
             val (S2,t2,ok2) = tc(TyEnv.declare(x,typeScheme,S1 onTE TE), e2)
          in (S2 oo S1, t2, ok1 andalso ok2)
         end
    | Ex.RECDECLexpr(fid,e1,e2)=>
         let val new = Ty.mkTypeScheme([],
                         Ty.mkTypeTyvar(Ty.freshTyvar()))
             val TE' = TyEnv.declare(fid,new,TE)
             val (S1,t1, ok1) = tc(TE',e1)
             val (S2,t2, ok2) = tc(S1 onTE TE', e2)
          in
             (S2 oo S1, t2, ok1 andalso ok2)
         end
    | Ex.IDENTexpr x   => 
         ((Ty.Id, Ty.instance(TyEnv.retrieve(x,TE)), true)
         handle TyEnv.Retrieve _=> 
          Recovery.report(exp,8,Ty.Id,[x]))
    | Ex.LAMBDAexpr(x,e)=>
         let val newty = Ty.mkTypeTyvar(Ty.freshTyvar())
             val new_scheme = Ty.mkTypeScheme([], newty)
             val TE' = TyEnv.declare(x,new_scheme,TE)
             val (S1,t1,ok1) = tc(TE', e)
          in (S1, Ty.mkTypeArrow(S1 on newty,t1), ok1)
         end

    | Ex.APPLexpr(e1,e2)=>
        (let val (S1,t1,ok1) = tc(TE, e1)
             val new =  Ty.mkTypeTyvar(Ty.freshTyvar())
             val new' = Ty.mkTypeTyvar(Ty.freshTyvar())
             val arrow1=Ty.mkTypeArrow(new,new')
             val S1' = Unify.unify(arrow1,t1)
                 handle Unify.Unify=>
                 raise Recover(e1,9,S1,[Ty.prType t1])
             val (S2,t2,ok2) = tc((S1' oo S1) onTE TE, e2)
             val new2 = Ty.mkTypeTyvar(Ty.freshTyvar())
             val arrow2 = Ty.mkTypeArrow(t2,new2) 
             val S3 = Unify.unify(arrow2, (S2 oo S1') on t1)
                 handle Unify.Unify=> 
                 raise Recover(exp, 6, (S2 oo S1' oo S1 ), 
                    [Ty.prType ((S2 oo S1') on new),Ty.prType  t2])
          in (S3 oo S2 oo S1' oo S1,
              S3 on new2, ok1 andalso ok2)
         end  handle Recover q=> Recovery.report q)

   )handle Unify.NotImplemented msg => raise NotImplemented msg
       
  and checkIntBin(TE,e1,e2) =
   (let val (S1,t1,ok1) = tc(TE,e1)
        val S1'  = Unify.unify(t1, Ty.mkTypeInt())
                 handle Unify.Unify=> 
                 raise Recover(e1, 7, S1, [Ty.prType t1])
        val (S2,t2,ok2) = tc((S1' oo S1) onTE TE,e2)
        val S2' =  Unify.unify(t2, Ty.mkTypeInt())
                   handle Unify.Unify=> 
                   raise Recover(e2, 7, (S2 oo S1' oo S1), [Ty.prType t2])
     in (S2' oo S2 oo S1' oo S1, Ty.mkTypeInt(), ok1 andalso ok2)
    end handle Recover q=> Recovery.report q);
 
  fun typecheck(e) = let val (_,ty,ok) =
                          tc(TyEnv.emptyEnv,e)
                      in (ty,ok)
                     end

end; (*TypeChecker*)


functor Unify(Ty:TYPE):UNIFY=
struct
   structure Type = Ty
   exception NotImplemented of string
   exception Unify
 
   infix on 
   val op on = Ty.on
   infix oo
   val op oo = Ty.oo
   fun occurs(tv:Ty.tyvar,t:Ty.Type):bool=
     (Ty.unTypeInt t; false)              handle Ty.Type=>
     (Ty.unTypeBool t; false)             handle Ty.Type=>
     let val tv' = Ty.unTypeTyvar t
     in  tv=tv'
     end                                  handle Ty.Type=>
     let val t'  = Ty.unTypeList t
     in  occurs(tv,t')
     end                                  handle Ty.Type=>
     let val (t1,t2)= Ty.unTypeArrow t
     in occurs(tv, t1) orelse occurs(tv, t2)
     end                                  handle Ty.Type=>
   raise NotImplemented "(the occur check)"


   fun unify(t,t')=
   let val tv = Ty.unTypeTyvar t
    in let val tv' = Ty.unTypeTyvar t'
        in Ty.mkSubst(tv,t')
       end                            	handle Ty.Type=>
       if occurs(tv,t') then raise Unify
       else Ty.mkSubst(tv,t')
   end                                  handle Ty.Type=>
   let val tv' = Ty.unTypeTyvar t'
    in if occurs(tv',t) then raise Unify
       else Ty.mkSubst(tv',t)
   end                   		handle Ty.Type=>
   let val ? = Ty.unTypeInt t
    in let val ? = Ty.unTypeInt t'
        in Ty.Id
       end handle Ty.Type=> raise Unify
   end					handle Ty.Type =>
   let val ? = Ty.unTypeBool t
    in let val ? = Ty.unTypeBool t'
        in Ty.Id
       end handle Ty.Type=> raise Unify
   end					handle Ty.Type=>
   let val t = Ty.unTypeList t
    in let val t' = Ty.unTypeList t'
        in unify(t,t')
       end handle Ty.Type => raise Unify
   end 					handle Ty.Type=>
   let val (t1,t2)= Ty.unTypeArrow(t)
    in let val (t1',t2') = Ty.unTypeArrow(t')
        in let val S1 = unify(t1,t1')
               val S2 = unify(S1 on t2, S1 on t2')
            in S2 oo S1
           end
       end handle Ty.Type => raise Unify
   end 					handle Ty.Type=>
   raise NotImplemented "(unify)"     

end; (*Unify*)
  
                     (* the basics -- nullary functors *)


functor Type(structure List:LISTUTIL
             structure Print: PRINTUTIL) :TYPE =
struct
  type tyvar = int
  (*E' un generatore di numeri interi. Esso viene utilizzato dalla nostra struttura per creare varibili di tipo. Queste variabili di tipo saranno identificate da un numero intero.*)
  val freshTyvar =
      let val r= ref 0 in fn()=>(r:= !r +1; !r) end
	  
  (*
	Il seguente datatype rappresenta i nostri tipi. Questi tipi 
  *)
  datatype Type = INT
                | BOOL
                | LIST of Type
                | ARROW of Type * Type 
                | TYVAR of tyvar  

  datatype TypeScheme = FORALL of tyvar list * Type

  (*Prende un Type t e restituisce la lista di variabili di tipo contenute in t. Ovviamente dato che le nostre variabili di tipo sono identificate da numeri interi essa sarà una lista di numeri interi.*)
  fun tyvarsTy INT = []
    | tyvarsTy BOOL = []
    | tyvarsTy (LIST ty) = tyvarsTy ty
    | tyvarsTy (ARROW(ty,ty')) = List.union(tyvarsTy ty, tyvarsTy ty')
    | tyvarsTy (TYVAR tyvar) = [tyvar];

  (*
	Prende in input un tipo FORALL comprese le variabili di tipo su cui di astra e le variabili libere nel corpo. Restituisce la lista di variabili di tipo libere nel corpo su cui non si sta astraendo.
  *)
  fun tyvarsTySch(FORALL(tyvarlist, ty))= List.minus(tyvarsTy ty, tyvarlist)

  (*
    Prende un TypeScheme e ritorna un Type. Esegue i seguenti passi:
	- Per prima cosa crea una variabile old_to_new_tyvars che non è altro che la lista di coppie tali che il primo elemento sarà il numero della variabile di tipo dato in input e il secondo sarà il nuovo numero della stessa variabile di tipo. Quindoi si può dire che è una ridenominazione delle variabili di tipo;
	- Crea una funzione find che non fa altro che prendere in input un identificatore di variabile di tipo (intero) e una lista di coppie creata nel modo descritto poco fa e restituisce il nuovo identificatore per quella variabile di tipo;
	- Crea una funzione ty_istance che prende in input un tipo e restituisce il type in input con tutte le variabili di tipo mappate nelle nuove variabili di tipo create nel primo passo.
	- Applica ty_instance al corpo di FORALL. Quindi in parole povere instance prende in input un FORALL e restituisce il suo copro con le variabili di tipo su cui si sta astraendo ridenominate.
  *)
  fun instance(FORALL(tyvars,ty))=
  let val old_to_new_tyvars = map (fn tv=>(tv,freshTyvar())) tyvars
      exception Find;
      fun find(tv,[]:(tyvar*tyvar)list)= raise Find
      |   find(tv,(tv',new_tv)::rest)=
          if tv=tv' then new_tv else find(tv,rest)
      fun ty_instance INT = INT
      |   ty_instance BOOL = BOOL
      |   ty_instance (LIST t) = LIST(ty_instance t)
      |   ty_instance (ARROW(t,t'))= ARROW(ty_instance t, ty_instance t')
      |   ty_instance (TYVAR tv) = 
             TYVAR(find(tv,old_to_new_tyvars)
                   handle Find=> tv)

  in 
     ty_instance ty
  end
             

  exception Type

  fun mkTypeInt() = INT
  and unTypeInt(INT)=()
    | unTypeInt(_)= raise Type

  fun mkTypeBool() = BOOL
  and unTypeBool(BOOL)=()
    | unTypeBool(_)= raise Type

  fun mkTypeList(t)=LIST t
  and unTypeList(LIST t)= t
    | unTypeList(_)= raise Type

  fun mkTypeArrow(t,t')= ARROW(t,t')
  and unTypeArrow(ARROW(t,t'))= (t,t')
    | unTypeArrow(_) = raise Type

  fun mkTypeTyvar tv = TYVAR tv
  and unTypeTyvar(TYVAR tv) = tv
    | unTypeTyvar _ = raise Type
  
  fun mkTypeScheme(l,ty)= FORALL(l,ty)
  and unTypeScheme(FORALL(l,ty))= (l,ty)

  type subst = Type -> Type

  fun Id x = x
  (*
    Prende in input due variabili di tipo e restituisce una funzione che mappa la prima variabile di tipo con la seconda variabile di tipo.
  *)
  fun mkSubst(tv,ty)=
     let fun su(TYVAR tv')= if tv=tv' then ty else TYVAR tv'
         |   su(INT) = INT
         |   su(BOOL)= BOOL
         |   su(LIST ty') = LIST (su ty')
         |   su(ARROW (ty,ty'))= ARROW(su ty, su ty')
      in su
     end

  
  fun on(S,t)= S(t)
  infixr on
  
  (*
	 Prende in input una funzione S e un tipo FORALL. Dopodichè esegue i seguenti passi:
	 - Crea una variabile fv che contiene la lista di variabili di tipo in ty.
	 - Crea una variabile fvrange 
  *)
  fun onScheme(S,FORALL(bounds,ty)) = 
      let val fv = tyvarsTy ty
          val fvrange= 
           List.fold(fn (tv,res)=>
                      List.union(tyvarsTy(S(TYVAR tv)),res))
                    []
                    fv
          val criticals= List.intersect(bounds, fvrange)
          val criticals'= map (freshTyvar o (fn _=>())) 
                          criticals
          val renlist = List.zip(criticals,criticals')
          fun renaming(TYVAR tv) =TYVAR(List.lookup renlist tv
                                        handle List.Lookup=>tv)
            | renaming(INT)=INT
            | renaming(BOOL)=BOOL
            | renaming(LIST ty)= (LIST (renaming ty))
            | renaming(ARROW(ty,ty'))= ARROW(renaming ty, renaming ty')

          val bounds'= List.map (fn tv=> List.lookup renlist tv
                                         handle List.Lookup => tv)
                                bounds
                            
          val ty'= S on renaming on ty
       in FORALL(bounds',ty')
      end

  val oo = op o; (* composition of substitutions is just
                    function composision *)



  fun prType INT = "int"
  |   prType BOOL= "bool"
  |   prType (LIST ty) = "(" ^ prType ty ^ ")list"
  |   prType (ARROW(ty,ty'))= "(" ^ prType ty ^ "->" ^ prType ty' ^ ")"
  |   prType (TYVAR tv) = "a" ^ Print.intToString tv
end;

functor TypeEnv(structure Type: TYPE 
                structure E: ENVIRONMENT 
                structure List: LISTUTIL): TYPEENV=
struct
  structure Type = Type
  structure E = Environment()
  open E
  type typeenv = Type.TypeScheme Environment
  
  fun close(TE, ty)= 
      let fun f(tyscheme, tyvars)= List.union(Type.tyvarsTySch tyscheme,
                                              tyvars)
          val tyvarsTE = E.fold f [] TE
          val bound = List.minus(Type.tyvarsTy ty, tyvarsTE)
       in Type.mkTypeScheme(bound,ty)
      end;
 
  fun onTE(S,TE)=
      E.map(fn(scheme)=> Type.onScheme(S,scheme)) TE
end;


