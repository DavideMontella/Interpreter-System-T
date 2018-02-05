use "interp.sml";

structure List = List();

structure Expression= Expression();

structure Parser= Parser(Expression);

structure Env = Environment();

structure Value = Value(structure Env= Env
                        structure Exp = Expression);

structure Evaluator= 
   Evaluator(structure Expression= Expression
             structure Env = Env        
             structure Value = Value);

structure Ty = Type(structure List = List); 

structure Unify = Unify(Ty);

structure TE =
  TypeEnv(structure Type = Ty
          structure E = Environment()
          structure List = List);


structure TyCh= 
  TypeChecker(structure Ex = Expression
              structure Ty = Ty
              structure Unify= Unify
              structure TyEnv = TE
              structure List = List);

structure Interpreter=
  Interpreter(structure Ty= Ty
              structure Value = Value
              structure Parser = Parser
              structure TyCh = TyCh
              structure Evaluator = Evaluator);

open Interpreter;
