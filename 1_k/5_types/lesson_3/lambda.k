// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module LAMBDA
  imports DOMAINS
  syntax Type ::= "int" | "bool"
                | Type "->" Type               [klabel(functionType)]
                | "(" Type ")"                 [bracket]

  syntax Exp ::= Id
               | "lambda" Id ":" Type "." Exp
               | Exp Exp                       [strict, left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="blue"> .Map </tenv>
                </T>

  syntax Exp ::= Exp "->" Exp                  [strict, klabel(functionType)]
  rule <k> lambda X : T . E => (T -> E) ~> Rho ...</k>
       <tenv> Rho => Rho[X <- T] </tenv>

  rule <k> X:Id => T ...</k> <tenv>... X |-> T ...</tenv>
  rule (T1 -> T2) T1 => T2

  syntax Exp ::= Int | Bool
               | Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  rule _:Int => int
  rule _:Bool => bool
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool

  syntax Exp ::= "if" Exp "then" Exp "else" Exp                       [strict]
  rule if bool then T:Type else T => T

  syntax Exp ::= "let" Id ":" Type "=" Exp "in" Exp [macro]
  rule let X : T = E in E' => (lambda X : T . E') E

  syntax Exp ::= "letrec" Id ":" Type Id ":" Type "=" Exp "in" Exp [macro]
               | "mu" Id ":" Type "." Exp
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'
  rule <k> mu X : T . E => (T -> T) E ~> Rho ...</k>
       <tenv> Rho => Rho[X <- T] </tenv>

// Auxiliary type environment recovery
  rule <k> _:Type ~> (Rho => .K) ...</k> <tenv> _ => Rho </tenv>
endmodule
