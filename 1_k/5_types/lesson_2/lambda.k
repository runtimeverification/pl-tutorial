// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "substitution.md"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

  syntax Type ::= "int" | "bool"
                | Type "->" Type               [klabel(functionType)]
                | "(" Type ")"                 [bracket]

  syntax Exp ::= KVar
               | "lambda" KVar ":" Type "." Exp  [binder]
               | Exp Exp                       [strict, left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  syntax Exp ::= Exp "->" Exp                  [strict, klabel(functionType)]

  rule lambda X : T . E => T -> (E[T/X])
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

  syntax Exp ::= "let" KVar ":" Type "=" Exp "in" Exp [macro]
  rule let X : T = E in E' => (lambda X : T . E') E

  syntax Exp ::= "letrec" KVar ":" Type KVar ":" Type "=" Exp "in" Exp  [macro]
               | "mu" KVar ":" Type "." Exp                             [binder]
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'
  rule mu X : T . E => (T -> T) (E[T/X])
endmodule
