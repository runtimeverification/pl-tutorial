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
               | Exp Exp                       [left]
               | "(" Exp ")"                   [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  syntax Exp ::= Exp "->" Exp                  [klabel(functionType)]
  rule lambda X : T . E => T -> (E[T/X])       [anywhere]
  rule (T1 -> T2) T1 => T2                     [anywhere]

  syntax Exp ::= Int                           [klabel(intConst), prefer]
               | Bool                          [klabel(boolConst), prefer]
               | Exp "*" Exp                   [left]
               | Exp "/" Exp
               > Exp "+" Exp                   [left]
               > Exp "<=" Exp

  rule _:Int => int                            [anywhere]
  rule _:Bool => bool                          [anywhere]
  rule int * int => int                        [anywhere]
  rule int / int => int                        [anywhere]
  rule int + int => int                        [anywhere]
  rule int <= int => bool                      [anywhere]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp
  rule if bool then T:Type else T => T         [anywhere]

  syntax Exp ::= "let" KVar ":" Type "=" Exp "in" Exp [macro]
  rule let X : T = E in E' => (lambda X : T . E') E

  syntax Exp ::= "letrec" KVar ":" Type KVar ":" Type "=" Exp "in" Exp  [macro]
               | "mu" KVar ":" Type "." Exp                             [binder]
  rule letrec F : T1  X : T2 = E in E'
    => let F : T1 = mu F : T1 . lambda X : T2 . E in E'
  rule mu X : T . E => (T -> T) (E[T/X])         [anywhere]
endmodule
