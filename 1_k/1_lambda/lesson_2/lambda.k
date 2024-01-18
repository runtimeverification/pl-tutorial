// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX

  syntax Exp ::= Exp "[" Exp "/" KVar "]" [function]
  rule X:Val [_ / _] => X [owise]

  rule X [V / X] => V

  rule (lambda X . E) [V / Y] => lambda X . (E[V / Y])

  rule (E1:Exp E2:Exp) [V / X] => E1[V / X] (E2[V / X])

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]
endmodule
