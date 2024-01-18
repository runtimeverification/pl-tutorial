// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" KVar "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp [macro]
  syntax KVar ::= "$x" [token] | "$y" [token]
  rule letrec F:KVar X:KVar = E in E'
    => let F =
         (lambda $x . ((lambda F . lambda X . E) (lambda $y . ($x $x $y))))
         (lambda $x . ((lambda F . lambda X . E) (lambda $y . ($x $x $y))))
       in E'
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS

  syntax Exp ::= Exp "[" Exp "/" KVar "]" [function]
  rule X:Exp [_ / _] => X [owise]

  rule X [V / X] => V

  rule (lambda X . E) [V / Y] => lambda X . (E[V / Y])

  rule (E1:Exp E2:Exp) [V / X] => E1[V / X] (E2[V / X])

  rule (E1:Exp *  E2:Exp) [V / X] => E1[V / X] *  (E2[V / X])
  rule (E1:Exp /  E2:Exp) [V / X] => E1[V / X] /  (E2[V / X])
  rule (E1:Exp +  E2:Exp) [V / X] => E1[V / X] +  (E2[V / X])
  rule (E1:Exp <= E2:Exp) [V / X] => E1[V / X] <= (E2[V / X])

  rule (if C then E1 else E2) [V / X] => if C[V / X] then E1[V / X] else (E2[V / X])

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E
endmodule
