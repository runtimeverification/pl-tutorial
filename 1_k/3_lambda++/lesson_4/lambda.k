// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module LAMBDA
  imports DOMAINS
  syntax Exp ::= Id
               | "lambda" Id "." Exp
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  configuration <T>
                  <k> $PGM:Exp </k>
                  <env> .Map </env>
                  <store> .Map </store>
                </T>

  syntax Val ::= closure(Map,Id,Exp)
  syntax Exp ::= Val
  syntax KResult ::= Val

  rule <k> lambda X:Id . E => closure(Rho,X,E) ...</k>
       <env> Rho </env>
  rule <k> closure(Rho,X,E) V:Val => E ~> Rho' ...</k>
       <env> Rho' => Rho[X <- !N] </env>
       <store>... .Map => (!N:Int |-> V) ...</store>
  rule <k> X => V ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> V ...</store>
  rule <k> _:Val ~> (Rho => .K) ...</k> <env> _ => Rho </env>

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E

  syntax Exp ::= "let" Id "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp [macro]
  syntax Id ::= "$x" [token] | "$y" [token]
  rule letrec F:Id X:Id = E in E'
    => let F =
         (lambda $x . ((lambda F . lambda X . E) (lambda $y . ($x $x $y))))
         (lambda $x . ((lambda F . lambda X . E) (lambda $y . ($x $x $y))))
       in E'

  syntax Exp ::= "callcc" Exp  [strict]
  syntax Val ::= cc(K)
  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V ~> _ =>  V ~> K </k>
endmodule
