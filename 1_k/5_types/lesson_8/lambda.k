// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

// NOTE: this definition is not up to date with the latest version of K, as it
// uses both substitution and symbolic reasoning.
// It is intended for documentation and academic purposes only.

requires "substitution.md"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

  syntax Exp ::= Int | Bool | KVar
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [seqstrict, left]
               > Exp "*" Exp                      [seqstrict, left]
               | Exp "/" Exp                      [seqstrict]
               > Exp "+" Exp                      [seqstrict, left]
               > Exp "<=" Exp                     [seqstrict]
               > "lambda" KVar "." Exp              [binder]
               | "if" Exp "then" Exp "else" Exp   [seqstrict]
               | "let" KVar "=" Exp "in" Exp          [macro]
               | "letrec" KVar KVar "=" Exp "in" Exp  [macro]
               | "mu" KVar "." Exp                  [binder]

  syntax Type ::= "int" | "bool"
                | Type "->" Type                  [klabel(functionType)]
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>

  rule _I:Int => int
  rule _B:Bool => bool
  rule <k> X:KVar => T ...</k>  <tenv>... X |-> T ...</tenv>
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool

  syntax Exp ::= Exp "->" Exp                  [seqstrict, klabel(functionType)]
  rule <k> lambda X:KVar . E => ?T:Type -> E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  rule T1:Type T2:Type => T1 = (T2 -> ?T:Type) ~> ?T
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1
  rule let X = E in E' => E'[E/X]
  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'
  rule <k> mu X:KVar . E:Exp => (?T:Type -> ?T) E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  syntax KItem ::= Type "=" Type
  rule T = T => .

  syntax KItem ::= setTenv(Map)
  rule <k> _T:Type ~> (setTenv(TEnv) => .K) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
