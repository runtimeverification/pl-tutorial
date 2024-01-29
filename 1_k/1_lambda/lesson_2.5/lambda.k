// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports ID-SYNTAX

  syntax Val ::= Id
               | "lambda" Id "." Exp
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS

  syntax Set ::= freeVars( Exp ) [function]
  rule freeVars( V:Id )         => SetItem(V)
  rule freeVars( lambda X . E ) => freeVars( E ) -Set SetItem(X)
  rule freeVars( E1 E2 )        => freeVars(E1) freeVars(E2)

  syntax Id ::= freshVar(Id, Int, Set) [function]
  rule freshVar(V, I, S) => #let X = String2Id(Id2String(V) +String Int2String(I)) #in #if X in S #then freshVar(V, I +Int 1, S) #else X #fi

  syntax Exp ::= Exp "[" Exp "/" Id "]" [function]

  rule X:Exp [_ / _] => X [owise]
  rule X [V / X] => V

  rule (lambda Y . E) [_ / Y] => lambda Y . E
  rule (lambda Y . E) [V / X] => lambda Y . (E[V / X]) requires Y =/=K X andBool notBool (Y in freeVars(V))
  rule (lambda Y . E) [V / X] => #let Z = freshVar(Y, 0, freeVars(E) freeVars(V)) #in lambda Z . (E[Z / Y] [V / X])
    requires Y =/=K X andBool Y in freeVars(V)

  rule (E1:Exp E2:Exp) [V / X] => E1[V / X] (E2[V / X])

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
