---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# A Naive Substitution-Based Type Inferencer

In this lesson you learn how to define a naive substitution-based type
inferencer for a higher-order language, namely the LAMBDA language
defined in Part 1 of the tutorial.

Unlike in the type checker defined in Lessons 2 and 3, where we had to
associate a type with each declared variable, a type inferencer
attempts to infer the types of all the variables from the way those
variables are used. Let us take a look at this program, say `plus.lambda`:

    lambda x . lambda y . x + y

Since `x` and `y` are used in an integer addition context, we can infer
that they must have the type `int` and the result of the addition is
also an `int`, so the type of the entire expression is `int -> int -> int`.
Similarly, the program `if.lambda`

    lambda x . lambda y . lambda z .
      if x then y else z

can only make sense when `x` has type `bool` and `y` and `z` have the same
type, say `t`, in which case the type of the entire expression is
`bool -> t -> t -> t`. Since the type `t` can be anything, we say that
the type of this expression is _polymorphic_. That means that the code
above can be used in different contexts, where `t` can be an `int`, a
`bool`, a function type `int -> int`, and so on.

In the `identity.lambda` program

    let f = lambda x . x
    in f 1

`f` has such a polymorphic type, which is then applied to an integer,
so this program is type-safe and its type is `int`.

A typical polymorphic expression is the composition

    lambda f . lambda g . lambda x .
      g (f x)

which has the type `(t1 -> t2) -> (t2 -> t3) -> (t1 -> t3)`, polymorphic
in 3 types.

Let us now define our naive type inferencer and then we discuss more
examples. The idea is quite simple: we conceptually do the same
operations like we did within the type checker defined in Lesson 2,
with two important differences:

1. instead of declaring a type with each declared variable, we assume
   a fresh type for that variable; and
2. instead of checking that the types of expressions satisfy the
   type properties of the context in which they are used, we impose
   those properties as type equality constraints. A general-purpose
   unification-based constraint solving mechanism is then used to solve
   the generated type constraints.

Let us start with the syntax, which is essentially identical to that
of the type checker in Lesson 2, except that bound variables are not
declared a type anymore. Also, to keep things more compact, we put
all the `Exp` syntax declarations in one syntax declaration this time.

<!-- This part needs to change -->

Before we modify the rules, let us first define our machinery for
adding and solving constraints. First, we require and import the
unification procedure. We do not discuss unification here, but if you
are interested you can consult the `unification.k` files under
[k-distribution/include/kframework/builtin](../../../../include/kframework/builtin/README.md), which contains our current generic
definition of unification, which is written also in K. The generic unification
provides a sort, `Mgu`, for _most-general-unifier_, an operation
`updateMgu(Mgu,T1,T2)` which updates `Mgu` with additional constraints
generated by forcing the terms `T1` and `T2` to be equal, and an operation
`applyMgu(Mgu,T)` which applies `Mgu` to term `T`. For our use
of unification here, we do not even need to know how `Mgu` terms are
represented internally.

We define a K item construct, `=`, which takes two `Type` terms and
enforces them to be equal by means of updating the current `Mgu`.
Once the constraints are added to the `Mgu`, the equality dissolves
itself. With this semantics of `=` in mind, we can now go ahead and
modify the rules of the type checker systematically into rules
for a type inferencer. The changes are self-explanatory and
mechanical: for example, the rule

    rule int * int => int

changes into rule

    rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int

generating the constraints that the two arguments of multiplication
have the type `int`, and the result type is `int`. Recall that each type
equality on the `<k/>` cell updates the current `Mgu` appropriately and
then dissolves itself; thus, the above says that after imposing the
constraints `T1=int` and `T2=int`, multiplication yields a type `int`.

As mentioned above, since types of variables are not declared anymore,
but inferred, we have to generate a fresh type for each variable at its
declaration time, and then generate appropriately constraints for it.
For example, the type semantics of `lambda` and `mu` become:

    rule lambda X . E => T -> E[T/X]  when fresh(T:Type)
    rule mu X . E => (T -> T) E[T/X]  when fresh(T:Type)

that is, we add a condition stating that the previously declared type
is now a fresh one. This type will be further constrained by how the
variable `X` is being used within `E`.

Interestingly, the previous typing rule for lambda application is not
powerful enough anymore. Indeed, since types are not given anymore,
it may very well be the case that the inferred type of the first
argument of the application construct is not yet a function type
(remember, for example, the program composition.lambda above). What
we have to do is to enforce it to be a function type, by means of
fresh types and constraints. We can introduce a fresh type for the
result of the application, and then write the expected rule as
follows:

    rule T1:Type T2:Type => T1 = (T2 -> T) ~> T  when fresh(T:Type)

The conditional requires that its first argument is a `bool` and its
second and third arguments have the same type, which is also the
result type.

The macros do not change, in particular `let` is desugared into lambda
application. We will next see that this is a significant restriction,
because it limits the polymorphism of our type system.

We are done. We have a working type inferencer for LAMBDA.

Let's `kompile` it and `krun` the programs above. They all work as
expected. Let us also try some additional programs, to push it to its
limits.

First, let us test `mu` by means of a `letrec` example:

    letrec f x = 3
    in f

We can also try all the programs that we had in our first tutorial, on
lambda, for example the `factorial.imp` program:

    letrec f x = if x <= 1 then 1 else (x * (f (x + -1)))
    in (f 10)

Those programs are simple enough that they should all work as
expected with our naive type inferencer here.

Let us next try to type some tricky programs, which involve more
complex and indirect type constraints.

`tricky-1.lambda`:

    lambda f . lambda x . lambda y . (
      (f x y) + x + (let x = y in x)
    )

`tricky-2.lambda`:

    lambda x .
      let f = lambda y . if true then y else x
      in (lambda x . f 0)

`tricky-3.lambda`:

    lambda x . let f = lambda y . if true then x 7 else x y
               in f

`tricky-4.lambda`:

    lambda x . let f = lambda x . x
               in let d = (f x) + 1
                  in x

`tricky-5.lambda`:

    lambda x . let f = lambda y . x y
               in let z = x 0 in f

It is now time to see the limitations of this naive type inferencer.
Consider the program

    let id = lambda x . x
    in if (id true) then (id 1) else (id 2)

Our type inferencer fails graciously with a clash in the `<mgu/>` cell
between `int` and `bool`. Indeed, the desugaring macro of `let` turns it
into a `lambda` and an application, which further enforce `id` to have a
type of the form `t -> t` for some fresh type `t`. The first use of `id`
in the condition of `if` will then constrain `t` to be `bool`, while the
other uses in the two branches will enforce `t` to be `int`. Thus the
clash in the `<mgu/>` cell.

Similarly, the program

    let id = lambda x . x
    in id id

yields a different kind of conflict: if `id` has type `t -> t`, in order
to apply `id` to itself it must be the case that its argument, `t`, equals
`t -> t`. These two type terms cannot be unified because there is a
circular dependence on `t`, so we get a cycle in the `<mgu/>` cell.

Both limitations above will be solved when we change the semantics of
`let` later on, to account for the desired polymorphism.

Before we conclude this lesson, let us see one more interesting
example, where the lack of let-polymorphism leads not to a type error,
but to a less generic type:

    let f1 = lambda x . x in
      let f2 = f1 in
        let f3 = f2 in
          let f4 = f3 in
            let f5 = f4 in
              if (f5 true) then f2 else f3

Our current type inferencer will infer the type `bool -> bool` for the
program above. Nevertheless, since all functions `f1`, `f2`, `f3`, `f4`, `f5`
are the identity function, which is polymorphic, we would expect the
entire program to type to the same polymorphic identity function type.

This limitation will be also addressed when we define our
let-polymorphic type inferencer.

Before that, in the next lesson we will show how easily we can turn
the naive substitution-based type inferencer discussed in this lesson
into a similarly naive, but environment-based type inferencer.

Go to [Lesson 5, Type Systems: A Naive Environment-Based Type Inferencer](../lesson_5/README.md).
