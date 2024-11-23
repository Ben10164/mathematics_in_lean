-- Simple type theory

/-
\ So what is type theory?

Basically, it is based on the fact that every expression has an associated type.
e.g. x + 0 may denote a natural number, while f may denote a function on natural numbers
-/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/-
Generally, it is
def [name] : [type] := [value]
-/

-- Lets check their types!

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

-- Now lets evaluate some things

#eval 5 * 4
#eval 5 + n
#eval b1 && b2

/-
\ Functional programming type syntax things

The way that functions are described in functional languages are:
[input 1 type] -> [input 2 type] -> ... -> [input n type] -> [output type]
And this actually lets us do some cool things, especially if a function
takes in another function

So like in ocaml we can do something like this:

(* Type Declaration *)
type ('a, 'b) kvlist =
  | Node of 'a * 'b * ('a, 'b) kvlist
  | Nil
;;

Basically, this means that there is a thing called a
kv (key, value) list that has two types, a type for the
key and a type for the value.

(* 'a -> 'b -> ('a, 'b) kvlist -> ('a, 'b) kvlist *)
let insert a b kvlist = Node (a, b, kvlist)

So when we define the insertion, it takes in a value for the key of type 'a,
a value for the value of type 'b, and a kv list with a key type of 'a and a
value type of 'b.
-/

#check Nat.add
-- this tells us that adding natural numbers takes in 2 Nat's and outputs a new Nat
#check (Nat -> Nat) -> Nat

-- Array syntax btw
#eval (5, 9).1
#eval (5, 9).2

-- Notice how the type of these things, is `Type`
#check Nat
#check Bool
#check Nat -> Bool
#check Nat × Bool -- Note; this is `\times`, not `*` or `x`
#check Nat -> Nat
#check Nat × Nat -> Nat
#check Nat -> Nat -> Nat
#check Nat -> (Nat -> Nat)
#check Nat -> Nat -> Bool
#check (Nat -> Nat) -> Nat

def α : Type := Nat -- `\alpha`
def β : Type := Bool -- `\beta`
def G : Type -> Type -> Type := Prod
-- notice
#check Prod α β
#check α × β
#check List α
#check List Nat

-- Heres something funny
#check Type
#check Type 2
#check Type 3
-- Type 0 is a universe of small, or ordinary types
-- Type 1 is a larger universe of types, containing Type 0 as an element
-- Type 2 is even larger ...
-- This list is infinite
#check Sort
#check Prod

def F.{u} (α : Type u) : Type u := Prod α α

#check F

/-
Function Abstraction and Evaluation
fun (or λ) is a keyword to create a function
-/

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x => x + 5
#check λ x => x + 5


#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

/-
Lets do some functions!!
-/

def f (n : Nat) : String := toString n
#check f
#eval f 5

#check fun (g : String -> Bool) (f : Nat -> String) (x : Nat) => g (f x)
#eval (fun x : Nat => x) 1


def double (x : Nat) : Nat :=
 x + x

#eval double 3

-- We can also use lambda functions, so the following is the same

def double_lambda : Nat -> Nat :=
  fun (x : Nat) => x + x

#eval double_lambda 3

def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)

-- Funny thing, you can think of variables as functions, soooo
def pi := 3.14159265

def greater (x y : Nat) :=
  if x > y then x
  else y

-- Now this is where higher order functions are introduced

-- This function takes another function in as a parameter
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2

/-
Big example...
-/

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/-
This means compose is a function that takes any two functions as input arguments,
so long as those functions each take only one input.
The type algebra β → γ and α → β means it is a requirement that the type of the
output of the second function must match the type of the input to the first function,
which makes sense, otherwise the two functions would not be composable.

compose also takes a 3rd argument of type α which it uses to invoke the second
function (locally named f) and it passes the result of that function (which is type β)
as input to the first function (locally named g). The first function returns a type γ
so that is also the return type of the compose function.

compose is also very general in that it works over any type α β γ.
This means compose can compose just about any 2 functions so long as they each take one
parameter, and so long as the type of output of the second matches the input of the first.
For example:
-/

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3

-- this is basically
-- "Lets do a function with types Nat, Nat, and Nat
-- Then it reads in double (which returns a nat),
-- square (which returns a nat) and 3 (a nat)
-- But also note how double requires a nat input, which
-- square is, and square requires a nat input, which 3 is
-- Pretty cool stuff
