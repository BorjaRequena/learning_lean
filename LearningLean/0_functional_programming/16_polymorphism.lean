/- Types in Lean can take arguments. For instance, the type List Nat describes lists of natural
numbers, List String describes lists of strings. In functional programming, the term POLYMORPHISM
typically refers to datatypes and definitions that take types as arguments. These type arguments
can be used in the datatype or definition, which allows the same datatype or definition to be used
with any type that results from replacing the arguments' names with some other types.

Let us illustrate this with the Point structure that we have worked with before. Previously, the
structure required that both x and y were Floats. However, we can consider points with specific
representation for each coordinate. A polymorphic version of such a point can take a type as an
argument, and then use that type for both fields. Let's see how it looks like:
-/

-- We use Greek letters to name type arguments in Lean if no more specific name suggests itself.
structure PolyPoint (α : Type) where
  x : α
  y : α
deriving Repr

-- Just like List, PolyPoint can be used by providing a specific type as its argument
def natOrigin : PolyPoint Nat := { x := Nat.zero, y := Nat.zero}
def floatOrigin : PolyPoint Float := { x := 0.0, y := 0.0 }
def stringOrigin : PolyPoint String := { x := "0", y := "0" }

#eval natOrigin
#eval floatOrigin
#eval stringOrigin

-- Definitions can also be polymorphic taking types as arguments
def replaceX (α : Type) (point : PolyPoint α) (newX : α) : PolyPoint α :=
  { point with x := newX }

#check (replaceX)
#check (replaceX Float)
#check (replaceX Nat natOrigin)

#eval replaceX Nat natOrigin 1
#eval replaceX Float floatOrigin 1.0
#eval replaceX String stringOrigin "1"

/- Polymorphic functions work by taking a named type argument and having later types refer to the
argument's name. However, there's nothing special about type arguments that allows them to be
named. For example, it is possible to write a function that returns a Nat if the value is positive
or an Int if it is negative, given a datatype that represents positive or negative signs.-/

inductive Sign where
  | pos
  | neg

def posOrNegSeven (s : Sign) :
  match s with | Sign.pos => Nat | Sign.neg => Int :=  -- Dynamic expected return type
  -- Function body
  match s with
  | Sign.pos => 7
  | Sign.neg => -7

#eval posOrNegSeven Sign.pos
#eval posOrNegSeven Sign.neg

/- The List type in Lean is an inductive datatype
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
(Not exactly like this but this captures the idea)

This definition says that List takes a single type as its argument, just as PolyPoint did. This
type is the type of the entries stored in the list. According to the constructors, a List α can be
built with either nil or cons. The constructor nil represents empty lists and cons is for non-empty
lists. The first argument to cons is the head of the list, and the second argument is its tail. A
list that contains n entries contains n cons constructors, the last of which has nil as its tail.
-/

-- Let's see an example with a list of natural numbers
def primesUnder10 : List Nat := [2, 3, 5, 7]

-- This list can be written with the explicit list constructors
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

#eval primesUnder10
#eval explicitPrimesUnder10

-- Lists can be understood as Nats that have an extra data field in the succ constructor.
-- We can compute the lenght of a list similarlly to how we did the summation function
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => 0
  | List.cons _ ys => Nat.succ (length α ys) -- Apply Nat.succ until we reach the tail (nil)

-- The names xs and ys are typical convention for lists of arbitrary elements

#eval length Nat primesUnder10

-- Matching against nil can be done with [], and matching against cons can be done with ::
def lenght2 (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (lenght2 α ys)

#eval lenght2 Nat primesUnder10

/- Both in replaceX and length, we have explicitly provided the type argument. However, the
compiler is perfectly capable of determining type arguments on its own, and only
occasionally needs help from users.

Arguments can be DECLARED IMPLICIT by wrapping them in curly braces instead of parentheses
-/

-- Let's rewrite the replaceX function with implicit type argumen
