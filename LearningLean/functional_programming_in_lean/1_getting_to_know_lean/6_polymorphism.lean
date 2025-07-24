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
def replaceXImplicit {α : Type} (point : PolyPoint α) (newX : α) : PolyPoint α :=
  { point with x := newX }

#eval replaceXImplicit natOrigin 1
#eval replaceXImplicit floatOrigin 1.0
#eval replaceXImplicit stringOrigin "1"

-- Same for length
def lengthImplicit {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (lengthImplicit ys)

#eval lengthImplicit primesUnder10

/- Besides Lists, Lean offers a bunch of other structures and inductive datatypes.

** OPTION **
Lean offers an Option datatype to indicate the possibility of missing values. This is in place of
the typical null of other programming languages. For example, we call Option (List String) to
indicate a list of strings that may be empty.

inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α

Option has two constructors none and some, that respectively represent the absence and presence of
a value. This allows multiple layers of optionality like Option (Option Int), which can be
constructed either with `some (some 3)` or `none none` (?? not sure about this last one)).

For example, the function List.head? finds the head of a list if it exists. The ? is just part of
the name to indicate it returns an Option.
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
-/

#eval primesUnder10.head?
#eval [].head?  -- Can't infer implicit type
#eval [].head? (α := Int)
#eval ([] : List Int).head?

/-
** PROD **
Prod (short for product) is a datatype that represents a pair of values. It is similar to a tuple
in other programming languages. For instance, we could write PolyPoint Nat as Prod Nat Nat. In
some cases, it's better to write a custom structure or type, which will make the code more readable
and may prevent some errors. However, there are many other cases where this is not worth it and we
just need the notion of a "pair of things".

structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β

Prods are used so often that Lean provides a special syntax for them: α × β. This is \ x or \ times
-/

-- Let's see an example with the full syntax
def fives : Prod String Nat := { fst := "five", snd := 5 }

#eval fives

-- We can keep it simpler and more readable with the special syntax
def threes : String × Int := ("three", 3)

-- The notation is right-associative, meaning the following two expressions are equivalent
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens' : String × (Int × Nat) := ("VII", (7, 4 + 3))

#eval sevens
#eval sevens'

/-
** SUM **
Sum is a datatype that represents a choice between two values. It is similar to a union in other
programming languages. For instance, Sum String Int is either a String or an Int, or we could write
Option Nat as Sum Nat Nat. Like Prod, Sum should be used either when writing very generic code, for
a very small section of code. In most situations, it is more readable and maintainable to use a
custom inductive type.

inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β

Sum has two constructors inl and inr, that respectively represent the left and right choice. They
abbreviate left and right injection.

We can use the “circled plus” notation α ⊕ β to represent Sum α β.
-/

def PetName : Type := String ⊕ String

def animals : List PetName :=
  -- Left are dog names, right are cat names
  [Sum.inl "Rex", Sum.inr "Whiskers", Sum.inl "Spot", Sum.inl "Snuffles", Sum.inr "Tiger"]

#eval animals

-- We can use pattern matching, for instance, to count the number of dogs in a name list
def countDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: remainingPets => Nat.succ (countDogs remainingPets)  -- Sum one for each Sum.inl
  | Sum.inr _ :: remainingPets => countDogs remainingPets  -- Ignore Sum.inr

#eval countDogs animals

/-
** UNIT **
Unit is a type with just one argumentless constructor. It describes only a single value, which
consists of said constructor applied to no arguments whatsoever.

inductive Unit : Type where
  | unit : Unit

In polymorphic code, Unit can be used as a placeholder for data that is missing. For instance,
the following inductive datatype represents arithmetic expressions:

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

The type argument ann stands for annotations, and each constructor is annotated. Expressions coming
from a parser might be annotated with source locations, so a return type of ArithExpr SourcePos
ensures that the parser put a SourcePos at each subexpression. Expressions that don't come from the
parser, however, will not have source locations, so their type can be ArithExpr Unit.

Since all Lean functions take arguments, zero-argument functions in other languages can be
represented as functions that take a Unit argument. In a return position, the Unit type is similar
to void in languages derived from C. By being an intentionally uninteresting value, Unit allows
this to be expressed without requiring a special-purpose void feature in the type system. Unit's
constructor can be written as empty parentheses: () : Unit.
-/

#check ()

def sayHello (_ : Unit) : String := "Hello"
#eval sayHello ()

-- With some fancier notation
def sayHi : Unit → String := fun _ => "Hi"
#eval sayHi ()

/- ** EMPTY **

The Empty datatype has no constructors whatsoever. Thus, it indicates unreachable code, because no
series of calls can ever terminate with a value at type Empty.

Empty is not used nearly as often as Unit. However, it is useful in some specialized contexts. Many
polymorphic datatypes do not use all of their type arguments in all of their constructors. For
instance, Sum.inl and Sum.inr each use only one of Sum's type arguments. Using Empty as one of the
type arguments to Sum can rule out one of the constructors at a particular point in a program. This
can allow generic code to be used in contexts that have additional restrictions.
-/

-- Let's see an example where we rule out the inr constructor using Empty
-- This creates a type that can only contain left values (String), never right values
def OnlyStrings : Type := String ⊕ Empty

-- We can only construct values using Sum.inl, never Sum.inr because Sum.inr expects Empty
def someString : OnlyStrings := Sum.inl "hello"
def impossibleString : OnlyStrings := Sum.inr "ampassabol :("

-- This allows us to only work with Sum.inr in functions that works with OnlyStrings
def extractString (value : OnlyStrings) : String :=
  match value with
  | Sum.inl s => s
  -- No need to handle Sum.inr case because it's impossible!

#eval extractString someString

/- EXERCISES
1. Write a function to find the last entry in a list. It should return an Option.
2. Write a function that finds the first entry in a list that satisfies a given predicate. Start
the definition with
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := ….
3. Write a function Prod.switch that switches the two fields in a pair for each other. Start the
definition with
def Prod.switch {α β : Type} (pair : α × β) : β × α := ….
4. Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.
5. Write a function zip that combines two lists into a list of pairs. The resulting list should be
as long as the shortest input list. Start the definition with
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := ….
6. Write a polymorphic function take that returns the first n entries in a list, where n is a Nat.
If the list contains fewer than n entries, then the resulting list should be the entire input list.
#eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
#eval take 1 ["bolete", "oyster"] should yield ["bolete"].
7. Using the analogy between types and arithmetic, write a function that distributes products over
sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
8. Using the analogy between types and arithmetic, write a function that turns multiplication by
two into a sum. In other words, it should have type Bool × α → α ⊕ α.
-/

-- 1. Function to find the last entry in a list returning an Option
def lastEntry? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none  -- Reach the tail or empty list
  | [x] => some x  -- Reach the last entry
  | _ :: xs => lastEntry? xs  -- Keep going until we reach the last entry

#eval lastEntry? [1, 2, 3]
#eval lastEntry? [1]
#eval lastEntry? ([] : List Nat)

-- 2. Function to find the first entry in a list that satisfies a given predicate
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none  -- Reach the tail or empty list
  -- Keep going until we find the first entry that satisfies the predicate or reach the tail
  | x :: xs => if predicate x then some x else List.findFirst? xs predicate

#eval List.findFirst? [1, 2, 3] (fun x => x >= 2)
#eval List.findFirst? [1, 2, 3] (fun x => x > 4)
#eval List.findFirst? ([] : List Nat) (fun x => x > 2)

-- 3. Function to switch the two fields in a pair
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#eval Prod.switch (1, "hello")
#eval Prod.switch ("hello", 1)

-- 4. Rewrite the PetName example to use a custom datatype
inductive PetNameCustom where
  | dog (name : String)
  | cat (name : String)
deriving Repr

def animalsCustom : List PetNameCustom :=
  [PetNameCustom.dog "Rex", PetNameCustom.cat "Whiskers", PetNameCustom.dog "Spot", PetNameCustom.dog "Snuffles", PetNameCustom.cat "Tiger"]

#eval animalsCustom

def countCats (pets : List PetNameCustom) : Nat :=
  match pets with
  | [] => 0
  | PetNameCustom.cat _ :: remainingPets => Nat.succ (countCats remainingPets)
  | PetNameCustom.dog _ :: remainingPets => countCats remainingPets

#eval countCats animalsCustom

-- 5. Function to zip two lists into a list of pairs
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: (zip xs ys)

#eval zip [1, 2, 3] ["a", "b", "c"]
#eval zip [1, 2, 3] ["a", "b"]
#eval zip [1, 2, 3] ([] : List Int)
#eval zip ([] : List Int) ["a", "b", "c"]

-- 6. Function to take the first n entries in a list
def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs => if n > 0 then x :: (take (n - 1) xs) else []

#eval take 1 [1, 2, 3, 4, 5]
#eval take 3 [1, 2, 3, 4, 5]
#eval take 0 [1, 2, 3, 4, 5]
#eval take 10 [1, 2, 3, 4, 5]

-- 7. Function to distribute products over sums α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
-- Exmaple (Nat, String ⊕ Int) → (Nat × String) ⊕ (Nat × Int)
def distribute {α β γ : Type} (x : α) (y : β ⊕ γ) : (α × β) ⊕ (α × γ) :=
  match y with
  | Sum.inl left => Sum.inl (x, left)
  | Sum.inr right => Sum.inr (x, right)

#eval distribute 42 (Sum.inl "hello" : String ⊕ Int)
#eval distribute 42 (Sum.inr 123 : String ⊕ Int)

def testSums : List (String ⊕ Int) := [
  Sum.inl "hello",
  Sum.inr 42,
  Sum.inl "world",
  Sum.inr 123
]
#eval testSums.map (fun sum => distribute 10 sum)

-- 8. Function to turn multiplication by two into a sum, shoudl have type Bool × α → α ⊕ α
def prodToSum {α : Type} (pair : Bool × α) : α ⊕ α :=
  match pair with
  | (true, x) => Sum.inl x
  | (false, x) => Sum.inr x

#eval prodToSum (true, "hello")
#eval prodToSum (false, "world")
#eval prodToSum (true, 42)
#eval prodToSum (false, 123)
