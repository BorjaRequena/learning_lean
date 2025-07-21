/- Lean offers some additional conveniences that simplify writing code, resulting in more
concise and readable programs.

** Automatic implicit parameters **
So far, we have been explicitly listing all the implicit parameters in every function definition
that we have written. However, they can be simply mentioned and, if Lean can determine their type,
they will be automatically added as implicit parameters.
-/

def length {α : Type} (xs : List α) : Nat :=  -- Implicit α is manually specified
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

def length' (xs : List α) : Nat :=  -- Implicit α is automatically added
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

#eval length [1, 2, 3]
#eval length' [1, 2, 3]
#eval length' ["hello", "world"]

/-
** Pattern matching definitions **
When defining functions with def, it is quite common to name an argument and then immediately use
it with pattern matching. For instance, in length, the argument xs is used only in match. In these
situations, the cases of the match expression can be written directly, without naming the argument
at all.
-/

def length1 : List α → Nat  -- Again implicit α
  -- Don't need to name the argument xs to match it immediately
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

#eval length1 [1, 2, 3]
#eval length1 ["hello", "world"]

-- We can also use this syntax in functions that take multiple arguments. In these cases, their
-- patterns are separated by commas
def drop : Nat → List α → List α
  -- Drop the first n elements of the list
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

#eval drop 2 [1, 2, 3, 4, 5]
#eval drop 0 ["hello", "world", "lean", "is", "fun"]
#eval drop 5 ([] : List Nat)

-- We can combine named arguments with pattern matching. For example, a function that takes a
-- default value and an optional value, and returns the default when the optional value is none.
def getSomething (default : α) : Option α → α
  -- Implicit α as well as pattern matchign on the Option α without naming it
  | some  x => x
  | none => default

#eval getSomething 0 (some 1)
#eval getSomething 0 none

-- This is equivalent to the `Option.getD` function
#eval Option.getD (some 1) 0
#eval (some "something").getD "default"
#eval none.getD "default"

-- We can rewrite the `getSomething` function using the full explicit syntax
def getSomething' {α : Type} (default : α) (value : Option α): α :=
  match value with
  | some x => x
  | none => default

#eval getSomething' 0 (some 1)
#eval getSomething' 0 none

/-
** Local definitions **
In Lean, we can use `let` to perform local definitions following a similar syntax to the top-level
`def`. After the local definition, the expression in which the local definition is available must
be on a new line, starting at a column in the file that is less than or equal to that of the let
keyword. -/

-- Consider the following unzip function that transforms a list of pairs into a pair of lists
def unzip : List (α × β) -> List α × List β
  | [] => ([], [])
  -- If it's a pair consecutive to a list, we take the first and second elements of uzipping the
  -- rest of the list and append them to each element of the pair
  | (x, y) :: pairs => (x :: (unzip pairs).fst, y :: (unzip pairs).snd)

#eval unzip [(1, "a"), (2, "b"), (3, "c")]

-- In this case, we can use a local definition to avoid repeating the unzip function over pairs
def unzip' : List (α × β) -> List α × List β
  | [] => ([], [])
  | (x, y) :: pairs => let unzipped : List α × List β := unzip pairs
    (x :: unzipped.fst, y :: unzipped.snd)

#eval unzip' [(1, "a"), (2, "b"), (3, "c")]

-- Local definitions can use pattern matching when one pattern can match all cases
def unzip'' : List (α × β) -> List α × List β
  | [] => ([], [])
  | (x, y) :: pairs => let (xs, ys) : List α × List β := unzip'' pairs  -- Unpack the tuple
    (x :: xs, y :: ys)

#eval unzip'' [(1, "a"), (2, "b"), (3, "c")]

-- The difference between let and def is that recursive let definitions must be explicitly written
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α  -- Recursive helper function with `let rec`
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

-- The helper function walks down the input list, moving one entry at a time over to soFar. When it
--reaches the end of the input list, soFar contains a reversed version of the input.

#eval reverse [1, 2, 3]

/-
** Type inference **
In many situations, Lean can automatically determine an expression's type. In these cases, explicit
types may be omitted from both top-level definitions (with def) and local definitions (with let).

As a rule of thumb, omitting the types of literal values (like strings and numbers) usually works,
although Lean may pick a type for literal numbers that is more specific than the intended type.
Lean can usually determine a type for a function application, because it already knows the argument
types and the return type. Omitting return types for function definitions will often work, but
function parameters typically require annotations. Definitions that are not functions do not need
type annotations if their bodies do not need type annotations, and the body of this definition is a
function application.

Generally speaking, it is a good idea to err on the side of too many, rather than too few, type
annotations. Explicit types communicate assumptions about the code to readers. Even if Lean can
determine the type on its own, it can still be easier to read code without having to repeatedly
query Lean for type information. Additionally, explicit types help localize errors. The more
explicit a program is about its types, the more informative the error messages can be. Finally,
explicit types make it easier to write the program in the first place.
-/

-- We can remove the type annotation from the local definition in the unzip function
-- Local definitions can use pattern matching when one pattern can match all cases
def unzipUnannotated : List (α × β) -> List α × List β
  | [] => ([], [])
  | (x, y) :: pairs => let (xs, ys) := unzipUnannotated pairs  -- Don't need to specify a type
    (x :: xs, y :: ys)

#eval unzipUnannotated [(1, "a"), (2, "b"), (3, "c")]

-- We can omit the return type of the function if we explicitly name the variable to match
def unzipUntyped (pairs : List (α × β)) :=  -- Omit the return type
  match pairs with  -- But explicitly match with variable name
  | [] => ([], [])
  | (x, y) :: pairs => let (xs, ys) := unzipUntyped pairs  -- Don't need to specify a type
    (x :: xs, y :: ys)

#eval unzipUntyped [(1, "a"), (2, "b"), (3, "c")]
