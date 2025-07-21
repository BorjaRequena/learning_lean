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
