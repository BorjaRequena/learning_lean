/- While a structure is an excellent way to keep track of a fixed set of fields, many applications
require data that may contain an arbitrary number of elements. Most classic data structures, such
as trees and lists, have a recursive structure, where the tail of a list is itself a list, or where
the left and right branches of a binary tree are themselves binary trees. In a calculator, the
structure of expressions themselves (addition, subtraction, multiplication) is recursive. The
summands in an addition expression may themselves be multiplication expressions, for instance.

Datatypes that allow choices are called sum types and datatypes that can include instances of
themselves are called recursive datatypes. Recursive sum types are called inductive datatypes,
because mathematical induction may be used to prove statements about them. When programming,
inductive datatypes are consumed through pattern matching and recursive functions.

Many built-in types are inductive datatypes, like Bool:
inductive Bool where
  | true : Bool
  | false : Bool

The first line provides the name of the new type (Bool), while the remaining lines each describe a
constructor. As with constructors of structures, constructors of inductive datatypes just receive
and store data. Unlike structures, inductive datatypes may have multiple constructors. Here, there
are two constructors, true and false, and neither takes any arguments. Just as a structure
declaration places its names in a namespace named after the declared type, an inductive datatype
places the names of its constructors in a namespace. In the Lean standard library, true and false
are re-exported from this namespace so that they can be written alone, rather than as Bool.true
and Bool.false, respectively.

The Bool type is a sum type because it can be either true or false.

The type Nat of non-negative integers is an inductive datatype:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

Here, zero represents 0, while succ represents the successor of some other number. The Nat mentioned
in succ's declaration is the very type Nat that is in the process of being defined. Successor means
“one greater than”, so 4 is represented as Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))). This
definition is almost like the definition of Bool with slightly different names. The only real
difference is that the constructor succ takes an argument, while the constructor true and false
take no arguments.

In Lean, we can operate over these types with pattern matching. This serves as a way to identify
the subclass that an element belongs to, as well as to extract the data from the corresponding
field. We can see an example in the following function:
-/

def isZero (n : Nat) : Bool :=
  match n with  -- Match n to either Nat.zero or Nat.succ and operate on the result
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero 0
#eval isZero 1

/- Here, we do not care about the actual value of the argument, so we use _ as a wildcard. We can
now experiment with a function to find the predecessor of a Nat to show how to use it. To find the
predecessor of a Nat, the first step is to check which constructor was used to create it. If it was
Nat.zero, then the result is Nat.zero. If it was Nat.succ, then the name k is used to refer to the
Nat underneath it. This Nat is the desired predecessor, so the result of the Nat.succ branch is k.
-/
def predecessor (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

-- `predecessor 5` is actually `predecessor (Nat.succ 4)` which is `4`
#eval predecessor 0
#eval predecessor 1
#eval predecessor 37

/- Definitions that refer to the name being defined are called recursive definitions. Inductive
datatypes are allowed to be recursive; indeed, Nat is an example of such a datatype because succ
demands another Nat.

Recursive datatypes are nicely complemented by recursive functions. In those, non-recursive
branches of the code are called base cases.
-/

-- Let's see an example of a function to find if a Nat is even. A number is even if its predecessor isn't.
def isEven (n : Nat) : Bool :=
  match n with
  | Nat.zero => true  -- Base case (assume zero is even because 1 is odd)
  | Nat.succ k => not (isEven k)  -- Recursive case

#eval isEven 0
#eval isEven 1
#eval isEven 8

-- Lean will not let us define a recursive function that will never terminate.
def isEvenInfinite (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (isEvenInfinite n)  -- Apply over n not k

-- We not always need to inspect all the arguments of a function. For example, in summation we can
-- inspect only one:
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | Nat.zero => n
  | Nat.succ m' => Nat.succ (add n m')  -- Apply Nat.succ m times to n

#eval add 0 0
#eval add 1 0
#eval add 7 2

-- Similarly, we can define a function to multiply two Nats
def multiply (n : Nat) (m : Nat) : Nat :=
  match m with
  | Nat.zero => Nat.zero
  | Nat.succ m' => add n (multiply n m')  -- Add n to itself m times

#eval multiply 0 3
#eval multiply 1 5
#eval multiply 7 2

-- In subtraction, we can also use the same philosophy
def subtract (n : Nat) (m : Nat) : Nat :=
  match m with
  | Nat.zero => n
  | Nat.succ m' => predecessor (subtract n m')  -- Take n's predecessor m times

-- These recursive functions suggest a recursive form for division
def divide (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (divide (n - k) k)

/- As long as the second argument is not 0, this program terminates, as it always makes progress
towards the base case. However, it is not structurally recursive, because it doesn't follow the
pattern of finding a result for zero and transforming a result for a smaller Nat into a result for
its successor.

Therefore, Lean complains!-/
