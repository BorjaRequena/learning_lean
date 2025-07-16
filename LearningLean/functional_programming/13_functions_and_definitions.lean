/- In Lean, definitions are done with the `def` keyword, and new names are defined using
the walrus operator `:=`. This is because `=` is used to describe equalities between
existing expressions. Additionally, we will typically need to add a type with the `:`
operator.-/

-- Let's start with a simple definition
def hello := "Hello"

-- Now we can add a type to the definition
def bye : String := "Bye"

/- There are multiple ways to define functions in Lean. The simplest approach is to place
the function's arguments before the type separated by spaces.-/

-- Let's define a function that adds 1 to a number
def add_1 (n : Nat) : Nat := n + 1

-- Now we can evaluate the function
#eval add_1 3

-- We can add multiple arguments by separating them with commas.
def maximum (n : Nat) (k : Nat) : Nat := if n < k then k else n

#eval maximum 3 5
#eval maximum (5 + 8) (2 * 7)

-- Another example with strings
def concatenate_with_space (s1 : String) (s2 : String) : String := String.append s1 (String.append " " s2)

#eval concatenate_with_space "Hello" "world"

-- Lean returns a function's signature when its type is checked with #check
#check add_1

/- Behind the scenes, all functions actually expect one argument. Functions with multiple arguments
are, in fact, functions that return functions and this new function takes the next argument until
no more arguments are expected. -/

-- We can see this in the type of a function with multiple arguments with a single argument
#check maximum 3

-- Exercises
-- Define the function joinStringsWith that places the first argument between the second and the third
def joinStringsWith (s1: String) (s2: String) (s3: String) : String :=
  String.append s2 (String.append s1 s3)

#eval joinStringsWith " " "Hello" "world"
#eval joinStringsWith ", " "One" "and another"

-- What is the type of the function joinStringsWith?
-- Expected String → String → String → String
#check joinStringsWith

-- Define a function volume with type Nat → Nat → Nat → Nat that computes the volume of a rectangular prism
def volume (height : Nat) (width : Nat) (depth : Nat) : Nat := height * width * depth

#eval volume 2 3 4
