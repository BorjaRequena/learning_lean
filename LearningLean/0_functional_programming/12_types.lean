/- Types are a fundamental concept in Lean. They are used to classify programs based on the values
they can compute. Types serve multiple roles:
- Find the best in-memory representation of a value
- Make sure the program behaves as expected
- Prevent mistakes (e.g. adding a number to a string)
- Help automate the production of auxiliary code

Every program and, more precisely, every expression must have a type in Lean. In some cases, they are
inferred by the compiler, but in others, we need to specify them explicitly.
-/

-- We can specify the type with the colon operator.
#eval (1 + 2 : Nat)

-- Nat is the default type for non-negative integers in Lean, although it is not always the best choice.
-- For example, in subtractions that result in negative numbers it will return zero.
#eval (1 - 2 : Nat)

-- In these cases, we need to use the Int type.
#eval (1 - 2 : Int)

-- To check the type of an expression without evaluating it, we can use the #check command.
#check (1- 2 : Int)

-- When a program can't be given a type, Lean will return an error both from #check and #eval.
-- Let's break it by providing a list instead of a string to the first argument of append.
#check String.append ["hello", " "] "world"
