/- Evaluation is the process of finding the value of an expression. In Lean, programs work
the same way as mathematical expressions. If two expressions have the same value, replacing
one with the other will not cause the program to compute a different result.
-/

-- To evaluate an expression, we can use the #eval command.
#eval 2 + 2

-- Lean follows the standard rules of precedence and associativity for arithmetic operations.
#eval 1 + 2 * 5

-- We can also use the #eval command to evaluate a function. Functions, typically f(x), are
-- follow the convention of being written as the function name next to the arguments f x.
#eval (fun x ↦ x + 1) 2

#eval String.append "Hello" " world!"

#eval String.length "Lean4 is fun!"

-- In lean, we do not have conditional statements (if-else clauses), we only have conditional expressions
#eval String.append "The evaluation is " (if true then "correct" else "incorrect")
#eval String.append "The evaluation is " (if false then "correct" else "incorrect")

-- Exercises
-- Expected 61
#eval 42 + 19
-- Expected "ABC"
#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
-- Expected 5
#eval if 3 == 3 then 5 else 7
-- Expected "not equal"
#eval if 3 == 4 then "equal" else "not equal"
