-- Eval is essentially just evaluating the value
#eval "Hello, World!"
#eval 4 + 2

-- Similarly, there is check for "checking" what something does (or more importantly, what it takes in, and spits out)
#check Nat
#check Nat.add

variable (a : ℕ)
#check a
#check Nat.add_assoc
