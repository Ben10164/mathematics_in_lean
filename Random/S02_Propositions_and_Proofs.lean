-- Now time for the good stuff
def Implies (p q : Prop) : Prop := p → q
#check Implies

-- All the general logic things are here
#check And
#check Or
#check Not

-- We can define a variable (or in this case, multiple) Props like this
variable (p q r : Prop)

-- Like all relational algebra, and stack calculators,
-- things go like function, input input
#check And p q
-- And is the function, which takes in p and q, and then does p ^ q
#check Or (And p q) r
-- Or is a function which takes in (And p q) and r,
-- then does (And p q) ∨ r
-- which expands/simplifies to:
-- p ∧ q ∨ r
#check Implies (And p q) (And q p)
-- this expands to
-- (p ∧ q) → (q ∧ p)
-- or in English,
-- both p and q being true implies that both q and p are true

#check Implies (And p q) (Not q)

-- We could then introduce, for each element p : Prop,
-- another type Proof p, for the type of proofs of p.
-- An "axiom" would be a constant of such a type.

structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_communitive (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_communitive p q

-- In addition to axioms, however, we would also need rules to build new proofs from old ones.
-- For example, in many proof systems for propositional logic, we have the rule of modus ponens:
-- "From a proof of Implies p q and a proof of p, we obtain a proof of q."

-- We could represent this as follows:
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
-- this says:
-- modus_pones is an axiom in which given props p and q,
-- if we are told that p implies q, and a proof of p, then we have a proof of q
#check modus_ponens
