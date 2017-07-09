# Calculus of CoHerent ImplicitS

Type checker for the Cochis calculus and translation to explicit terms.

Based on *Cochis: Deterministic and Coherent Implicits*,
a technical report by
Tom Schrijvers, Bruno C. d. S. Oliveira, Philip Wadler (2017).

Language:

    E = x                   -- variable
      | \x -> E             -- abstraction (λ)
      | E E                 -- application
      | (E :: forall a. _)  -- type abstraction (Λ)
      | E @T                -- type application
      | implicit @i E       -- implicit abstraction (λ?)
      | with E E            -- implicit application
      | (_ :: T)            -- implicit query (?)

    Note: (with e1 e0) is the implicit function e0 applied to e1

    T = a            -- variable
      | A            -- type constructor
      | forall a. T  -- universal type
      | T -> T       -- function type
      | T ~> T       -- rule type
