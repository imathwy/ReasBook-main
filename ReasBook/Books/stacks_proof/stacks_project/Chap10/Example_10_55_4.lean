import stacks_proof.stacks_project.Chap10.Example_10_55_3

-- Declarations for this item will be appended below by the statement pipeline.

variable (k : Type*) [Field k]

/- Example 10.55.4: for a field `k`, the polynomial ring `k[X]` is a principal ideal domain, so
Example 10.55.3 specializes to the canonical equivalence identifying `K₀(k[X])` with `ℤ`. -/
#check (projectiveGrothendieckGroup_pidEquiv (Polynomial k) :
  projectiveGrothendieckGroup (Polynomial k) ≃+ ℤ)

/- Example 10.55.4: the same specialization identifies `K'_0(k[X])`, modeled here by finitely
generated `k[X]`-modules, with `ℤ`. -/
#check (finiteGrothendieckGroup_pidEquiv (Polynomial k) :
  finiteGrothendieckGroup (Polynomial k) ≃+ ℤ)
