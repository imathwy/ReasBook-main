import Mathlib.RingTheory.Ideal.Maps
import stacks_proof.stacks_project.Chap15.Definition_15_71_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
* primary domain: `I`-projective modules, expressed by projective factorizations of scalar
  multiplication maps;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.lsmul`,
  `Module.Projective`,
  `Module.IsIdealProjective`;
* best owner abstraction: the module-level owner is `Module.IsIdealProjective I M`, whose
  primitive data are exactly the projective factorizations of the scalar-action endomorphisms
  `LinearMap.lsmul R M (a : R)` for `a ∈ I`;
* primitive data here: only the annihilator containment `I ≤ Module.annihilator R M`;
* derived API here: each multiplication map from `I` is zero, hence factors through the zero
  projective module.
-/

section

variable {R : Type u} [CommRing R]

section

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.71.5: if the ideal `I` annihilates the `R`-module `M`, then `M` is
`I`-projective. -/
@[stacks 0G94]
theorem isIdealProjective_of_le_annihilator {I : Ideal R}
    (hM : I ≤ Module.annihilator R M) : Module.IsIdealProjective I M where
  factorsThroughProjective a := by
    have hzero : LinearMap.lsmul R M (a : R) = 0 := by
      ext m
      exact Module.mem_annihilator.mp (hM a.2) m
    simpa [hzero] using
      (LinearMap.factorsThroughProjective_zero :
        LinearMap.FactorsThroughProjective (0 : M →ₗ[R] M))

end

end
