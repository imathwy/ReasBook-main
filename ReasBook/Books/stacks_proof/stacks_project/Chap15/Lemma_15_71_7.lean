import Mathlib
import StacksProject_2024.Chap15.Definition_15_71_4
import StacksProject_2024.Chap15.Lemma_15_71_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
* primary domain: duality for `I`-projective modules, expressed through factorization of scalar
  multiplication maps;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `LinearMap.FactorsThroughFiniteProjective`,
  `LinearMap.FactorsThroughProjective.factorsThroughFiniteProjective`,
  `Module.dual_projective`;
* best owner abstraction: `Module.IsIdealProjective I M` is the source-facing owner, while finite
  projective factorizations and dual projectivity are derived `core/canonical` tools;
* primitive data: for each `a : I`, the scalar-action endomorphism
  `LinearMap.lsmul R M (a : R)` factors through a projective module;
* derived API used here: because `M` is finite, each such factorization upgrades to a finite
  projective one, and dualizing that factorization gives the required projective factorization on
  `Module.Dual R M`.
-/

section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 15.71.7: if `M` is a finite `I`-projective `R`-module, then the dual module
`Hom_R(M, R)` is `I`-projective. -/
@[stacks 0G96]
theorem isIdealProjective_dual (hM : Module.IsIdealProjective I M) :
    Module.IsIdealProjective I (Module.Dual R M) where
  factorsThroughProjective a := by
    rcases (hM.factorsThroughProjective a).factorsThroughFiniteProjective with
      ⟨P, _instAddCommGroup, _instModule, _instFinite, _instProjective, f, g, hfg⟩
    refine ⟨Module.Dual R P, inferInstance, inferInstance, inferInstance, g.dualMap, f.dualMap, ?_⟩
    have hsmul :
        LinearMap.dualMap (LinearMap.lsmul R M (a : R)) =
          LinearMap.lsmul R (Module.Dual R M) (a : R) := by
      ext φ m
      change φ ((a : R) • m) = (a : R) • φ m
      simpa using map_smul φ (a : R) m
    have hdual := congrArg LinearMap.dualMap hfg
    simpa [hsmul, LinearMap.dualMap_comp_dualMap] using hdual

end
