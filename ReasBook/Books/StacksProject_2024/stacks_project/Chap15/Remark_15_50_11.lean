import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- 
Domain sampling:
* Primary domain: commutative algebra of `G`-rings and adic completion.
* Owner declarations inspected in this domain:
  - `IsGRing`
  - `CompletedLocalizationAtPrime`
  - `isGRing_iff_forall_regular_localization_completion`
  - `AdicCompletion`
* Best owner abstraction: the chapter owner predicate `IsGRing R` on a commutative ring `R`,
  together with the canonical completion owner `AdicCompletion I R`.
* Source/core/bridge triage:
  - `source-facing`: adic completion does not preserve the `G`-ring property in general;
  - `core/canonical`: `IsGRing R` and `AdicCompletion I R`;
  - `bridge/view`: the existential counterexample formulation below.
* Primitive vs. derived: the primitive data are the commutative ring `R` and the ideal `I : Ideal R`;
  the facts that `R` is a `G`-ring and `AdicCompletion I R` is not are derived properties and should
  not be presented as separate primitive existential data.
-/

-- Proof sketch: use the counterexample cited in the remark, due to Nishimura and generalized by
-- Dumitrescu. It gives a `G`-ring `R` together with an ideal `I ⊆ R` whose `I`-adic completion is
-- not again a `G`-ring.
/-- Companion existential counterexample form of Remark 15.50.11. -/
theorem exists_gRing_ideal_with_adicCompletion_not_gRing :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      IsGRing R ∧ ¬ IsGRing (AdicCompletion I R) := sorry

/-- Remark 15.50.11: adic completion does not preserve the `G`-ring property in general. -/
theorem adicCompletion_not_preserves_isGRing :
    ¬ ∀ (R : Type u) (_ : CommRing R) (I : Ideal R), IsGRing R → IsGRing (AdicCompletion I R) := by
  intro h
  obtain ⟨R, hR, I, hGR, hnotGR⟩ := exists_gRing_ideal_with_adicCompletion_not_gRing
  exact hnotGR (h R hR I hGR)

end
