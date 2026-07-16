import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Descent
import StacksProject_2024.stacks_project.Chap04.Lemma_4_43_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_127_3
import StacksProject_2024.stacks_project.Chap15.«15_74_0_2»

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-
Domain-style sampling for Lemma 15.127.4:
- primary domain: invertible objects in the monoidal derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.tensorLeft_isEquivalence_iff_exists_tensor_inverse`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.exactPairing_isPerfect`,
  `CategoryTheory.ringSingle`,
  `CategoryTheory.derivedTensorWithAlgebra`;
- best owner abstraction:
  `source-facing`: the local criterion that an invertible object of `D(R)` becomes a shifted copy
    of the localized unit after derived base change to some `Localization.Away f`;
  `core/canonical`: the chapter owner `DerivedCategory.IsPerfect` for perfectness and the monoidal
    owner `ExactPairing N M` for left-dual data;
  `bridge/view`: chosen tensor-inverse data extracted from `(tensorLeft M).IsEquivalence`, used
    only internally to build an exact pairing and invoke `exactPairing_isPerfect`, together with
    the chapter notation `M ⊗[R]^L[Localization.Away f]` for derived localization.

Primitive data are only the invertibility witness `(tensorLeft M).IsEquivalence`, the localized
derived tensor product, and the shifted localized unit `ringSingleAway[f]⟦-n⟧`. The perfectness
conclusion is derived API via the existing chapter owner `exactPairing_isPerfect`, so this file
should keep only the source-facing local criterion and that thin canonical corollary.
-/

local notation "DModAway[" f "]" => DerivedCategory (ModuleCat (Localization.Away f))
local notation "ringSingleAway[" f "]" => (ringSingle : DModAway[f])

-- Proof sketch: for the forward implication, tensoring with the inverse of an invertible object
-- shows that after localization at every prime, the base change of `M` is still invertible over
-- the localized ring; over a local ring an invertible perfect object is a single shift of the
-- unit. For the reverse implication, apply the local criterion prime-by-prime to the evaluation
-- map from the derived dual tensor `M`, and conclude that it is an isomorphism globally because
-- isomorphisms in `D(R)` can be checked after localization.
/-- Lemma 15.127.4: an object `M` of `D(R)` is invertible if and only if for every prime ideal
`𝔭 ⊂ R` there exists an element `f ∉ 𝔭` such that the derived localization `M_f` is isomorphic to
`R_f[-n]` for some integer `n`. -/
theorem isInvertibleObject_iff_locally_isomorphic_to_shifted_localized_ring
    (M : DMod) :
    (tensorLeft M).IsEquivalence ↔
      ∀ p : PrimeSpectrum R,
        ∃ f : R, f ∉ p.asIdeal ∧ ∃ n : ℤ,
          IsIsomorphic (M ⊗[R]^L[Localization.Away f]) (ringSingleAway[f]⟦-n⟧) := sorry

/-
Proof sketch: once `M` is invertible, choose a tensor inverse `N` using
`tensorLeft_isEquivalence_iff_exists_tensor_inverse`. The isomorphisms `M ⊗ N ≅ 𝟙` and
`N ⊗ M ≅ 𝟙` provide an exact pairing `ExactPairing N M`, so the perfectness conclusion is the
canonical Chapter 15 consequence `exactPairing_isPerfect`.
-/
/-- An invertible object of `D(R)` is perfect. -/
theorem isPerfect_of_isInvertibleObject
    {M : DMod} (hM : (tensorLeft M).IsEquivalence) :
    M.IsPerfect := by
  rcases (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).1 hM with
    ⟨N, ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  have hpair : ExactPairing N M := by
    letI : ExactPairing M N :=
      { coevaluation' := e₁.inv
        evaluation' := e₂.hom
        coevaluation_evaluation' := by
          sorry
        evaluation_coevaluation' := by
          sorry }
    exact BraidedCategory.exactPairing_swap M N
  simpa using exactPairing_isPerfect hpair

end

end CategoryTheory
