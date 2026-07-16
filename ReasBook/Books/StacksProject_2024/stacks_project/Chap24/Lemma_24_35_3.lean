import Mathlib.Algebra.Category.ModuleCat.AB
import StacksProject_2024.stacks_project.Chap24.Lemma_24_35_2

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uR uM

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type uR} [Ring R]
variable {MObj : Type uM}

local notation "DMod" => DerivedCategory (ModuleCat R)

-- Semantic recall note: `lean_leansearch` returned only generic derived-limit/isomorphism hits,
-- so the owner choice was checked against the local dependency `Lemma_24_35_2`, whose
-- `IsIsomorphic` comparison for pro-isomorphic tensor towers is the exact categorical surface
-- needed here.

/-- Lemma 24.35.3: let `K_n` be the powered Koszul differential graded `R`-algebras and let
`(M_n)` be an object of `D(\mathbf N, (K_n))`. For every `t ≥ 1`, if
`tensorOverR M t ht` models the inverse system `(M_n \otimes_R^{\mathbf L} K_t)_n`,
`tensorOverKn M t ht` models `(M_n \otimes_{K_n}^{\mathbf L} K_t)_n`, and these two towers are
pro-isomorphic, then their chosen derived inverse limits are isomorphic in `D(R)`. -/
theorem koszulTensorDerivedLimit_isIsomorphic_of_proIsomorphism
    (tensorOverR tensorOverKn : MObj → (t : ℕ) → 1 ≤ t → ℕᵒᵖ ⥤ DMod)
    (derivedLimitOverR derivedLimitOverKn : MObj → (t : ℕ) → 1 ≤ t → DMod)
    (hlimOverR :
      ∀ (M : MObj) (t : ℕ) (ht : 1 ≤ t),
        IsDerivedLimit (tensorOverR M t ht) (derivedLimitOverR M t ht))
    (hlimOverKn :
      ∀ (M : MObj) (t : ℕ) (ht : 1 ≤ t),
        IsDerivedLimit (tensorOverKn M t ht) (derivedLimitOverKn M t ht))
    {M : MObj} {t : ℕ} (ht : 1 ≤ t)
    (η :
      colimit (((tensorOverKn M t ht).op) ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor (tensorOverR M t ht) ⋙ uliftFunctor.{0})
    [IsIso η] :
    IsIsomorphic (derivedLimitOverR M t ht) (derivedLimitOverKn M t ht) := sorry

end

end CategoryTheory
