import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced affine basic opens via
-- `instIsAffineHomιBasicOpen`; the source's `X_s` is stated by its explicit nonvanishing-locus
-- formula to avoid depending on currently noncompiling Chapter 17 owner files.

/-- Lemma 29.11.11: let `X` be a scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, and let `s ∈ Γ(X, \mathcal L)`. If `U` is the open subset
`X_s` where the germ of `s` does not vanish, then the inclusion `U ⟶ X` is an
affine morphism. -/
@[stacks 01SF]
theorem isAffineHom_ι_of_eq_sectionNonvanishingLocus
    (X : Scheme.{u}) [MonoidalCategory X.toRingedSpace.Modules]
    (ℒ : X.toRingedSpace.Modules) [Functor.IsEquivalence (tensorRight ℒ)]
    (s : ℒ.sections) (U : X.Opens)
    (hU : (U : Set X) =
      {x | TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤)) ∉
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat ℒ x)))}) :
    IsAffineHom U.ι := sorry

end AlgebraicGeometry
