import StacksProject_2024.Chap28.Lemma_28_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme} [MonoidalCategory X.Modules]

/-- The monoidal structure on scheme modules, viewed as the corresponding monoidal structure on
modules over the underlying ringed space. -/
local instance instMonoidalCategoryRingedSpaceModulesForLemma32116 :
    MonoidalCategory (SheafOfModules X.toRingedSpace.ringCatSheaf) :=
  inferInstanceAs (MonoidalCategory X.Modules)

/- Semantic recall: `lean_leansearch` surfaced the canonical affine basic-open API. Local
Chapter 28 precedent for Lemma 28.29.6 expands the unavailable packaged ampleness owner into
`Functor.IsEquivalence (tensorRight L)`, compactness of `X`, and affine nonvanishing
neighborhoods for the tensor powers `RingedSpace.tensorPowerSheaf L n`; the source-facing open
`X_s` is represented by `tensorPowerSectionNonvanishingSet`. The Stacks tag evidence is
consistent: item tag `0E21` agrees with the source URL ending in `/tag/0E21`. -/

/-- Lemma 32.11.6: let `X` be a scheme and let `L` be an ample invertible
`\mathcal O_X`-module, expressed through the expanded Chapter 28 ampleness interface. Given an
open `W ⊆ X`, a field `k`, an integral `k`-algebra `A`, and a morphism `Spec(A) ⟶ W`, there is
a positive tensor power and a global section `s` such that the nonvanishing open `X_s` is affine,
lies in `W`, and the morphism from `Spec(A)` factors through `X_s`. The morphism
`Spec(A) ⟶ Spec(k)` is the canonical one induced by the `k`-algebra structure on `A`. -/
@[stacks 0E21]
theorem exists_positive_tensorPow_section_affine_nonvanishingOpen_subset_open_and_factor
    (L : X.Modules) [Functor.IsEquivalence (tensorRight L)]
    (hX_compact : IsCompact (Set.univ : Set X))
    (hL_ample : ∀ x : X, ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
        ∃ U : X.Opens, TensorPowerSectionAffineNonvanishingAt L n s U x)
    (W : X.Opens)
    (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (toW : Spec (CommRingCat.of A) ⟶ W.toScheme) :
    ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
        ∃ U : X.Opens,
          ∃ hU_set : (U : Set X) = tensorPowerSectionNonvanishingSet L n s,
            ∃ hU_affine : IsAffineOpen U,
              ∃ hsub : U ≤ W,
                ∃ lift : Spec (CommRingCat.of A) ⟶ U.toScheme,
                  lift ≫ X.homOfLE hsub = toW := sorry

end AlgebraicGeometry.Scheme.Modules
