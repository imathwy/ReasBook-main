import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced the basic-open cover theorem
-- `PrimeSpectrum.iSup_basicOpen_eq_top_iff` and the dense-range kernel criterion. Local Chapter 29
-- precedent confirms `schemeTheoreticClosure` and `schemeTheoreticallyDense` as the project owners.
-- The Stacks tag evidence is consistent: item tag `056C` matches the source URL `/tag/056C`.

variable {A : Type u} [CommRing A]

/-- The finite union of principal open subsets `D(f_i)` in `Spec(A)`. -/
@[stacks 056C]
abbrev affineBasicOpenUnion (n : ℕ) (f : Fin n → A) : (Spec (CommRingCat.of A)).Opens :=
  ⨆ i : Fin n, PrimeSpectrum.basicOpen (f i)

/-- The canonical map from `A` to the product of the principal localizations `A_{f_i}`. -/
@[stacks 056C]
def awayLocalizationProductMap (n : ℕ) (f : Fin n → A) :
    A →+* (∀ i : Fin n, Localization.Away (f i)) :=
  Pi.ringHom (fun i : Fin n ↦ algebraMap A (Localization.Away (f i)))

/-- The kernel ideal of the map from `A` to the product of the localizations `A_{f_i}`. -/
@[stacks 056C]
abbrev affineBasicOpenUnionClosureIdeal (n : ℕ) (f : Fin n → A) : Ideal A :=
  RingHom.ker (awayLocalizationProductMap n f)

/-- Example 29.7.4 (1): for `U = ⋃ᵢ D(f_i) ⊆ Spec(A)` and
`I = ker(A → ∏ᵢ A_{f_i})`, the scheme-theoretic closure of `U` in `Spec(A)` is
`Spec(A / I)`. -/
@[stacks 056C]
theorem schemeTheoreticClosure_affineBasicOpenUnion_eq_spec_quotient
    (n : ℕ) (f : Fin n → A) :
    schemeTheoreticClosure (affineBasicOpenUnion n f) =
      Spec (CommRingCat.of (A ⧸ affineBasicOpenUnionClosureIdeal n f)) := sorry

/-- Example 29.7.4 (2): the open immersion `U = ⋃ᵢ D(f_i) ⟶ Spec(A)` is quasi-compact. -/
@[stacks 056C]
theorem quasiCompact_affineBasicOpenUnion_ι (n : ℕ) (f : Fin n → A) :
    QuasiCompact (affineBasicOpenUnion n f).ι := sorry

/-- Example 29.7.4 (3): for `U = ⋃ᵢ D(f_i) ⊆ Spec(A)` and
`I = ker(A → ∏ᵢ A_{f_i})`, the open subscheme `U` is scheme-theoretically dense in
`Spec(A)` if and only if `I = 0`. -/
@[stacks 056C]
theorem schemeTheoreticallyDense_affineBasicOpenUnion_iff_closureIdeal_eq_bot
    (n : ℕ) (f : Fin n → A) :
    schemeTheoreticallyDense (affineBasicOpenUnion n f) ↔
      affineBasicOpenUnionClosureIdeal n f = ⊥ := sorry

end

end AlgebraicGeometry
