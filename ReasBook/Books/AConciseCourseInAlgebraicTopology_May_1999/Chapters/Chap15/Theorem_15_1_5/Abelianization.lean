import Mathlib.GroupTheory.Abelianization.Defs
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Definition_15_1_1

open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

local notation "BasedSpace" => CategoryTheory.Under (⊤_ TopCat)

section

variable {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)

/-- The degree-`1` Hurewicz homomorphism factors canonically through the abelianization of
`π_ 1(X)` because its target is an additive commutative group. -/
noncomputable abbrev degreeOneAbelianizedHurewiczHomomorphism
    (X : BasedSpace) [HasHurewiczComparison 1 X] (i₁ : SphereHomologyGenerator H 1) :
    Additive (Abelianization (π_ 1 X.right (underTopBasepoint X))) →+
      basedReducedHomology H (1 : ℤ) X :=
  (Abelianization.lift ((hurewiczHomomorphism H 1 X i₁).toMultiplicativeRight)).toAdditive

/-- Composing the canonical abelianized degree-`1` Hurewicz map with `Abelianization.of` recovers
the original Hurewicz homomorphism. -/
theorem degreeOneAbelianizedHurewiczHomomorphism_comp_abelianizationOf
    (X : BasedSpace) [HasHurewiczComparison 1 X] (i₁ : SphereHomologyGenerator H 1) :
    (degreeOneAbelianizedHurewiczHomomorphism H X i₁).comp
        ((Abelianization.of :
            π_ 1 X.right (underTopBasepoint X) →*
              Abelianization (π_ 1 X.right (underTopBasepoint X))).toAdditive) =
      hurewiczHomomorphism H 1 X i₁ := by
  ext a
  change Additive.ofMul
      ((Abelianization.lift ((hurewiczHomomorphism H 1 X i₁).toMultiplicativeRight))
        (Abelianization.of (Additive.toMul a))) = _
  rw [Abelianization.lift_apply_of]
  rfl

end
