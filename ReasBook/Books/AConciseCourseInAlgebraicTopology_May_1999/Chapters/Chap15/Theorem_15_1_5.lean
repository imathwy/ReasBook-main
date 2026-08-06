import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_4.PositiveDegree
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Theorem_15_1_5.Abelianization

open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

local notation "BasedSpace" => CategoryTheory.Under (⊤_ TopCat)

-- The item-local foundations already own the reusable positive-degree wrappers and the canonical
-- degree-`1` factorization through `Abelianization`, so this file keeps only the source-facing
-- connectedness consequences.

section

variable {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)

/-- Theorem 15.1.5 (1): if `X.right` is `0`-connected, then the Chapter 15 degree-`1` Hurewicz
homomorphism is the abelianization map: it factors through `Abelianization.of`, and the induced
map from `Additive (Abelianization (π_ 1(X)))` to `H̃_1(X)` is bijective. -/
theorem hurewiczHomomorphism_degreeOne_isAbelianization_of_zeroConnected
    (X : BasedSpace)
    [NConnectedSpace 0 X.right] [HasHurewiczComparison 1 X]
    (i₁ : SphereHomologyGenerator H 1) :
    hurewiczHomomorphism H 1 X i₁ =
        (degreeOneAbelianizedHurewiczHomomorphism H X i₁).comp
          ((Abelianization.of :
              π_ 1 X.right (underTopBasepoint X) →*
                Abelianization
                  (π_ 1 X.right (underTopBasepoint X))).toAdditive) ∧
      Function.Bijective (degreeOneAbelianizedHurewiczHomomorphism H X i₁) := sorry

/-- The additive equivalence form of Theorem 15.1.5 (1). -/
theorem hurewiczHomomorphism_degreeOne_addEquiv_of_zeroConnected
    (X : BasedSpace)
    [NConnectedSpace 0 X.right] [HasHurewiczComparison 1 X]
    (i₁ : SphereHomologyGenerator H 1) :
    ∃ e :
      Additive
          (Abelianization
            (π_ 1 X.right
              (underTopBasepoint X))) ≃+
        basedReducedHomology H (1 : ℤ) X,
      degreeOneAbelianizedHurewiczHomomorphism H X i₁ = e.toAddMonoidHom := by
  refine ⟨AddEquiv.ofBijective (degreeOneAbelianizedHurewiczHomomorphism H X i₁)
    (hurewiczHomomorphism_degreeOne_isAbelianization_of_zeroConnected H X i₁).2, rfl⟩

/-- Theorem 15.1.5 (2): if `1 < n` and `X.right` is `(n - 1)`-connected, then the Chapter 15
Hurewicz homomorphism `π_ n(X) → H̃_n(X)` is an isomorphism, expressed directly as bijectivity of
the canonical positive-degree homomorphism. -/
theorem hurewiczHomomorphism_isIso_of_nConnected
    (n : ℕ) (h_n : 1 < n) (X : BasedSpace)
    [NConnectedSpace (n - 1) X.right] [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n) :
    Function.Bijective
      (positiveDegreeHurewiczHomomorphismAtBasedSpace H n h_n X i_n) := sorry

/-- The additive equivalence form of Theorem 15.1.5 (2). -/
theorem hurewiczHomomorphism_addEquiv_of_nConnected
    (n : ℕ) (h_n : 1 < n) (X : BasedSpace)
    [NConnectedSpace (n - 1) X.right] [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n) :
    ∃ e :
      positiveDegreeAdditiveHomotopyGroup n h_n X ≃+
        basedReducedHomology H (n : ℤ) X,
      positiveDegreeHurewiczHomomorphismAtBasedSpace H n h_n X i_n =
        e.toAddMonoidHom := by
  refine ⟨AddEquiv.ofBijective
    (positiveDegreeHurewiczHomomorphismAtBasedSpace H n h_n X i_n)
    (hurewiczHomomorphism_isIso_of_nConnected H n h_n X i_n), rfl⟩

end
