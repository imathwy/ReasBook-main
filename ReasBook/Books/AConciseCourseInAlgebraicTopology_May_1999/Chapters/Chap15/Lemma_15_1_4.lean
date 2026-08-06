import Mathlib.GroupTheory.Abelianization.Defs
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_4.PositiveDegree
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_4.Wedge

open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

-- Chapter 13 already owns the canonical pointed wedge `wedgeOfNSpheres`, and the item-local
-- positive-degree foundation now owns the generic wrappers that expose the hypothesis `1 < n`
-- while internalizing the resulting `[Nonempty (Fin n)]`.
-- This file therefore keeps only the source-facing Hurewicz statements for the Chapter 15 wedge
-- model `basedWedgeOfNSpheres`.

section

variable {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)

/-- Lemma 15.1.4 (1). For a wedge of `1`-spheres, the Hurewicz homomorphism
`π_ 1(X) → H̃_1(X)` is the abelianization map. Equivalently, for
`X = basedWedgeOfNSpheres 1 ι`, the canonical Hurewicz homomorphism factors through
`Abelianization.of` and becomes an additive equivalence after that factorization. -/
theorem hurewiczHomomorphism_wedgeOfOneSpheres_isAbelianization
    (ι : Type u) [HasHurewiczComparison 1 (basedWedgeOfNSpheres 1 ι)]
    (i₁ : SphereHomologyGenerator H 1) :
    ∃ e :
      Additive
          (Abelianization
            (π_ 1 (basedWedgeOfNSpheres 1 ι).right
              (underTopBasepoint (basedWedgeOfNSpheres 1 ι)))) ≃+
        basedReducedHomology H (1 : ℤ) (basedWedgeOfNSpheres 1 ι),
      hurewiczHomomorphism H 1 (basedWedgeOfNSpheres 1 ι) i₁ =
        e.toAddMonoidHom.comp
          ((Abelianization.of :
              π_ 1 (basedWedgeOfNSpheres 1 ι).right
                  (underTopBasepoint (basedWedgeOfNSpheres 1 ι)) →*
                Abelianization
                  (π_ 1 (basedWedgeOfNSpheres 1 ι).right
                    (underTopBasepoint (basedWedgeOfNSpheres 1 ι)))).toAdditive) := sorry

/-- Lemma 15.1.4 (2). For a wedge of `n`-spheres with `n > 1`, the Hurewicz homomorphism
`π_ n(X) → H̃_n(X)` is an isomorphism. Equivalently, for `X = basedWedgeOfNSpheres n ι` and
`1 < n`, the canonical Hurewicz homomorphism, packaged through
`positiveDegreeHurewiczHomomorphismAtBasedSpace` with explicit positive-degree witness `h_n`, is
the additive homomorphism underlying an additive equivalence. -/
theorem hurewiczHomomorphism_wedgeOfNSpheres_isIso
    (n : ℕ) (h_n : 1 < n) (ι : Type u)
    [HasHurewiczComparison n (basedWedgeOfNSpheres n ι)]
    (i_n : SphereHomologyGenerator H n) :
    ∃ e :
      positiveDegreeAdditiveHomotopyGroup n h_n (basedWedgeOfNSpheres n ι) ≃+
        basedReducedHomology H (n : ℤ) (basedWedgeOfNSpheres n ι),
      positiveDegreeHurewiczHomomorphismAtBasedSpace
          H n h_n (basedWedgeOfNSpheres n ι) i_n =
        e.toAddMonoidHom := sorry

end
