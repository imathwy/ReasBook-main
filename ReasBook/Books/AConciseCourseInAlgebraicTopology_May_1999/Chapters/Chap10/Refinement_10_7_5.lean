import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_4

open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: no built-in owner surfaced for the source's
-- refinement of a CW-triad approximation by vanishing low-dimensional relative cells.
-- Local Chapter 10 precedent already uses the triad owners `Triad.leftIntersectionSubspace` and
-- `Triad.rightIntersectionSubspace` for the pairs `(A, C)` and `(B, C)` with `C = A ∩ B`,
-- `CWTriad` for chosen CW-triad data, and the bridge `Topology.RelCWComplex.NoCellsLEOf` for
-- exporting a chosen relative CW structure together with its low-cell vanishing clause.

/-- Refinement 10.7.5 (1): if `(X; A, B)` is an excisive triad and the pair `(A, C)` with
`C = A ∩ B`, viewed on the subtype ambient `A` as `T.leftIntersectionSubspace`, is
`n`-connected, then
the CW-triad approximation from Theorem 10.7.4 can be chosen so that the corresponding relative
CW approximation of `ΓA` over `ΓC = ΓA ∩ ΓB` has no relative `q`-cells for `q ≤ n`. The chosen
relative structure is recorded explicitly on the carrier `ΓT.subcomplexA`, with base
`ΓT.intersection`. -/
theorem exists_cwTriadApproximation_noCellsLE_subcomplexA
    (X : TopCat.{u}) (T : Triad X) (hT : T.IsExcisive) (n : ℕ)
    [NConnectedPair n T.leftIntersectionSubspace] :
    ∃ (ΓX : TopCat.{u}) (ΓT : CWTriad ΓX) (γX : C(ΓX, X)) (hMap : ΓT.IsMap T γX),
      IsCWTriadApproximation ΓT T γX hMap ∧
        ∃ h_relA : Topology.RelCWComplex ΓT.subcomplexA ΓT.intersection,
          h_relA.NoCellsLEOf n := sorry

/-- Refinement 10.7.5 (2): if `(X; A, B)` is an excisive triad and the pair `(B, C)` with
`C = A ∩ B`, viewed on the subtype ambient `B` as `T.rightIntersectionSubspace`, is
`n`-connected, then
the CW-triad approximation from Theorem 10.7.4 can be chosen so that the corresponding relative
CW approximation of `ΓB` over `ΓC = ΓA ∩ ΓB` has no relative `q`-cells for `q ≤ n`. The chosen
relative structure is recorded explicitly on the carrier `ΓT.subcomplexB`, with base
`ΓT.intersection`. -/
theorem exists_cwTriadApproximation_noCellsLE_subcomplexB
    (X : TopCat.{u}) (T : Triad X) (hT : T.IsExcisive) (n : ℕ)
    [NConnectedPair n T.rightIntersectionSubspace] :
    ∃ (ΓX : TopCat.{u}) (ΓT : CWTriad ΓX) (γX : C(ΓX, X)) (hMap : ΓT.IsMap T γX),
      IsCWTriadApproximation ΓT T γX hMap ∧
        ∃ h_relB : Topology.RelCWComplex ΓT.subcomplexB ΓT.intersection,
          h_relB.NoCellsLEOf n := sorry
