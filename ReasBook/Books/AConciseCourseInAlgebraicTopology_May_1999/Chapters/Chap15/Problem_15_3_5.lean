import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_5_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.KPiOne
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_4

-- Semantic recall: Chapter 15 already packages `K(π, 1)` and `K(π, n + 1)` by the canonical
-- source-facing owners `IsKPiOne` and `IsKPiSucc`. This item records the familiar models as
-- instances of those owners, reusing the homotopy-group calculations already established for
-- `Circle`, `RealProjectiveInfinity`, and `ComplexProjectiveInfinity`.

/-- Problem 15.3.5: `Circle` is the standard `K(ℤ, 1)` model. -/
instance circle_isKPiOne : IsKPiOne (Multiplicative ℤ) (TopCat.of Circle) (1 : Circle) where
  toConnectedSpace := by
    sorry
  cwComplex := by
    sorry
  pi1Iso := by
    refine ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup (1 : Circle)).trans ?_⟩
    exact circleFundamentalGroupMulEquivInt.symm
  higherHomotopySubsingleton := by
    intro n hn
    sorry

/-- Problem 15.3.5: `RealProjectiveInfinity` is the standard `K(ZMod 2, 1)` model. -/
instance realProjectiveInfinity_isKPiOne :
    IsKPiOne (Multiplicative (ZMod 2)) (TopCat.of RealProjectiveInfinity)
      realProjectiveInfinityBasepoint where
  toConnectedSpace := by
    sorry
  cwComplex := by
    sorry
  pi1Iso := realProjectiveInfinity_pi1_mulEquiv_zmod_two
  higherHomotopySubsingleton := by
    intro n hn
    exact realProjectiveInfinity_homotopyGroup_subsingleton hn realProjectiveInfinityBasepoint

/-- Problem 15.3.5: `ComplexProjectiveInfinity` is the standard `K(ℤ, 2)` model. -/
instance complexProjectiveInfinity_isKPiSucc :
    IsKPiSucc (Multiplicative ℤ) 1 (TopCat.of ComplexProjectiveInfinity)
      complexProjectiveInfinityBasepoint where
  toConnectedSpace := by
    sorry
  cwComplex := by
    sorry
  homotopyGroupIso := complexProjectiveInfinity_pi2_mulEquiv_int
  otherHomotopySubsingleton := by
    intro m hm
    sorry
