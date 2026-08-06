import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Proposition_1_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap CircleDegree FundamentalGroup

/-- Lemma 1.7.2: the degree of a self-map of `S¹` is unchanged under homotopy through maps
`S¹ → S¹`. -/
-- Proof sketch: choose a representative homotopy `H : f.Homotopy g`, apply
-- `fundamental_group_map_homotopy_commutes_apply` at the basepoint `1 : Circle`, and compare
-- the two
-- resulting loop classes after transporting both to the basepoint `1`. The source-facing bridge
-- `circleDegree_spec` identifies each transported class with the standard loop class of the
-- corresponding degree.
theorem circleDegree_eq_of_homotopic
    (f g : C(Circle, Circle)) (h : f.Homotopic g) :
    deg(f) = deg(g) := by
  obtain ⟨H⟩ := h
  let a : Path (g 1) (1 : Circle) := circlePathToOne (g 1)
  let ι : FundamentalGroup Circle (1 : Circle) := standardLoopClass 1
  have hmap :
      γ[H.evalAt 1] (FundamentalGroup.map f (1 : Circle) ι) =
        FundamentalGroup.map g (1 : Circle) ι := by
    exact fundamental_group_map_homotopy_commutes_apply f g H (1 : Circle) ι
  calc
    deg(f) = circleFundamentalGroupLiftIndex (standardLoopClass (deg(f))) := by
      symm
      exact circleFundamentalGroupLiftIndex_standardLoop (deg(f))
    _ = circleFundamentalGroupLiftIndex
        (γ[(H.evalAt 1).trans a] (FundamentalGroup.map f (1 : Circle) ι)) := by
          exact congrArg circleFundamentalGroupLiftIndex
            (circleDegree_spec f ((H.evalAt 1).trans a)).symm
    _ = circleFundamentalGroupLiftIndex
        (γ[a] (γ[H.evalAt 1] (FundamentalGroup.map f (1 : Circle) ι))) := by
          congr 1
          simpa using
            fundamentalGroupMulEquivOfPath_trans_apply
              (H.evalAt 1) a (FundamentalGroup.map f (1 : Circle) ι)
    _ = circleFundamentalGroupLiftIndex (γ[a] (FundamentalGroup.map g (1 : Circle) ι)) := by
          exact congrArg circleFundamentalGroupLiftIndex (congrArg (γ[a]) hmap)
    _ = circleFundamentalGroupLiftIndex (standardLoopClass (deg(g))) := by
          exact congrArg circleFundamentalGroupLiftIndex (circleDegree_spec g a)
    _ = deg(g) := by
      simpa using circleFundamentalGroupLiftIndex_standardLoop (deg(g))
