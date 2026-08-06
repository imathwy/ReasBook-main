import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.ContinuousMap.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.ClosedUnitDisk
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_5_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Path.Homotopic.Quotient
open scoped ClosedUnitDisk
open scoped ContinuousMap

/-- Every point of `Circle` lies in the closed unit disk of `ℂ`. -/
-- Proof sketch: rewrite membership in `D²` as the norm bound `‖z‖ ≤ 1`, then use
-- `Circle.norm_coe z = 1`.
theorem circle_mem_closed_unit_disk (z : Circle) :
    (z : ℂ) ∈ D² := by
  simp [Circle.norm_coe z]

/-- The boundary inclusion of the unit circle into the closed unit disk. -/
def circleBoundaryInclusion : C(Circle, D²) where
  toFun z := ⟨z, circle_mem_closed_unit_disk z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk circle_mem_closed_unit_disk

@[simp] theorem circleBoundaryInclusion_apply (z : Circle) :
    ((circleBoundaryInclusion z : D²) : ℂ) = z :=
  rfl

/-- Helper for Proposition 1.6.2: a retraction of the disk onto the boundary fixes the chosen
basepoint `1 ∈ S¹`. -/
-- Evaluate the retraction identity at the basepoint to align the induced map on `π₁` with the
-- usual basepoint `1 : Circle`.
private theorem retraction_basepoint_eq_one (r : C(D², Circle))
    (hret : r.comp circleBoundaryInclusion = ContinuousMap.id Circle) :
    r (circleBoundaryInclusion 1) = 1 := by
  have happly := congrArg (fun f : C(Circle, Circle) ↦ f 1) hret
  simpa using happly

/-- Helper for Proposition 1.6.2: the induced map of a retraction is a left inverse to the map
induced by the boundary inclusion. -/
-- Functoriality identifies the induced map of `r ∘ i` with the composite `r_* ∘ i_*`, and the
-- retraction hypothesis turns that composite into the identity on `π₁(S¹, 1)`.
private theorem retraction_induced_map_left_inverse (r : C(D², Circle))
    (hbase : r (circleBoundaryInclusion 1) = 1)
    (hret : r.comp circleBoundaryInclusion = ContinuousMap.id Circle) :
    (FundamentalGroup.mapOfEq r hbase).comp
        (FundamentalGroup.map circleBoundaryInclusion 1) =
      MonoidHom.id (FundamentalGroup Circle 1) := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro p
  change FundamentalGroup.mapOfEq r hbase
      (FundamentalGroup.fromPath (.mk (p.map circleBoundaryInclusion.continuous))) =
    FundamentalGroup.fromPath (.mk p)
  rw [FundamentalGroup.mapOfEq_apply]
  -- Evaluate the transported composite on a representative loop and collapse it using `r ∘ i = id`.
  have hpath :
      (p.map (r.comp circleBoundaryInclusion).continuous).cast hbase.symm hbase.symm = p := by
    apply Path.ext
    funext t
    change (r.comp circleBoundaryInclusion) (p t) = p t
    exact congrFun (congrArg DFunLike.coe hret) (p t)
  exact congrArg FundamentalGroup.fromPath (congrArg mk hpath)

/-- Helper for Proposition 1.6.2: any hypothetical retraction would force the fundamental group of
the circle at `1` to be trivial. -/
-- The composite `r_* ∘ i_*` is the identity, but `i_*` factors through the trivial fundamental
-- group of the disk, so every element of `π₁(S¹, 1)` must coincide.
theorem circle_fundamental_group_subsingleton_of_retraction (r : C(D², Circle))
    (hret : r.comp circleBoundaryInclusion = ContinuousMap.id Circle) :
    Subsingleton (FundamentalGroup Circle 1) := by
  have hbase : r (circleBoundaryInclusion 1) = 1 :=
    retraction_basepoint_eq_one r hret
  refine ⟨fun γ δ ↦ ?_⟩
  calc
    γ = ((FundamentalGroup.mapOfEq r hbase).comp
          (FundamentalGroup.map circleBoundaryInclusion 1)) γ := by
            simp [retraction_induced_map_left_inverse r hbase hret]
    _ = ((FundamentalGroup.mapOfEq r hbase).comp
          (FundamentalGroup.map circleBoundaryInclusion 1)) δ := by
            apply congrArg (FundamentalGroup.mapOfEq r hbase)
            exact Subsingleton.elim _ _
    _ = δ := by
            simp [retraction_induced_map_left_inverse r hbase hret]

/-- Proposition 1.6.2: there is no continuous retraction from the closed unit disk `D²` onto its
boundary circle `S¹`; equivalently, no continuous map `r : D² → S¹` restricts to the identity on
the boundary inclusion `S¹ ↪ D²`. -/
-- Proof sketch: if such an `r` existed, then functoriality of `FundamentalGroup.map` would make
-- the identity map on `π₁(S¹, 1)` factor through `π₁(D², 1)`. By
-- `fundamental_group_map_comp` and `fundamental_group_map_id`, the induced map of the boundary
-- inclusion would then be injective. Lemma 1.6.1 makes `π₁(D², circleBoundaryInclusion 1)`
-- subsingleton, while Theorem 1.5.11 supplies that `π₁(S¹, 1)` is infinite, hence nontrivial.
theorem no_continuous_retraction_closed_unit_disk_to_circle :
    ¬ ∃ r : C(D², Circle), r.comp circleBoundaryInclusion = ContinuousMap.id Circle := by
  rintro ⟨r, hret⟩
  have _ : Subsingleton (FundamentalGroup Circle 1) :=
    circle_fundamental_group_subsingleton_of_retraction r hret
  -- The circle has infinite fundamental group, so it cannot simultaneously be subsingleton.
  have _ : Nontrivial (FundamentalGroup Circle 1) := inferInstance
  exact false_of_nontrivial_of_subsingleton (FundamentalGroup Circle 1)
