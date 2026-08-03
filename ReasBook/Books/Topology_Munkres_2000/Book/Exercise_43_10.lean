module

public import Topology_Munkres_2000.Book.Definition_43_5.Closure

open Set

public section

namespace Isometry

universe u v w

variable {X : Type u} {Y : Type v} {Y' : Type w}
variable [MetricSpace X] [MetricSpace Y] [MetricSpace Y']
variable {h : X → Y} {h' : X → Y'}

/-- Helper for Exercise 43.10: the canonical uniform equivalence between two closure
completions, viewed as an equivalence of their underlying spaces. -/
noncomputable def closureRangeCoreEquiv [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') : closure (range h) ≃ closure (range h') :=
  -- `mapEquiv` requires the source package's stored uniform structure.
  -- Local instance justification (defeq pin): it is definitionally the metric subtype structure.
  letI : UniformSpace hh.abstractCompletion.space := hh.abstractCompletion.uniformStruct
  -- `mapEquiv` requires the target package's stored uniform structure.
  -- Local instance justification (defeq pin): it is definitionally the metric subtype structure.
  letI : UniformSpace hh'.abstractCompletion.space := hh'.abstractCompletion.uniformStruct
  (hh.abstractCompletion.mapEquiv hh'.abstractCompletion (UniformEquiv.refl X)).toEquiv

/-- Helper for Exercise 43.10: the canonical comparison between closure completions is
continuous. -/
theorem closureRangeCoreEquiv_continuous [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') : Continuous (hh.closureRangeCoreEquiv hh') := by
  -- Pin the stored structures and use continuity of the uniform equivalence.
  letI : UniformSpace hh.abstractCompletion.space := hh.abstractCompletion.uniformStruct
  letI : UniformSpace hh'.abstractCompletion.space := hh'.abstractCompletion.uniformStruct
  exact (hh.abstractCompletion.mapEquiv hh'.abstractCompletion (UniformEquiv.refl X)).continuous

/-- Helper for Exercise 43.10: the canonical comparison agrees with the two closure-valued
embeddings. -/
theorem closureRangeCoreEquiv_apply [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') (x : X) :
    hh.closureRangeCoreEquiv hh' (hh.toClosure x) = hh'.toClosure x := by
  -- Pin the stored structures and invoke the comparison map's computation rule.
  letI : UniformSpace hh.abstractCompletion.space := hh.abstractCompletion.uniformStruct
  letI : UniformSpace hh'.abstractCompletion.space := hh'.abstractCompletion.uniformStruct
  exact hh.abstractCompletion.mapEquiv_coe hh'.abstractCompletion (UniformEquiv.refl X) x

/-- Helper for Exercise 43.10: the canonical comparison of two closure completions preserves
distance. -/
theorem closureRangeCoreEquiv_isometry [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') : Isometry (hh.closureRangeCoreEquiv hh') := by
  -- Distance preservation is closed in both variables, so extend it from the dense embeddings.
  apply Isometry.of_dist_eq
  intro x y
  refine hh.denseRange_toClosure.induction_on x ?_ ?_
  · exact isClosed_eq ((hh.closureRangeCoreEquiv_continuous hh').dist continuous_const)
      (continuous_id.dist continuous_const)
  · intro a
    refine hh.denseRange_toClosure.induction_on y ?_ ?_
    · exact isClosed_eq (continuous_const.dist (hh.closureRangeCoreEquiv_continuous hh'))
        (continuous_const.dist continuous_id)
    · intro b
      rw [hh.closureRangeCoreEquiv_apply hh' a, hh.closureRangeCoreEquiv_apply hh' b]
      exact (hh'.toClosure_isometry.dist_eq a b).trans
        (hh.toClosure_isometry.dist_eq a b).symm

/-- Exercise 43.10 (uniqueness of completion): the canonical isometric equivalence between
the closures realizing two completions of the same metric space. -/
noncomputable def closureRangeEquiv [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') : closure (range h) ≃ᵢ closure (range h') :=
  -- Assemble the isometric equivalence from the stable comparison interface above.
  { toEquiv := hh.closureRangeCoreEquiv hh'
    isometry_toFun := hh.closureRangeCoreEquiv_isometry hh' }

/-- Helper for Exercise 43.10: the canonical equivalence between closure completions
intertwines their original embeddings. -/
@[simp]
theorem closureRangeEquiv_apply [CompleteSpace Y] [CompleteSpace Y']
    (hh : Isometry h) (hh' : Isometry h') (x : X) :
    hh.closureRangeEquiv hh' ⟨h x, subset_closure ⟨x, rfl⟩⟩ =
      ⟨h' x, subset_closure ⟨x, rfl⟩⟩ := by
  -- Reduce to the comparison map's computation rule on the dense embedded copy.
  exact hh.closureRangeCoreEquiv_apply hh' x

end Isometry

end
