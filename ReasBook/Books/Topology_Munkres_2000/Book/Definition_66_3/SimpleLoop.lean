module

public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Definition_66_2.FreeHomotopy
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Interval

public section

open unitInterval

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- A simple loop is a loop whose only repeated parameter values are its two endpoints. -/
def IsSimpleLoop (f : C(unitInterval, X)) : Prop :=
  IsLoop f ∧
    ∀ s₁ s₂, f s₁ = f s₂ →
      s₁ = s₂ ∨ (s₁ = 0 ∧ s₂ = 1) ∨ (s₁ = 1 ∧ s₂ = 0)

/-- A continuous map is a simple loop exactly when it is a loop and only identifies endpoints. -/
theorem isSimpleLoop_iff {f : C(unitInterval, X)} :
    IsSimpleLoop f ↔
      IsLoop f ∧
        ∀ s₁ s₂, f s₁ = f s₂ →
          s₁ = s₂ ∨ (s₁ = 0 ∧ s₂ = 1) ∨ (s₁ = 1 ∧ s₂ = 0) :=
  Iff.rfl

namespace IsSimpleLoop

/-- A simple loop is a loop. -/
theorem isLoop {f : C(unitInterval, X)} (hf : IsSimpleLoop f) : IsLoop f :=
  hf.1

/-- Two parameters of a simple loop have equal values exactly in the permitted cases. -/
theorem eq_iff {f : C(unitInterval, X)} (hf : IsSimpleLoop f) (s₁ s₂ : unitInterval) :
    f s₁ = f s₂ ↔
      s₁ = s₂ ∨ (s₁ = 0 ∧ s₂ = 1) ∨ (s₁ = 1 ∧ s₂ = 0) := by
  constructor
  · exact hf.2 s₁ s₂
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact isLoop_iff.mp hf.isLoop
    · exact (isLoop_iff.mp hf.isLoop).symm

end IsSimpleLoop

namespace IsLoop

/-- Helper for Definition 66.3: the endpoint-compatible lift of a loop to `AddCircle 1`
is continuous. -/
lemma unitAddCircleLift_continuous {f : C(unitInterval, X)} (hf : IsLoop f) :
    Continuous (AddCircle.liftIco 1 0 (f.comp ContinuousMap.projIccCM)) := by
  -- The interval extension agrees at the two endpoints and is continuous everywhere.
  apply AddCircle.liftIco_zero_continuous
  · simpa [ContinuousMap.projIccCM, Set.projIcc] using ContinuousMap.isLoop_iff.mp hf
  · exact (f.comp ContinuousMap.projIccCM).continuous.continuousOn

/-- Helper for Definition 66.3: a loop descends to a continuous map from `AddCircle 1`. -/
noncomputable def toUnitAddCircleMap {f : C(unitInterval, X)} (hf : IsLoop f) :
    C(AddCircle (1 : ℝ), X) :=
  ⟨AddCircle.liftIco 1 0 (f.comp ContinuousMap.projIccCM),
    hf.unitAddCircleLift_continuous⟩

/-- Helper for Definition 66.3: the descended loop has the expected underlying function. -/
lemma toUnitAddCircleMap_apply {f : C(unitInterval, X)} (hf : IsLoop f)
    (x : AddCircle (1 : ℝ)) :
    hf.toUnitAddCircleMap x = AddCircle.liftIco 1 0 (f.comp ContinuousMap.projIccCM) x := by
  -- This is the projection rule for the bundled continuous map.
  rfl

/-- Helper for Definition 66.3: the descended loop agrees with the original loop on `[0, 1)`. -/
lemma toUnitAddCircleMap_coe_apply {f : C(unitInterval, X)} (hf : IsLoop f)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    hf.toUnitAddCircleMap (t : AddCircle (1 : ℝ)) = f ⟨t, ht.1, ht.2.le⟩ := by
  -- First compute the quotient lift, then remove the interval projection.
  rw [hf.toUnitAddCircleMap_apply, AddCircle.liftIco_zero_coe_apply ht]
  exact ContinuousMap.IccExtendCM_of_mem ⟨ht.1, ht.2.le⟩

end IsLoop

namespace IsSimpleLoop

/-- Helper for Definition 66.3: the map induced by a simple loop on `AddCircle 1` is injective. -/
lemma toUnitAddCircleMap_injective {f : C(unitInterval, X)} (hf : IsSimpleLoop f) :
    Function.Injective hf.isLoop.toUnitAddCircleMap := by
  -- Choose canonical half-open representatives for the two circle points.
  intro x y hxy
  obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ Set.Ico (0 : ℝ) 1, (x' : AddCircle (1 : ℝ)) = x := by
    have hx : x ∈ Set.univ := Set.mem_univ x
    rw [← AddCircle.coe_image_Ico_eq (1 : ℝ) 0] at hx
    simpa only [Set.mem_image, zero_add] using hx
  obtain ⟨y', hy', rfl⟩ : ∃ y' ∈ Set.Ico (0 : ℝ) 1, (y' : AddCircle (1 : ℝ)) = y := by
    have hy : y ∈ Set.univ := Set.mem_univ y
    rw [← AddCircle.coe_image_Ico_eq (1 : ℝ) 0] at hy
    simpa only [Set.mem_image, zero_add] using hy
  -- Simplicity forces equal representatives, since neither representative can be the endpoint `1`.
  rw [hf.isLoop.toUnitAddCircleMap_coe_apply hx',
    hf.isLoop.toUnitAddCircleMap_coe_apply hy'] at hxy
  rcases (hf.eq_iff _ _).mp hxy with h | h | h
  · exact congrArg (fun z : unitInterval ↦ (z : AddCircle (1 : ℝ))) h
  · exfalso
    exact (not_lt_of_ge (congrArg Subtype.val h.2).ge) hy'.2
  · exfalso
    exact (not_lt_of_ge (congrArg Subtype.val h.1).ge) hx'.2

/-- Helper for Definition 66.3: descending a simple loop to `AddCircle 1` preserves its range. -/
lemma range_toUnitAddCircleMap {f : C(unitInterval, X)} (hf : IsSimpleLoop f) :
    Set.range hf.isLoop.toUnitAddCircleMap = Set.range f := by
  apply Set.Subset.antisymm
  · -- Every circle point has a representative in `[0, 1)`.
    rintro z ⟨x, rfl⟩
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Set.Ico (0 : ℝ) 1, (t : AddCircle (1 : ℝ)) = x := by
      have hx : x ∈ Set.univ := Set.mem_univ x
      rw [← AddCircle.coe_image_Ico_eq (1 : ℝ) 0] at hx
      simpa only [Set.mem_image, zero_add] using hx
    rw [hf.isLoop.toUnitAddCircleMap_coe_apply ht]
    exact ⟨⟨t, ht.1, ht.2.le⟩, rfl⟩
  · -- Parameters below `1` map directly; the endpoint `1` is represented by `0`.
    rintro z ⟨s, rfl⟩
    rcases lt_or_eq_of_le s.property.2 with hs | hs
    · refine ⟨(s : ℝ), ?_⟩
      exact hf.isLoop.toUnitAddCircleMap_coe_apply ⟨s.property.1, hs⟩
    · refine ⟨((0 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      rw [hf.isLoop.toUnitAddCircleMap_coe_apply
        (show (0 : ℝ) ∈ Set.Ico 0 1 by norm_num)]
      have hsOne : s = 1 := Subtype.ext hs
      rw [hsOne]
      calc
        f ⟨0, by norm_num, by norm_num⟩ = f 0 := congrArg f (Subtype.ext rfl)
        _ = f 1 := ContinuousMap.isLoop_iff.mp hf.isLoop

/-- In a T2 space, the range of a simple loop is a simple closed curve. -/
theorem isSimpleClosedCurve_range [T2Space X] {f : C(unitInterval, X)}
    (hf : IsSimpleLoop f) : Topology.IsSimpleClosedCurve (Set.range f) := by
  classical
  -- Compactness and the Hausdorff hypothesis make the descended injection an embedding.
  have hEmbedding : Topology.IsEmbedding hf.isLoop.toUnitAddCircleMap :=
    (hf.isLoop.toUnitAddCircleMap.continuous.isClosedEmbedding
      hf.toUnitAddCircleMap_injective).isEmbedding
  -- Transport its range to the loop range and then use the standard circle homeomorphism.
  let rangeHomeomorph : Set.range f ≃ₜ Circle :=
    (Homeomorph.setCongr hf.range_toUnitAddCircleMap).symm |>.trans
      hEmbedding.toHomeomorph.symm |>.trans
        (AddCircle.homeomorphCircle one_ne_zero)
  exact ⟨⟨rangeHomeomorph⟩⟩

end IsSimpleLoop

end ContinuousMap
