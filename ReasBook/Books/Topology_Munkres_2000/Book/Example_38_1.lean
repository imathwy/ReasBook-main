module

public import Topology_Munkres_2000.Book.Definition_38_1.Equivalence
public import Topology_Munkres_2000.Book.Example_38_1.Compactifications

public section

open Complex Set

namespace OpenUnitInterval

/-- Helper for Example 38.1: the circle parametrization is the standard `AddCircle 1`
homeomorphism after taking the quotient class of the parameter. -/
private lemma circleMap_eq_addCircleHomeomorph (t : Ioo (0 : ℝ) 1) :
    circleMap t = AddCircle.homeomorphCircle one_ne_zero (t.1 : AddCircle (1 : ℝ)) := by
  -- Normalize both parametrizations to the same circle exponential.
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  apply Circle.ext
  rw [circleMap_apply]
  simp only [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  congr 1
  · congr 1
    ring_nf
  · congr 1
    ring_nf

/-- Helper for Example 38.1: the circle parametrization covers exactly the circle with `1`
omitted. -/
private lemma range_circleMap :
    Set.range circleMap = ({(1 : Circle)} : Set Circle)ᶜ := by
  -- Transport the canonical punctured `AddCircle` chart through its homeomorphism with `Circle`.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, circleMap_eq_addCircleHomeomorph]
    intro h
    have hzero : (t.1 : AddCircle (1 : ℝ)) = 0 := by
      apply (AddCircle.homeomorphCircle one_ne_zero).injective
      calc
        AddCircle.homeomorphCircle one_ne_zero (t.1 : AddCircle (1 : ℝ)) = 1 := h
        _ = AddCircle.homeomorphCircle one_ne_zero 0 := by
          simp [AddCircle.homeomorphCircle_apply]
    let chart := AddCircle.openPartialHomeomorphCoe (p := (1 : ℝ)) (a := 0)
    have ht : t.1 ∈ chart.source := by
      simp [chart, t.property]
    have htarget := chart.map_source ht
    have hne : (t.1 : AddCircle (1 : ℝ)) ≠ 0 := by
      simpa [chart] using htarget
    exact hne hzero
  · intro hz
    have hz' : z ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    let x : AddCircle (1 : ℝ) := (AddCircle.homeomorphCircle one_ne_zero).symm z
    have hx : x ∈ ({(0 : AddCircle (1 : ℝ))} : Set (AddCircle (1 : ℝ)))ᶜ := by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxzero
      apply hz'
      calc
        z = AddCircle.homeomorphCircle one_ne_zero x := by
          exact ((AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z).symm
        _ = 1 := by simp [hxzero, AddCircle.homeomorphCircle_apply]
    have hchart :
        (fun r : ℝ ↦ (r : AddCircle (1 : ℝ))) '' Ioo (0 : ℝ) 1 =
          ({(0 : AddCircle (1 : ℝ))} : Set (AddCircle (1 : ℝ)))ᶜ := by
      simpa using
        (AddCircle.openPartialHomeomorphCoe (p := (1 : ℝ)) (a := 0)).image_source_eq_target
    rw [← hchart] at hx
    rcases hx with ⟨r, hr, hrx⟩
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [circleMap_eq_addCircleHomeomorph]
    calc
      AddCircle.homeomorphCircle one_ne_zero
          ((⟨r, hr⟩ : Ioo (0 : ℝ) 1).1 : AddCircle (1 : ℝ)) =
          AddCircle.homeomorphCircle one_ne_zero x := by
        exact congrArg (AddCircle.homeomorphCircle one_ne_zero) hrx
      _ = z := (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z

/-- Helper for Example 38.1: the range of the circle parametrization is dense in the circle. -/
private lemma closure_range_circleMap :
    closure (Set.range circleMap) = (Set.univ : Set Circle) := by
  -- Rewrite the range as a punctured circle and rule out an open singleton by connectedness.
  rw [range_circleMap]
  apply Dense.closure_eq
  rw [dense_compl_singleton_iff_not_open]
  intro hopen
  have hclopen : IsClopen ({(1 : Circle)} : Set Circle) := ⟨isClosed_singleton, hopen⟩
  have huniv : ({(1 : Circle)} : Set Circle) = Set.univ :=
    IsClopen.eq_univ hclopen (Set.singleton_nonempty 1)
  have hneg : (-1 : Circle) ∈ ({(1 : Circle)} : Set Circle) := by
    rw [huniv]
    exact Set.mem_univ (-1)
  have hne : (-1 : Circle) ≠ 1 := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num at hval
  exact hne (Set.mem_singleton_iff.mp hneg)

/-- Helper for Example 38.1: the omitted endpoint belongs to the induced closure. -/
private lemma one_mem_closure_range_circleMap :
    (1 : Circle) ∈ closure (Set.range circleMap) := by
  -- The closure computation makes membership immediate.
  rw [closure_range_circleMap]
  exact Set.mem_univ 1

/-- Helper for Example 38.1: the distinguished added point of the circle compactification. -/
private noncomputable def circleCompactificationBasepoint :
    circleCompactification :=
  ⟨1, one_mem_closure_range_circleMap⟩

/-- Helper for Example 38.1: the compactification embedding omits exactly its distinguished
basepoint. -/
private lemma range_circleCompactification :
    Set.range circleCompactification =
      ({circleCompactificationBasepoint} : Set circleCompactification)ᶜ := by
  -- Compare range membership in the induced subtype with the ambient punctured-circle range.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hbase
    have hambient : circleMap t = 1 := by
      simpa only [circleCompactification_apply, InducedCompactification.ofMap,
        circleCompactificationBasepoint] using congrArg Subtype.val hbase
    have hrange : circleMap t ∈ Set.range circleMap := Set.mem_range_self t
    rw [range_circleMap, Set.mem_compl_iff, Set.mem_singleton_iff] at hrange
    exact hrange hambient
  · intro hz
    have hambient : z.1 ≠ (1 : Circle) := by
      intro hone
      have hbase : z = circleCompactificationBasepoint := by
        apply Subtype.ext
        simpa only [circleCompactificationBasepoint] using hone
      exact hz hbase
    have hrange : z.1 ∈ Set.range circleMap := by
      rw [range_circleMap, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hambient
    rcases hrange with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    simpa only [circleCompactification_apply, InducedCompactification.ofMap] using ht

/-- Example 38.1. The compactification induced by the circle embedding of `(0, 1)` is
equivalent over `(0, 1)` to its one-point compactification. -/
theorem circleCompactification_equivalent_onePoint :
    Compactification.Equivalent circleCompactification onePointCompactification := by
  -- Apply uniqueness of a one-point compactification to the single omitted circle point.
  rw [Compactification.equivalent_iff]
  change ∃ h : circleCompactification ≃ₜ OnePoint (Ioo (0 : ℝ) 1),
    ∀ t, h (circleCompactification t) = OnePoint.some t
  let e : OnePoint (Ioo (0 : ℝ) 1) ≃ₜ circleCompactification :=
    OnePoint.equivOfIsEmbeddingOfRangeEq circleCompactificationBasepoint
      circleCompactification circleCompactification.isDenseEmbedding.isEmbedding
      range_circleCompactification
  have hcommutes : ∀ t : Ioo (0 : ℝ) 1,
      e.symm (circleCompactification t) = OnePoint.some t := by
    intro t
    -- The uniqueness homeomorphism sends each ordinary point to the induced embedding.
    apply e.injective
    rw [e.apply_symm_apply]
    exact OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe
      (y := circleCompactificationBasepoint) (f := circleCompactification)
      circleCompactification.isDenseEmbedding.isEmbedding range_circleCompactification t
  exact ⟨e.symm, hcommutes⟩

end OpenUnitInterval

end
