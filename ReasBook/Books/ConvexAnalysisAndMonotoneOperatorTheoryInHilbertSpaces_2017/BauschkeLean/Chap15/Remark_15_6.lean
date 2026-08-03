import Mathlib
import BauschkeLean.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

-- Proof sketch: compute the explicit difference sets in `ℝ²`. For the axis example, the
-- difference is all of `ℝ²`, so clause (iii) holds, while the horizontal axis has empty interior,
-- which is the finite-dimensional set-level rendering of clause (iv) via Corollary 8.39. For the
-- segment example, the difference set is the horizontal segment `[-1,1] × {0}`, whose origin lies
-- in its strong relative interior and whose relative interior is nonempty, while the core
-- condition fails.
/-- Helper for Remark 15 6: the horizontal axis has empty interior inside the vertical axis. -/
lemma horizontal_axis_interior_inter_vertical_axis_eq_empty :
    interior (((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))) ∩ ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))) =
      (∅ : Set (ℝ × ℝ)) := by
  -- The product interior collapses because a singleton in `ℝ` has empty interior.
  rw [interior_prod_eq]
  simp [interior_singleton]

/-- Helper for Remark 15 6: subtracting the vertical axis from the horizontal axis yields all of
`ℝ²`. -/
lemma horizontal_axis_sub_vertical_axis_eq_univ :
    (((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) - ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)))) =
      (Set.univ : Set (ℝ × ℝ)) := by
  ext p
  constructor
  · intro hp
    simp
  · intro hp
    refine Set.mem_sub.mpr ?_
    refine ⟨(p.1, 0), ?_, (0, -p.2), ?_, ?_⟩
    · simp
    · simp
    · ext <;> simp

/-- Helper for Remark 15 6: the difference of the unit horizontal segment with itself is the
symmetric horizontal segment `[-1, 1] × {0}`. -/
lemma segment_sub_segment_eq_horizontal_segment :
    (((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) - (((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)))) =
      (Set.Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ)) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_sub.mp hp with ⟨x, hx, y, hy, rfl⟩
    -- Expand the endpoint constraints on both segment witnesses.
    have hx' : x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 = 0 := by
      simpa using hx
    have hy' : y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ y.2 = 0 := by
      simpa using hy
    have hfst : x.1 - y.1 ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hx'.1.1, hx'.1.2, hy'.1.1, hy'.1.2]
    have hsnd : x.2 - y.2 ∈ ({0} : Set ℝ) := by
      simp [hx'.2, hy'.2]
    simpa using And.intro hfst hsnd
  · intro hp
    -- Split by the sign of the first coordinate to build explicit witnesses in `[0,1]`.
    have hp' : p.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ p.2 = 0 := by
      simpa using hp
    by_cases hnonneg : 0 ≤ p.1
    · refine Set.mem_sub.mpr ?_
      refine ⟨(p.1, 0), ?_, (0, 0), ?_, ?_⟩
      · simp [hnonneg, hp'.1.2]
      · simp
      · ext <;> simp [hp'.2]
    · have hnonpos : p.1 ≤ 0 := le_of_not_ge hnonneg
      have hneg_nonneg : 0 ≤ -p.1 := by linarith
      have hneg_le_one : -p.1 ≤ 1 := by linarith [hp'.1.1]
      refine Set.mem_sub.mpr ?_
      refine ⟨(0, 0), ?_, (-p.1, 0), ?_, ?_⟩
      · simp
      · simp [hneg_nonneg, hneg_le_one]
      · ext <;> simp [hp'.2]

/-- Helper for Remark 15 6: subtracting the zero singleton does not change a set. -/
lemma sub_singleton_zero_eq_self {E : Type*} [AddGroup E] (C : Set E) :
    C - ({0} : Set E) = C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hyz⟩
    have hz0 : z = 0 := by
      simpa using hz
    subst z
    have hxy : x = y := by
      simpa using hyz.symm
    simpa [hxy] using hy
  · intro hx
    refine Set.mem_sub.mpr ?_
    refine ⟨x, hx, 0, ?_, ?_⟩
    · simp
    · simp

/-- Helper for Remark 15 6: points of a horizontal segment have second coordinate `0`. -/
lemma snd_eq_zero_of_mem_horizontal_segment {a : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) : p.2 = 0 := by
  -- Membership in the product set fixes the second coordinate.
  have hp' : p.1 ∈ Set.Icc (-a) a ∧ p.2 = 0 := by
    simpa using hp
  exact hp'.2

/-- Helper for Remark 15 6: every point in the cone over a horizontal segment still has second
coordinate `0`. -/
lemma snd_eq_zero_of_mem_cone_horizontal_segment {a : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ cone (Set.Icc (-a) a ×ˢ ({0} : Set ℝ))) : p.2 = 0 := by
  -- The generator is convex, so cone membership comes from a positive multiple of a segment point.
  change p ∈ (ConvexCone.hull ℝ (Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) : Set (ℝ × ℝ)) at hp
  have hconvex : Convex ℝ (Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) := by
    exact (convex_Icc (-a) a).prod (convex_singleton (0 : ℝ))
  rcases (ConvexCone.mem_hull_of_convex hconvex).1 hp with ⟨r, hr, hp'⟩
  rcases Set.mem_smul_set.mp hp' with ⟨q, hq, rfl⟩
  have hq2 : q.2 = 0 := snd_eq_zero_of_mem_horizontal_segment hq
  simp [hq2]

/-- Helper for Remark 15 6: the cone over any symmetric horizontal segment of positive radius is
the whole horizontal axis. -/
lemma horizontal_segment_cone_eq_horizontal_axis {a : ℝ} (ha : 0 < a) :
    cone (Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) = (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
  have hconvex : Convex ℝ (Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) := by
    exact (convex_Icc (-a) a).prod (convex_singleton (0 : ℝ))
  ext p
  constructor
  · intro hp
    -- The cone never produces a nonzero second coordinate.
    have hp2 : p.2 = 0 := snd_eq_zero_of_mem_cone_horizontal_segment hp
    simp [hp2]
  · intro hp
    -- Rescale the point back into the generating segment.
    have hp2 : p.2 = 0 := by
      simpa using hp
    let r : ℝ := |p.1| / a + 1
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hbound : |p.1| ≤ a * r := by
      have hr_eq : a * r = |p.1| + a := by
        calc
          a * r = a * (|p.1| / a + 1) := by rfl
          _ = a * (|p.1| / a) + a := by ring
          _ = |p.1| + a := by rw [mul_div_cancel₀ _ ha.ne']
      nlinarith [abs_nonneg p.1, ha, hr_eq]
    have habs_le : |p.1| / r ≤ a := by
      rw [div_le_iff₀ hr]
      exact hbound
    have habs : |p.1 / r| ≤ a := by
      rw [abs_div, abs_of_pos hr]
      simpa using habs_le
    have hp_interval : p.1 / r ∈ Set.Icc (-a) a := by
      exact abs_le.mp habs
    have hscale_first : r * (p.1 / r) = p.1 := by
      calc
        r * (p.1 / r) = r * (p.1 * r⁻¹) := by rw [div_eq_mul_inv]
        _ = p.1 * (r * r⁻¹) := by ring
        _ = p.1 * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hr)]
        _ = p.1 := by ring
    refine (ConvexCone.mem_hull_of_convex hconvex).2 ?_
    refine ⟨r, hr, ?_⟩
    refine Set.mem_smul_set.mpr ?_
    refine ⟨(p.1 / r, (0 : ℝ)), ?_, ?_⟩
    · simpa using And.intro hp_interval (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
    · ext <;> simp [hscale_first, hp2]

/-- Helper for Remark 15 6: the span of a symmetric horizontal segment of positive radius is the
whole horizontal axis. -/
lemma horizontal_segment_span_eq_horizontal_axis {a : ℝ} (ha : 0 < a) :
    (Submodule.span ℝ (Set.Icc (-a) a ×ˢ ({0} : Set ℝ)) : Set (ℝ × ℝ)) =
      (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
  let S : Set (ℝ × ℝ) := Set.Icc (-a) a ×ˢ ({0} : Set ℝ)
  have hspan_le : Submodule.span ℝ S ≤ Submodule.fst ℝ ℝ ℝ := by
    -- Every generator already lies on the horizontal axis, so the whole span does too.
    refine Submodule.span_le.mpr ?_
    intro p hp
    have hp2 : p.2 = 0 := snd_eq_zero_of_mem_horizontal_segment hp
    simp [Submodule.fst, hp2]
  have hfst_le : Submodule.fst ℝ ℝ ℝ ≤ Submodule.span ℝ S := by
    intro p hp
    -- The endpoint `(a, 0)` lies in the segment, and scalar multiples recover any horizontal point.
    have hp2 : p.2 = 0 := by
      simpa [Submodule.fst] using hp
    have ha_mem : (a, (0 : ℝ)) ∈ S := by
      have hleft : -a ≤ a := by linarith
      simp [S, hleft]
    have hbase : (a, (0 : ℝ)) ∈ Submodule.span ℝ S := Submodule.subset_span ha_mem
    have hscale_first : (p.1 / a) * a = p.1 := by
      calc
        (p.1 / a) * a = (p.1 * a⁻¹) * a := by rw [div_eq_mul_inv]
        _ = p.1 * (a⁻¹ * a) := by ring
        _ = p.1 * 1 := by rw [inv_mul_cancel₀ ha.ne']
        _ = p.1 := by ring
    have hscale : (p.1 / a) • (a, (0 : ℝ)) = p := by
      ext <;> simp [hscale_first, hp2]
    exact hscale ▸ Submodule.smul_mem (Submodule.span ℝ S) (p.1 / a) hbase
  ext p
  constructor
  · intro hp
    have hp' : p ∈ Submodule.fst ℝ ℝ ℝ := hspan_le hp
    simpa [Submodule.fst] using hp'
  · intro hp
    have hp' : p ∈ Submodule.fst ℝ ℝ ℝ := by
      simpa [Submodule.fst] using hp
    exact hfst_le hp'

/-- Helper for Remark 15 6: the origin belongs to the segment difference with itself. -/
lemma zero_mem_segment_sub_segment :
    (0 : ℝ × ℝ) ∈ (((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) -
      (((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)))) := by
  -- Use the same endpoint in both copies of the segment.
  refine Set.mem_sub.mpr ?_
  refine ⟨(0, 0), ?_, (0, 0), ?_, ?_⟩
  · simp
  · simp
  · simp

/-- Helper for Remark 15 6: the translated cone at the origin misses the vertical direction, so
the origin is not in the core of the segment difference. -/
lemma zero_not_mem_core_segment_sub_segment :
    ¬ ((0 : ℝ × ℝ) ∈ core ((((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) -
      ((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ))))) := by
  -- Route correction: the obstruction is the missing vertical direction `(0, 1)`, not the later
  -- `sri` or `ri` clauses.
  intro hcore
  rcases Set.mem_core_iff.mp hcore with ⟨_, hcone_univ⟩
  have h01 : ((0 : ℝ), (1 : ℝ)) ∈
      cone (((((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) -
        ((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ))) - ({(0 : ℝ × ℝ)} : Set (ℝ × ℝ)))) := by
    rw [hcone_univ]
    simp
  rw [segment_sub_segment_eq_horizontal_segment, sub_singleton_zero_eq_self] at h01
  have hsnd : (((0 : ℝ), (1 : ℝ))).2 = 0 := snd_eq_zero_of_mem_cone_horizontal_segment h01
  norm_num at hsnd

/-- Helper for Remark 15 6: translating the unit segment by its midpoint gives the symmetric
half-segment `[-1 / 2, 1 / 2] × {0}`. -/
lemma segment_sub_midpoint_eq_horizontal_half_segment :
    (((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) -
      ({((1 / 2 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))) =
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ ({0} : Set ℝ)) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_sub.mp hp with ⟨x, hx, y, hy, rfl⟩
    -- Expanding the translated segment gives the centered interval bounds.
    have hx' : x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 = 0 := by
      simpa using hx
    have hy' : y = ((1 / 2 : ℝ), (0 : ℝ)) := by
      simpa using hy
    subst y
    have hfst : x.1 - (1 / 2 : ℝ) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      constructor <;> linarith [hx'.1.1, hx'.1.2]
    have hsnd : x.2 - (0 : ℝ) ∈ ({0} : Set ℝ) := by
      simp [hx'.2]
    simpa using And.intro hfst hsnd
  · intro hp
    -- Shift the centered interval back by `1 / 2`.
    have hp' : p.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧ p.2 = 0 := by
      simpa using hp
    have hleft : 0 ≤ p.1 + 1 / 2 := by
      linarith [hp'.1.1]
    have hright : p.1 + 1 / 2 ≤ 1 := by
      linarith [hp'.1.2]
    refine Set.mem_sub.mpr ?_
    refine ⟨(p.1 + 1 / 2, 0), ?_, ((1 / 2 : ℝ), 0), ?_, ?_⟩
    · simpa using And.intro (And.intro hleft hright) (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
    · simp
    · ext <;> simp [hp'.2]

/-- Helper for Remark 15 6: the origin lies in the strong relative interior of the segment
difference. -/
lemma zero_mem_sri_segment_sub_segment :
    (0 : ℝ × ℝ) ∈ sri ((((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) -
      ((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)))) := by
  -- Compute the translated difference set and identify both sides with the horizontal axis.
  rw [Set.mem_strongRelativeInterior_iff]
  constructor
  · exact zero_mem_segment_sub_segment
  · rw [segment_sub_segment_eq_horizontal_segment, sub_singleton_zero_eq_self]
    calc
      cone (Set.Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ)) =
          (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) :=
        horizontal_segment_cone_eq_horizontal_axis (by norm_num)
      _ = closure ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) := by
        symm
        exact IsClosed.closure_eq
          ((isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod isClosed_singleton)
      _ = closure ((Submodule.span ℝ (Set.Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ)) : Set (ℝ × ℝ))) := by
        rw [horizontal_segment_span_eq_horizontal_axis (a := (1 : ℝ)) (by norm_num)]
      _ =
          ((Submodule.span ℝ (Set.Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ))).topologicalClosure :
            Set (ℝ × ℝ)) := by
        rw [Submodule.topologicalClosure_coe]

/-- Helper for Remark 15 6: the midpoint of the unit segment lies in its relative interior. -/
lemma midpoint_mem_ri_segment :
    ((1 / 2 : ℝ), (0 : ℝ)) ∈ ri ((Set.Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ)) := by
  -- Translate by the midpoint and again compare the cone and the span with the horizontal axis.
  rw [Set.mem_relativeInterior_iff]
  constructor
  · have hmid : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    simpa using And.intro hmid (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
  · rw [segment_sub_midpoint_eq_horizontal_half_segment]
    calc
      cone (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ ({0} : Set ℝ)) =
          (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) :=
        horizontal_segment_cone_eq_horizontal_axis (by norm_num)
      _ =
          (Submodule.span ℝ (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ ({0} : Set ℝ)) :
            Set (ℝ × ℝ)) := by
        symm
        exact horizontal_segment_span_eq_horizontal_axis (a := (1 / 2 : ℝ)) (by norm_num)

/-- Remark 15 6: the regularity conditions in Proposition 15.5 are not equivalent. In `ℝ²`, for
the domain pair `ℝ × {0}` and `{0} × ℝ`, the finite-dimensional set-level form of clause (iv),
namely `interior C ∩ D ≠ ∅`, fails while clause (iii) holds. For the pair
`[0,1] × {0}` and `[0,1] × {0}`, clause (ii) fails while `(15.9)` and clause (v) hold. -/
theorem attouchBrezisRegularityConditions_not_equivalent :
    let horizontalAxis : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)
    let verticalAxis : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)
    let segment : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)
    (¬ (interior horizontalAxis ∩ verticalAxis).Nonempty ∧
      (0 : ℝ × ℝ) ∈ interior (horizontalAxis - verticalAxis)) ∧
      (¬ ((0 : ℝ × ℝ) ∈ core (segment - segment)) ∧
        (0 : ℝ × ℝ) ∈ sri (segment - segment) ∧
        (ri segment ∩ ri segment).Nonempty) := by
  dsimp
  constructor
  · constructor
    · -- The horizontal axis has empty interior in `ℝ²`, so the intersection is empty.
      rw [horizontal_axis_interior_inter_vertical_axis_eq_empty]
      simp
    · -- The axis difference is all of `ℝ²`, hence its interior contains the origin.
      rw [horizontal_axis_sub_vertical_axis_eq_univ]
      simp
  · constructor
    · exact zero_not_mem_core_segment_sub_segment
    · constructor
      · exact zero_mem_sri_segment_sub_segment
      · -- The midpoint belongs to `ri segment`, so the self-intersection is nonempty.
        refine ⟨((1 / 2 : ℝ), (0 : ℝ)), ?_, ?_⟩
        · exact midpoint_mem_ri_segment
        · exact midpoint_mem_ri_segment
