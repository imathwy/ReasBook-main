module

public import Topology_Munkres_2000.Book.Definition_8_99_3
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

public section

open Set

namespace PruferManifold


/-- The open sheet `A ∪ B_c` that is the range of the chart indexed by `c`. -/
def chartRange (c : ℝ) : Set PruferManifold :=
  {p | 0 < p.x ∨ (p.x ≤ 0 ∧ p.z = c)}

/-- Membership in the chart range is the source condition for belonging to `A ∪ B_c`. -/
theorem mem_chartRange_iff {c : ℝ} {p : PruferManifold} :
    p ∈ chartRange c ↔ 0 < p.x ∨ (p.x ≤ 0 ∧ p.z = c) := by
  rfl

/-- The explicit piecewise map `f_c : ℝ × ℝ → PruferManifold` from the exercise. -/
noncomputable def chartMap (c : ℝ) (p : ℝ × ℝ) : PruferManifold :=
  if hx : 0 < p.1 then upper p.1 (c + p.1 * p.2) hx
  else sheet c p.1 p.2 (le_of_not_gt hx)

/-- Helper for Exercise 8.99.6: the chart map uses the upper formula at positive inputs. -/
lemma chartMap_of_pos (c : ℝ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    chartMap c p = upper p.1 (c + p.1 * p.2) hp := by
  unfold chartMap
  rw [dif_pos hp]

/-- Helper for Exercise 8.99.6: the chart map uses its sheet formula at nonpositive inputs. -/
lemma chartMap_of_nonpos (c : ℝ) (p : ℝ × ℝ) (hp : ¬0 < p.1) :
    chartMap c p = sheet c p.1 p.2 (le_of_not_gt hp) := by
  unfold chartMap
  rw [dif_neg hp]

/-- The explicit map `f_c` takes values in the open sheet `A ∪ B_c`. -/
theorem chartMap_mem (c : ℝ) (p : ℝ × ℝ) : chartMap c p ∈ chartRange c := by
  by_cases hx : 0 < p.1
  · rw [chartMap_of_pos c p hx, mem_chartRange_iff]
    simp only [upper_x]
    exact Or.inl hx
  · rw [chartMap_of_nonpos c p hx, mem_chartRange_iff]
    simp only [sheet_x, sheet_z]
    apply Or.inr
    constructor
    · exact le_of_not_gt hx
    · trivial

/-- The inverse coordinate map on `A ∪ B_c`, using slope above the boundary line. -/
noncomputable def chartInv (c : ℝ) (p : chartRange c) : ℝ × ℝ :=
  if 0 < p.1.x then (p.1.x, (p.1.y - c) / p.1.x) else (p.1.x, p.1.y)

/-- The explicit inverse is a left inverse to `f_c`. -/
theorem chartInv_left (c : ℝ) (p : ℝ × ℝ) :
    chartInv c ⟨chartMap c p, chartMap_mem c p⟩ = p := by
  by_cases hx : 0 < p.1
  · simp only [chartInv, chartMap_of_pos c p hx, upper_x, upper_y, if_pos hx]
    apply Prod.ext
    · rfl
    · have hx0 : p.1 ≠ 0 := ne_of_gt hx
      field_simp
      ring
  · simp only [chartInv, chartMap_of_nonpos c p hx, sheet_x, sheet_y, if_neg hx]

/-- The explicit inverse is a right inverse to `f_c` on `A ∪ B_c`. -/
theorem chartInv_right (c : ℝ) (p : chartRange c) :
    chartMap c (chartInv c p) = p.1 := by
  by_cases hx : 0 < p.1.x
  · have hz : p.1.z = 0 := by
      rcases p.1.valid with hp | hp
      · exact hp.2
      · exact False.elim (not_lt_of_ge hp hx)
    simp only [chartInv, if_pos hx, chartMap, dif_pos hx]
    apply PruferManifold.ext
    · simp only [upper_x]
    · simp only [upper_y]
      field_simp
      ring
    · simpa only [upper_z] using hz.symm
  · have hpRange := mem_chartRange_iff.mp p.2
    have hz : p.1.z = c := by
      rcases hpRange with hp | hp
      · exact False.elim (hx hp)
      · exact hp.2
    simp only [chartInv, if_neg hx, chartMap, dif_neg hx]
    apply PruferManifold.ext
    · simp only [sheet_x]
    · simp only [sheet_y]
    · simpa only [sheet_z] using hz.symm

/-- Helper for Exercise 8.99.6: the coordinate map is continuous in the Prüfer topology. -/
private lemma continuous_chartMap_ambient (c : ℝ) : Continuous (chartMap c) := by
  -- It suffices to compute the inverse image of each of the three defining basis families.
  rw [basis_isTopologicalBasis.continuous_iff]
  intro s hs
  rcases mem_basis_iff.mp hs with ⟨U, hU, rfl⟩ | ⟨d, U, hU, rfl⟩ |
    ⟨d, a, b, ε, hab, hε, rfl⟩
  · let g : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, c + p.1 * p.2)
    have hg : Continuous g := continuous_fst.prodMk
      (continuous_const.add (continuous_fst.mul continuous_snd))
    have hpreimage : chartMap c ⁻¹' upperOpen U = {p | 0 < p.1} ∩ g ⁻¹' U := by
      ext p
      by_cases hp : 0 < p.1
      · simp only [Set.mem_preimage]
        rw [chartMap_of_pos c p hp]
        simp only [Set.mem_preimage, mem_upperOpen_iff, upper_x, upper_y,
          Set.mem_inter_iff, Set.mem_setOf_eq, hp, true_and, g]
      · simp only [Set.mem_preimage]
        rw [chartMap_of_nonpos c p hp]
        simp only [Set.mem_preimage, mem_upperOpen_iff, sheet_x,
          Set.mem_inter_iff, Set.mem_setOf_eq, hp, false_and]
    rw [hpreimage]
    exact (isOpen_lt continuous_const continuous_fst).inter (hU.preimage hg)
  · by_cases hcd : c = d
    · subst d
      have hpreimage :
          chartMap c ⁻¹' sheetInteriorOpen c U = {p | p.1 < 0} ∩ U := by
        ext p
        by_cases hp : 0 < p.1
        · simp only [Set.mem_preimage]
          rw [chartMap_of_pos c p hp]
          simp only [mem_sheetInteriorOpen_iff, upper_z, upper_x,
            Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · exact fun h ↦ False.elim (not_lt_of_ge (le_of_lt hp) h.2.1)
          · exact fun h ↦ False.elim (not_lt_of_ge (le_of_lt hp) h.1)
        · simp only [Set.mem_preimage]
          rw [chartMap_of_nonpos c p hp]
          simp only [mem_sheetInteriorOpen_iff, sheet_z, sheet_x, sheet_y,
            Set.mem_inter_iff, Set.mem_setOf_eq, true_and]
      rw [hpreimage]
      exact (isOpen_lt continuous_fst continuous_const).inter hU
    · have hpreimage : chartMap c ⁻¹' sheetInteriorOpen d U = ∅ := by
        ext p
        by_cases hp : 0 < p.1
        · simp only [Set.mem_preimage]
          rw [chartMap_of_pos c p hp]
          simp only [mem_sheetInteriorOpen_iff, upper_z, upper_x,
            Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ False.elim (not_lt_of_ge (le_of_lt hp) h.2.1)
        · simp only [Set.mem_preimage]
          rw [chartMap_of_nonpos c p hp]
          simp only [mem_sheetInteriorOpen_iff, sheet_z,
            Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ hcd h.1
      rw [hpreimage]
      exact isOpen_empty
  · by_cases hcd : c = d
    · subst d
      let R : Set (ℝ × ℝ) := {p | -ε < p.1 ∧ p.1 < ε ∧ a < p.2 ∧ p.2 < b}
      have hpreimage : chartMap c ⁻¹' gluingNeighborhood c a b ε = R := by
        ext p
        by_cases hp : 0 < p.1
        · simp only [Set.mem_preimage]
          rw [chartMap_of_pos c p hp]
          simp only [mem_gluingNeighborhood_iff, mem_upperWedge_iff,
            upper_x, upper_y, mem_sheetStrip_iff, upper_z, R, Set.mem_setOf_eq]
          constructor
          · rintro (h | h)
            · have ha' : a < p.2 := by nlinarith
              have hb' : p.2 < b := by nlinarith
              have hleft : -ε < p.1 := by linarith
              exact ⟨hleft, h.2.1, ha', hb'⟩
            · linarith [h.2.2.1]
          · intro h
            apply Or.inl
            constructor
            · exact hp
            constructor
            · exact h.2.1
            constructor
            · nlinarith
            · nlinarith
        · simp only [Set.mem_preimage]
          rw [chartMap_of_nonpos c p hp]
          simp only [mem_gluingNeighborhood_iff, mem_upperWedge_iff,
            sheet_x, sheet_y, mem_sheetStrip_iff, sheet_z, R, Set.mem_setOf_eq]
          constructor
          · rintro (h | h)
            · exact False.elim (hp h.1)
            · have hright : p.1 < ε := by linarith [h.2.2.1]
              exact ⟨h.2.1, hright, h.2.2.2.1, h.2.2.2.2⟩
          · intro h
            apply Or.inr
            constructor
            · trivial
            · exact ⟨h.1, le_of_not_gt hp, h.2.2.1, h.2.2.2⟩
      rw [hpreimage]
      have hleft : IsOpen {p : ℝ × ℝ | -ε < p.1} :=
        isOpen_lt continuous_const continuous_fst
      have hright : IsOpen {p : ℝ × ℝ | p.1 < ε} :=
        isOpen_lt continuous_fst continuous_const
      have hlower : IsOpen {p : ℝ × ℝ | a < p.2} :=
        isOpen_lt continuous_const continuous_snd
      have hupper : IsOpen {p : ℝ × ℝ | p.2 < b} :=
        isOpen_lt continuous_snd continuous_const
      exact hleft.inter (hright.inter (hlower.inter hupper))
    · let W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < ε ∧
          d + a * p.1 < c + p.1 * p.2 ∧ c + p.1 * p.2 < d + b * p.1}
      have hpreimage : chartMap c ⁻¹' gluingNeighborhood d a b ε = W := by
        ext p
        by_cases hp : 0 < p.1
        · simp only [Set.mem_preimage]
          rw [chartMap_of_pos c p hp]
          simp only [mem_gluingNeighborhood_iff, mem_upperWedge_iff,
            upper_x, upper_y, mem_sheetStrip_iff, upper_z, W, Set.mem_setOf_eq]
          constructor
          · rintro (h | h)
            · exact h
            · linarith [h.2.2.1]
          · exact fun h ↦ Or.inl h
        · simp only [Set.mem_preimage]
          rw [chartMap_of_nonpos c p hp]
          simp only [mem_gluingNeighborhood_iff, mem_upperWedge_iff,
            sheet_x, sheet_y, mem_sheetStrip_iff, sheet_z, W, Set.mem_setOf_eq]
          constructor
          · rintro (h | h)
            · exact False.elim (hp h.1)
            · exact False.elim (hcd h.1)
          · exact fun h ↦ False.elim (hp h.1)
      rw [hpreimage]
      have hpositive : IsOpen {p : ℝ × ℝ | 0 < p.1} :=
        isOpen_lt continuous_const continuous_fst
      have hradius : IsOpen {p : ℝ × ℝ | p.1 < ε} :=
        isOpen_lt continuous_fst continuous_const
      have hlower : IsOpen {p : ℝ × ℝ | d + a * p.1 < c + p.1 * p.2} :=
        isOpen_lt (continuous_const.add (continuous_const.mul continuous_fst))
          (continuous_const.add (continuous_fst.mul continuous_snd))
      have hupper : IsOpen {p : ℝ × ℝ | c + p.1 * p.2 < d + b * p.1} :=
        isOpen_lt (continuous_const.add (continuous_fst.mul continuous_snd))
          (continuous_const.add (continuous_const.mul continuous_fst))
      exact hpositive.inter (hradius.inter (hlower.inter hupper))

/-- The explicit map `f_c` is continuous into the open sheet `A ∪ B_c`. -/
theorem continuous_chartMap (c : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ (⟨chartMap c p, chartMap_mem c p⟩ : chartRange c)) := by
  -- The subtype topology reduces continuity to the ambient coordinate map.
  exact Topology.IsInducing.subtypeVal.continuous_iff.mpr (continuous_chartMap_ambient c)

/-- The explicit inverse coordinate map on `A ∪ B_c` is continuous. -/
theorem continuous_chartInv (c : ℝ) : Continuous (chartInv c) := by
  -- Pull back an arbitrary coordinate-plane open and choose a basis neighborhood by sign.
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro p hp
  rcases lt_trichotomy p.1.x 0 with hpx | hpx | hpx
  · have hpz : p.1.z = c := by
      have hpRange := mem_chartRange_iff.mp p.2
      exact (hpRange.resolve_left (not_lt_of_ge hpx.le)).2
    have hpU : (p.1.x, p.1.y) ∈ U := by
      have hnot : ¬0 < p.1.x := not_lt_of_ge hpx.le
      simpa only [Set.mem_preimage, chartInv, if_neg hnot] using hp
    have hSheetOpen : IsOpen (sheetInteriorOpen c U) :=
      basis_isTopologicalBasis.isOpen
        (mem_basis_iff.mpr (Or.inr (Or.inl ⟨c, U, hU, rfl⟩)))
    have hpSheet : p ∈ Subtype.val ⁻¹' sheetInteriorOpen c U :=
      mem_sheetInteriorOpen_iff.mpr ⟨hpz, hpx, hpU⟩
    refine Filter.mem_of_superset
      ((hSheetOpen.preimage continuous_subtype_val).mem_nhds hpSheet) ?_
    intro q hq
    have hqData := mem_sheetInteriorOpen_iff.mp hq
    have hqNot : ¬0 < q.1.x := not_lt_of_ge (le_of_lt hqData.2.1)
    simpa only [Set.mem_preimage, chartInv, if_neg hqNot] using hqData.2.2
  · have hpz : p.1.z = c := by
      have hpRange := mem_chartRange_iff.mp p.2
      exact (hpRange.resolve_left (not_lt_of_ge hpx.le)).2
    have hpU : (0, p.1.y) ∈ U := by
      have hnot : ¬0 < p.1.x := not_lt_of_ge hpx.le
      have hpU' : (p.1.x, p.1.y) ∈ U := by
        simpa only [Set.mem_preimage, chartInv, if_neg hnot] using hp
      rwa [hpx] at hpU'
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hpU)
    obtain ⟨l, r, hzero, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
    obtain ⟨a, b, hy, habv⟩ := mem_nhds_iff_exists_Ioo_subset.mp hv
    let ε := min (-l) r
    have hε : 0 < ε := by
      exact lt_min (neg_pos.mpr hzero.1) hzero.2
    have hGluingOpen : IsOpen (gluingNeighborhood c a b ε) :=
      basis_isTopologicalBasis.isOpen
        (mem_basis_iff.mpr (Or.inr (Or.inr ⟨c, a, b, ε, hy.1.trans hy.2, hε, rfl⟩)))
    have hpGluing : p ∈ Subtype.val ⁻¹' gluingNeighborhood c a b ε := by
      simp only [Set.mem_preimage]
      rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
      apply Or.inr
      refine ⟨hpz, ?_, hpx.le, hy.1, hy.2⟩
      linarith
    refine Filter.mem_of_superset
      ((hGluingOpen.preimage continuous_subtype_val).mem_nhds hpGluing) ?_
    intro q hq
    rcases mem_gluingNeighborhood_iff.mp hq with hqWedge | hqStrip
    · have hqData := mem_upperWedge_iff.mp hqWedge
      have hqFirst : q.1.x ∈ Ioo l r := by
        constructor
        · exact hzero.1.trans hqData.1
        · exact hqData.2.1.trans_le (min_le_right (-l) r)
      have hqSecond : (q.1.y - c) / q.1.x ∈ Ioo a b := by
        constructor
        · rw [lt_div_iff₀ hqData.1]
          linarith [hqData.2.2.1]
        · rw [div_lt_iff₀ hqData.1]
          linarith [hqData.2.2.2]
      have hqU : (q.1.x, (q.1.y - c) / q.1.x) ∈ U :=
        huv ⟨hlu hqFirst, habv hqSecond⟩
      simpa only [Set.mem_preimage, chartInv, if_pos hqData.1] using hqU
    · have hqData := mem_sheetStrip_iff.mp hqStrip
      have hqFirst : q.1.x ∈ Ioo l r := by
        constructor
        · have hεl : ε ≤ -l := min_le_left (-l) r
          linarith [hqData.2.1]
        · exact lt_of_le_of_lt hqData.2.2.1 hzero.2
      have hqU : (q.1.x, q.1.y) ∈ U :=
        huv ⟨hlu hqFirst, habv ⟨hqData.2.2.2.1, hqData.2.2.2.2⟩⟩
      have hqNot : ¬0 < q.1.x := not_lt_of_ge hqData.2.2.1
      simpa only [Set.mem_preimage, chartInv, if_neg hqNot] using hqU
  · let D : Set (ℝ × ℝ) := {r | 0 < r.1}
    let g : ℝ × ℝ → ℝ × ℝ := fun r ↦ (r.1, (r.2 - c) / r.1)
    have hD : IsOpen D := isOpen_lt continuous_const continuous_fst
    have hgSecond : ContinuousOn (fun r : ℝ × ℝ ↦ (r.2 - c) / r.1) D :=
      (continuousOn_snd.sub continuousOn_const).div continuousOn_fst
        (fun r hr ↦ ne_of_gt hr)
    have hg : ContinuousOn g D := continuousOn_fst.prodMk hgSecond
    have hW : IsOpen (D ∩ g ⁻¹' U) := hg.isOpen_inter_preimage hD hU
    have hpU : (p.1.x, (p.1.y - c) / p.1.x) ∈ U := by
      simpa only [Set.mem_preimage, chartInv, if_pos hpx] using hp
    have hpUpper : p ∈ Subtype.val ⁻¹' upperOpen (D ∩ g ⁻¹' U) := by
      apply mem_upperOpen_iff.mpr
      refine ⟨hpx, hpx, ?_⟩
      exact hpU
    have hUpperOpen : IsOpen (upperOpen (D ∩ g ⁻¹' U)) :=
      basis_isTopologicalBasis.isOpen
        (mem_basis_iff.mpr (Or.inl ⟨D ∩ g ⁻¹' U, hW, rfl⟩))
    refine Filter.mem_of_superset
      ((hUpperOpen.preimage continuous_subtype_val).mem_nhds hpUpper) ?_
    intro q hq
    have hqData := mem_upperOpen_iff.mp hq
    simpa only [Set.mem_preimage, chartInv, if_pos hqData.1] using hqData.2.2

/-- The source map `f_c` is a homeomorphism from `ℝ²` onto `A ∪ B_c`. -/
noncomputable def chart (c : ℝ) : (ℝ × ℝ) ≃ₜ chartRange c where
  toFun p := ⟨chartMap c p, chartMap_mem c p⟩
  invFun := chartInv c
  left_inv := chartInv_left c
  right_inv p := Subtype.ext (chartInv_right c p)
  continuous_toFun := continuous_chartMap c
  continuous_invFun := continuous_chartInv c

/-- The bundled chart has the exact piecewise underlying map specified in the exercise. -/
theorem chart_apply (c : ℝ) (p : ℝ × ℝ) : (chart c p).1 = chartMap c p := by
  rfl

/-- The chart range `A ∪ B_c` is open in the Prüfer manifold. -/
theorem chartRange_isOpen (c : ℝ) : IsOpen (chartRange c) := by
  -- At positive, negative, and boundary points choose the corresponding defining basis set.
  refine basis_isTopologicalBasis.isOpen_iff.mpr ?_
  intro p hp
  rcases lt_trichotomy p.x 0 with hpx | hpx | hpx
  · refine ⟨sheetInteriorOpen c Set.univ, ?_, ?_, ?_⟩
    · exact mem_basis_iff.mpr (Or.inr (Or.inl ⟨c, Set.univ, isOpen_univ, rfl⟩))
    · have hpz : p.z = c := (mem_chartRange_iff.mp hp).resolve_left (not_lt_of_ge hpx.le) |>.2
      exact mem_sheetInteriorOpen_iff.mpr ⟨hpz, hpx, Set.mem_univ _⟩
    · intro q hq
      exact mem_chartRange_iff.mpr
        (Or.inr ⟨le_of_lt (mem_sheetInteriorOpen_iff.mp hq).2.1,
          (mem_sheetInteriorOpen_iff.mp hq).1⟩)
  · refine ⟨gluingNeighborhood c (p.y - 1) (p.y + 1) 1, ?_, ?_, ?_⟩
    · have hInterval : p.y - 1 < p.y + 1 := by linarith
      have hRadius : (0 : ℝ) < 1 := by norm_num
      exact mem_basis_iff.mpr (Or.inr (Or.inr
        ⟨c, p.y - 1, p.y + 1, 1, hInterval, hRadius, rfl⟩))
    · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
      have hpz : p.z = c := (mem_chartRange_iff.mp hp).resolve_left (not_lt_of_ge hpx.le) |>.2
      have hLeft : (-1 : ℝ) < p.x := by linarith
      have hLower : p.y - 1 < p.y := by linarith
      have hUpper : p.y < p.y + 1 := by linarith
      exact Or.inr ⟨hpz, hLeft, hpx.le, hLower, hUpper⟩
    · intro q hq
      rcases mem_gluingNeighborhood_iff.mp hq with hq | hq
      · exact mem_chartRange_iff.mpr (Or.inl (mem_upperWedge_iff.mp hq).1)
      · exact mem_chartRange_iff.mpr
          (Or.inr ⟨(mem_sheetStrip_iff.mp hq).2.2.1, (mem_sheetStrip_iff.mp hq).1⟩)
  · refine ⟨upperOpen Set.univ, mem_basis_iff.mpr (Or.inl ⟨Set.univ, isOpen_univ, rfl⟩),
      mem_upperOpen_iff.mpr ⟨hpx, Set.mem_univ _⟩, ?_⟩
    intro q hq
    exact mem_chartRange_iff.mpr (Or.inl (mem_upperOpen_iff.mp hq).1)

/-- The standard homeomorphism from the coordinate plane to two-dimensional Euclidean space. -/
private noncomputable def planeHomeomorph : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph.symm

/-- The open chart range as an element of `TopologicalSpace.Opens PruferManifold`. -/
private def chartRangeOpen (c : ℝ) : TopologicalSpace.Opens PruferManifold :=
  ⟨chartRange c, chartRange_isOpen c⟩

/-- The chart on the Prüfer manifold indexed by the sheet coordinate `c`. -/
noncomputable def euclideanChart (c : ℝ) :
    OpenPartialHomeomorph PruferManifold (EuclideanSpace ℝ (Fin 2)) :=
  ((chartRangeOpen c).openPartialHomeomorphSubtypeCoe
      ⟨chartMap c (0, 0), chartMap_mem c (0, 0)⟩).symm.trans
    ((chart c).symm.toOpenPartialHomeomorph.transHomeomorph planeHomeomorph)

/-- Helper for Exercise 8.99.6: each point belongs to the source of its sheet chart. -/
lemma mem_euclideanChart_source (p : PruferManifold) :
    p ∈ (euclideanChart p.z).source := by
  -- The selected sheet chart contains every nonpositive point and every upper point.
  simp only [euclideanChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.symm_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · change p ∈ chartRange p.z
    rw [mem_chartRange_iff]
    rcases p.valid with hp | hp
    · exact Or.inl hp.1
    · exact Or.inr ⟨hp, rfl⟩
  · exact Set.mem_univ _

/-- The explicit sheet charts give the Prüfer manifold its canonical locally two-Euclidean
structure. -/
noncomputable instance instChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) PruferManifold where
  atlas := range euclideanChart
  chartAt p := euclideanChart p.z
  mem_chart_source := mem_euclideanChart_source
  chart_mem_atlas p := mem_range_self p.z

end PruferManifold
