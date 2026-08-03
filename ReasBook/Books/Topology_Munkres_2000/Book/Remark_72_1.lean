module

public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles
import all Topology_Munkres_2000.Book.Example_22_5.Torus
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

namespace unitInterval

/-- Helper for Remark 72.1: a point of `unitInterval` maps to zero in `UnitAddCircle`
exactly when it is an endpoint. -/
theorem coe_eq_zero_iff (x : unitInterval) :
    (x : UnitAddCircle) = 0 ↔ x = 0 ∨ x = 1 := by
  -- Use the canonical half-open representative theorem for `AddCircle`.
  constructor
  · intro hx
    by_cases hx_one : x = 1
    · exact Or.inr hx_one
    · have hx_lt_one : (x : ℝ) < 1 :=
        lt_of_le_of_ne (unitInterval.le_one x) (unitInterval.coe_ne_one.mpr hx_one)
      have hx_mem : (x : ℝ) ∈ Set.Ico 0 1 := ⟨unitInterval.nonneg x, hx_lt_one⟩
      have hx_zero : (x : ℝ) = 0 :=
        (AddCircle.coe_eq_zero_iff_of_mem_Ico hx_mem).mp hx
      exact Or.inl (Subtype.ext hx_zero)
  · intro hx
    rcases hx with hx_zero | hx_one
    · subst x
      exact AddCircle.coe_zero (1 : ℝ)
    · subst x
      exact AddCircle.coe_period (1 : ℝ)

/-- Helper for Remark 72.1: coercion to `UnitAddCircle` is injective away from the upper
endpoint of `unitInterval`. -/
theorem coe_eq_coe_of_ne_one {x y : unitInterval} (hx : x ≠ 1) (hy : y ≠ 1)
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) : x = y := by
  -- Put both representatives in `[0, 1)` and use injectivity of the quotient map there.
  have hx_lt_one : (x : ℝ) < 1 :=
    lt_of_le_of_ne (unitInterval.le_one x) (unitInterval.coe_ne_one.mpr hx)
  have hy_lt_one : (y : ℝ) < 1 :=
    lt_of_le_of_ne (unitInterval.le_one y) (unitInterval.coe_ne_one.mpr hy)
  have hx_lt_sum : (x : ℝ) < 0 + 1 := by
    simpa only [zero_add] using hx_lt_one
  have hy_lt_sum : (y : ℝ) < 0 + 1 := by
    simpa only [zero_add] using hy_lt_one
  have hx_mem : (x : ℝ) ∈ Set.Ico 0 (0 + 1) := by
    exact ⟨unitInterval.nonneg x, hx_lt_sum⟩
  have hy_mem : (y : ℝ) ∈ Set.Ico 0 (0 + 1) := by
    exact ⟨unitInterval.nonneg y, hy_lt_sum⟩
  exact Subtype.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ico hx_mem hy_mem).mp hxy)

end unitInterval

namespace TorusSquare

/-- The four-edge boundary of the unit square. -/
def boundary : Set (unitInterval × unitInterval) :=
  {point | point.1 = 0 ∨ point.1 = 1 ∨ point.2 = 0 ∨ point.2 = 1}

/-- Membership in the four-edge boundary of the unit square. -/
theorem mem_boundary_iff (point : unitInterval × unitInterval) :
    point ∈ boundary ↔
      point.1 = 0 ∨ point.1 = 1 ∨ point.2 = 0 ∨ point.2 = 1 := by
  rfl

/-- The union of the two coordinate circles in the torus. -/
def axes : Set (UnitAddCircle × UnitAddCircle) :=
  Set.univ ×ˢ {(0 : UnitAddCircle)} ∪ {(0 : UnitAddCircle)} ×ˢ Set.univ

/-- Membership in the union of the two coordinate circles. -/
theorem mem_axes_iff (point : UnitAddCircle × UnitAddCircle) :
    point ∈ axes ↔ point.2 = 0 ∨ point.1 = 0 := by
  simp [axes]

/-- The two coordinate circles, regarded as subspaces of their union. -/
def circles : Fin 2 → Set axes
  | 0 => {point | point.1.2 = 0}
  | 1 => {point | point.1.1 = 0}

/-- The origin of the torus lies in the union of its coordinate circles. -/
theorem origin_mem_axes : ((0 : UnitAddCircle), (0 : UnitAddCircle)) ∈ axes := by
  simp [axes]

/-- The common basepoint of the two coordinate circles. -/
def basepoint : axes :=
  ⟨((0 : UnitAddCircle), (0 : UnitAddCircle)), origin_mem_axes⟩

/-- Helper for Remark 72.1: the canonical square map is coordinatewise coercion into
`UnitAddCircle × UnitAddCircle`. -/
theorem toTorus_apply (point : unitInterval × unitInterval) :
    toTorus point = ((point.1 : UnitAddCircle), (point.2 : UnitAddCircle)) := by
  -- Record the coordinate formula once, after locally exposing the direct dependency.
  rfl

/-- Helper for Remark 72.1: the inverse image of the coordinate axes is precisely the
boundary of the unit square. -/
theorem toTorus_preimage_axes : toTorus ⁻¹' axes = boundary := by
  -- Normalize both coordinate-circle conditions to endpoint conditions in the square.
  ext point
  rw [Set.mem_preimage, mem_axes_iff, toTorus_apply, mem_boundary_iff]
  simp only [unitInterval.coe_eq_zero_iff]
  tauto

/-- Remark 72.1: The square boundary maps onto the union of the coordinate circles. -/
theorem boundary_image : toTorus '' boundary = axes := by
  -- Replace the boundary by the exact preimage bridge, then use quotient-map surjectivity.
  calc
    toTorus '' boundary = toTorus '' (toTorus ⁻¹' axes) :=
      congrArg (Set.image toTorus) toTorus_preimage_axes.symm
    _ = axes := Set.image_preimage_eq axes toTorus_isQuotientMap.surjective

/-- Helper for Remark 72.1: each coordinate circle in `axes` is homeomorphic to `Circle`. -/
private theorem coordinateCircleHomeomorphicCircle (i : Fin 2) :
    Nonempty (circles i ≃ₜ Circle) := by
  -- Identify each nested coordinate-circle subtype with its direct ambient product set.
  fin_cases i
  · let horizontal : Set (UnitAddCircle × UnitAddCircle) :=
      Set.univ ×ˢ {(0 : UnitAddCircle)}
    have hsubset : horizontal ⊆ Set.range (Subtype.val : axes → UnitAddCircle × UnitAddCircle) := by
      intro point hpoint
      refine ⟨⟨point, ?_⟩, rfl⟩
      rw [mem_axes_iff]
      exact Or.inl hpoint.2
    have hpreimage : circles 0 = Subtype.val ⁻¹' horizontal := by
      ext point
      simp only [circles, Set.mem_setOf_eq, Set.mem_preimage, horizontal,
        Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
    let restriction : circles 0 ≃ₜ horizontal :=
      (Homeomorph.setCongr hpreimage).trans
        (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsubset)
    let split := Homeomorph.Set.prod (Set.univ : Set UnitAddCircle) ({0} : Set UnitAddCircle)
    let discard := Homeomorph.prodUnique (Set.univ : Set UnitAddCircle)
      ({0} : Set UnitAddCircle)
    let univCircle := (Homeomorph.Set.univ UnitAddCircle).trans
      (AddCircle.homeomorphCircle one_ne_zero)
    exact ⟨restriction.trans (split.trans (discard.trans univCircle))⟩
  · let vertical : Set (UnitAddCircle × UnitAddCircle) :=
      {(0 : UnitAddCircle)} ×ˢ Set.univ
    have hsubset : vertical ⊆ Set.range (Subtype.val : axes → UnitAddCircle × UnitAddCircle) := by
      intro point hpoint
      refine ⟨⟨point, ?_⟩, rfl⟩
      rw [mem_axes_iff]
      exact Or.inr hpoint.1
    have hpreimage : circles 1 = Subtype.val ⁻¹' vertical := by
      ext point
      simp only [circles, Set.mem_setOf_eq, Set.mem_preimage, vertical,
        Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, and_true]
    let restriction : circles 1 ≃ₜ vertical :=
      (Homeomorph.setCongr hpreimage).trans
        (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsubset)
    let split := Homeomorph.Set.prod ({0} : Set UnitAddCircle) (Set.univ : Set UnitAddCircle)
    let discard := Homeomorph.uniqueProd ({0} : Set UnitAddCircle)
      (Set.univ : Set UnitAddCircle)
    let univCircle := (Homeomorph.Set.univ UnitAddCircle).trans
      (AddCircle.homeomorphCircle one_ne_zero)
    exact ⟨restriction.trans (split.trans (discard.trans univCircle))⟩

/-- Helper for Remark 72.1: the two coordinate circles form a finite wedge at `basepoint`. -/
private theorem isFiniteWedgeOfCoordinateCircles :
    Topology.IsFiniteWedgeOfCircles circles basepoint := by
  -- Verify coverage, the circle models, and the single nontrivial intersection.
  apply Topology.IsFiniteWedgeOfCircles.of
  · ext point
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases (mem_axes_iff point.1).mp point.property with hsecond | hfirst
    · exact ⟨0, hsecond⟩
    · exact ⟨1, hfirst⟩
  · exact coordinateCircleHomeomorphicCircle
  · intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · ext point
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · intro hpoint
          apply Subtype.ext
          exact Prod.ext hpoint.2 hpoint.1
        · intro hpoint
          subst point
          exact ⟨rfl, rfl⟩
    · fin_cases j
      · ext point
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · intro hpoint
          apply Subtype.ext
          exact Prod.ext hpoint.1 hpoint.2
        · intro hpoint
          subst point
          exact ⟨rfl, rfl⟩
      · exact (hij rfl).elim

/-- Companion to Remark 72.1: The two coordinate circles form a wedge at their common
basepoint. -/
instance instIsWedgeOfCircles :
    Topology.IsWedgeOfCircles circles basepoint := by
  -- Promote the verified finite wedge through the canonical coherence theorem.
  exact Topology.IsWedgeOfCircles.ofFinite isFiniteWedgeOfCoordinateCircles

/-- Helper for Remark 72.1: `toTorus` is injective away from the square boundary. -/
private theorem toTorusInjOnInterior : Set.InjOn toTorus boundaryᶜ := by
  -- Interior points lie in the half-open representative square, where each coordinate is unique.
  intro point hpoint point' hpoint' heq
  have hfirst_ne_one : point.1 ≠ 1 := by
    intro hfirst
    apply hpoint
    exact (mem_boundary_iff point).mpr (Or.inr (Or.inl hfirst))
  have hfirst'_ne_one : point'.1 ≠ 1 := by
    intro hfirst
    apply hpoint'
    exact (mem_boundary_iff point').mpr (Or.inr (Or.inl hfirst))
  have hsecond_ne_one : point.2 ≠ 1 := by
    intro hsecond
    apply hpoint
    exact (mem_boundary_iff point).mpr (Or.inr (Or.inr (Or.inr hsecond)))
  have hsecond'_ne_one : point'.2 ≠ 1 := by
    intro hsecond
    apply hpoint'
    exact (mem_boundary_iff point').mpr (Or.inr (Or.inr (Or.inr hsecond)))
  rw [toTorus_apply point, toTorus_apply point'] at heq
  exact Prod.ext
    (unitInterval.coe_eq_coe_of_ne_one hfirst_ne_one hfirst'_ne_one
      (congrArg Prod.fst heq))
    (unitInterval.coe_eq_coe_of_ne_one hsecond_ne_one hsecond'_ne_one
      (congrArg Prod.snd heq))

/-- Companion to Remark 72.1: The complement of the square boundary maps bijectively onto
the complement of the coordinate circles. -/
theorem interior_bijOn : Set.BijOn toTorus boundaryᶜ axesᶜ := by
  -- The exact preimage bridge gives complement mapping, and boundary mapping plus global
  -- surjectivity gives complement surjectivity.
  have hboundary_maps : Set.MapsTo toTorus boundary axes := by
    rw [Set.mapsTo_iff_image_subset]
    exact boundary_image.le
  refine Set.BijOn.mk ?_ toTorusInjOnInterior ?_
  · intro point hpoint haxes
    apply hpoint
    have hpreimage : point ∈ toTorus ⁻¹' axes := haxes
    rwa [toTorus_preimage_axes] at hpreimage
  · exact hboundary_maps.surjOn_compl toTorus_isQuotientMap.surjective

end TorusSquare

end
