import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open scoped Manifold ContDiff

universe uK uVE uVM uHE uHM uE uM uSheet

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable (IE : ModelWithCorners K VE HE) (IM : ModelWithCorners K VM HM)
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E] [IsManifold IE (∞ : ℕ∞ω) E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM (∞ : ℕ∞ω) M]

namespace Bundle.Trivialization

/-- Helper for Exercise 4.39: on one connected component of `pi ⁻¹' t.baseSet`, the sheet
coordinate of a trivialization is constant. -/
lemma sheet_coordinate_eq_on_component
    {pi : E → M} {Sheet : Type uSheet} [TopologicalSpace Sheet] [DiscreteTopology Sheet]
    (t : Trivialization Sheet pi)
    {e x : E} (he : e ∈ pi ⁻¹' t.baseSet)
    (hx : x ∈ connectedComponentIn (pi ⁻¹' t.baseSet) e) :
    (t x).2 = (t e).2 := by
  let s := connectedComponentIn (pi ⁻¹' t.baseSet) e
  have hs_subset : s ⊆ pi ⁻¹' t.baseSet := connectedComponentIn_subset _ _
  have hs_subset_source : s ⊆ t.source := by
    intro y hy
    exact t.mem_source.mpr (hs_subset hy)
  have hs_preconnected : IsPreconnected s := isPreconnected_connectedComponentIn
  let f : s → Sheet := s.restrict fun y : E => (t y).2
  -- The sheet coordinate is continuous on the component, hence locally constant.
  have hf_continuousOn : ContinuousOn (fun y : E => (t y).2) s := by
    exact continuous_snd.comp_continuousOn (t.continuousOn_toFun.mono hs_subset_source)
  have hf_continuous : Continuous f := by
    simpa [f, s] using hf_continuousOn.restrict
  have hf_locallyConstant : IsLocallyConstant f := by
    exact (IsLocallyConstant.iff_continuous f).2 hf_continuous
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs_preconnected
  have he_mem : e ∈ s := mem_connectedComponentIn he
  -- A locally constant map on a preconnected subtype is constant.
  simpa [f, s] using
    hf_locallyConstant.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨e, he_mem⟩

/-- Helper for Exercise 4.39: the fixed-sheet lift of any base point lies in the connected
component determined by `e`. -/
lemma fixed_sheet_lift_mem_component
    {pi : E → M} {Sheet : Type uSheet} [TopologicalSpace Sheet] [DiscreteTopology Sheet]
    (t : Trivialization Sheet pi) (hbase : IsPreconnected t.baseSet)
    {e : E} (he : e ∈ pi ⁻¹' t.baseSet)
    {b : M} (hb : b ∈ t.baseSet) :
    t.invFun (b, (t e).2) ∈ connectedComponentIn (pi ⁻¹' t.baseSet) e := by
  let lift : t.baseSet → E := fun y => t.invFun (y, (t e).2)
  have hlift_target : ∀ y : t.baseSet, ((y : M), (t e).2) ∈ t.target := by
    intro y
    exact t.mem_target.2 y.2
  -- The fixed-sheet section is continuous on the preconnected base set.
  have hlift_continuous : Continuous lift := by
    letI : PreconnectedSpace t.baseSet := Subtype.preconnectedSpace hbase
    have hcomp : Continuous fun y : t.baseSet => ((y : M), (t e).2) := by
      exact continuous_subtype_val.prodMk continuous_const
    have hmem : ∀ y : t.baseSet, ((y : M), (t e).2) ∈ t.target := hlift_target
    simpa [lift] using t.continuousOn_invFun.comp_continuous hcomp hmem
  let liftSet : Set E := Set.range lift
  have hlift_preconnected : IsPreconnected liftSet := by
    letI : PreconnectedSpace t.baseSet := Subtype.preconnectedSpace hbase
    have hpreconnected_univ : IsPreconnected (Set.univ : Set t.baseSet) := isPreconnected_univ
    simpa [liftSet, lift] using hpreconnected_univ.image lift hlift_continuous.continuousOn
  have he_mem_liftSet : e ∈ liftSet := by
    refine ⟨⟨pi e, he⟩, ?_⟩
    -- Over the chosen sheet index, the inverse trivialization sends `pi e` back to `e`.
    simpa [lift] using t.symm_apply_mk_proj (t.mem_source.mpr he)
  have hlift_subset : liftSet ⊆ pi ⁻¹' t.baseSet := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    -- Every point in the target lifts back into the source of the trivialization.
    simpa [lift] using t.mem_source.mp (t.map_target (hlift_target z))
  have hlift_component :
      liftSet ⊆ connectedComponentIn (pi ⁻¹' t.baseSet) e := by
    exact hlift_preconnected.subset_connectedComponentIn he_mem_liftSet hlift_subset
  have hb_mem_liftSet : t.invFun (b, (t e).2) ∈ liftSet := by
    exact ⟨⟨b, hb⟩, rfl⟩
  exact hlift_component hb_mem_liftSet

/-- Helper for Exercise 4.39: the projection is bijective from one connected component onto the
base set of the trivialization. -/
lemma component_bijOn_baseSet
    {pi : E → M} {Sheet : Type uSheet} [TopologicalSpace Sheet] [DiscreteTopology Sheet]
    (t : Trivialization Sheet pi) (hbase : IsPreconnected t.baseSet)
    {e : E} (he : e ∈ pi ⁻¹' t.baseSet) :
    Set.BijOn pi (connectedComponentIn (pi ⁻¹' t.baseSet) e) t.baseSet := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro x hx
    exact connectedComponentIn_subset (pi ⁻¹' t.baseSet) e hx
  · intro x hx y hy hxy
    have hx_source : x ∈ t.source := by
      exact t.mem_source.mpr (connectedComponentIn_subset (pi ⁻¹' t.baseSet) e hx)
    have hy_source : y ∈ t.source := by
      exact t.mem_source.mpr (connectedComponentIn_subset (pi ⁻¹' t.baseSet) e hy)
    have hx_sheet :
        (t x).2 = (t e).2 := sheet_coordinate_eq_on_component t he hx
    have hy_sheet :
        (t y).2 = (t e).2 := sheet_coordinate_eq_on_component t he hy
    -- Route correction: injectivity comes from rewriting both points into the same fixed sheet.
    have hx_repr : t.invFun (pi x, (t e).2) = x := by
      rw [← hx_sheet]
      simpa using t.symm_apply_mk_proj hx_source
    have hy_repr : t.invFun (pi y, (t e).2) = y := by
      rw [← hy_sheet]
      simpa using t.symm_apply_mk_proj hy_source
    calc
      x = t.invFun (pi x, (t e).2) := hx_repr.symm
      _ = t.invFun (pi y, (t e).2) := by rw [hxy]
      _ = y := hy_repr
  · intro b hb
    refine ⟨t.invFun (b, (t e).2), ?_, ?_⟩
    · exact fixed_sheet_lift_mem_component t hbase he hb
    · simpa using t.proj_symm_apply' (x := (t e).2) hb

-- Proof sketch: use the discrete trivialization to identify `pi ⁻¹' U` with `U × Sheet`;
-- preconnectedness of `U` forces the connected component of any `e ∈ pi ⁻¹' U` to be a single
-- sheet, and the ambient smooth local diffeomorphism property of `pi` restricts to that sheet.
/-- If `t` is a trivialization of a smooth local diffeomorphism over a preconnected base set, then
the restriction of `pi` to each connected component of the source over `t.baseSet` is bijective
onto `t.baseSet` and is still a smooth local diffeomorphism. -/
theorem component_isLocalDiffeomorphOn_and_bijOn
    {pi : E → M} {Sheet : Type uSheet} [TopologicalSpace Sheet] [DiscreteTopology Sheet]
    (t : Trivialization Sheet pi) (hpi : IsLocalDiffeomorph IE IM ∞ pi)
    (hbase : IsPreconnected t.baseSet)
    {e : E} (he : e ∈ pi ⁻¹' t.baseSet) :
    IsLocalDiffeomorphOn IE IM ∞ pi (connectedComponentIn (pi ⁻¹' t.baseSet) e) ∧
      Set.BijOn pi (connectedComponentIn (pi ⁻¹' t.baseSet) e) t.baseSet := by
  constructor
  · -- Restricting the domain does not change a pointwise local-diffeomorphism property.
    exact hpi.isLocalDiffeomorphOn _
  · -- The connected component is exactly one sheet over the preconnected base set.
    exact component_bijOn_baseSet t hbase he

end Bundle.Trivialization

/-- Exercise 4.39: if a preconnected open set `U` is topologically evenly covered by a smooth
local diffeomorphism `pi`, then the restriction of `pi` to each connected component of
`pi ⁻¹' U` is bijective onto `U` and is still a smooth local diffeomorphism. -/
theorem topological_evenly_covered_component_isLocalDiffeomorphOn_and_bijOn
    {pi : E → M} {U : Set M} (hpi : IsLocalDiffeomorph IE IM ∞ pi)
    {Sheet : Type uSheet} [TopologicalSpace Sheet] [DiscreteTopology Sheet]
    (t : Trivialization Sheet pi) (ht : t.baseSet = U) (hU : IsPreconnected U)
    {e : E} (he : e ∈ pi ⁻¹' U) :
    IsLocalDiffeomorphOn IE IM ∞ pi (connectedComponentIn (pi ⁻¹' U) e) ∧
      Set.BijOn pi (connectedComponentIn (pi ⁻¹' U) e) U := by
  subst ht
  simpa using Bundle.Trivialization.component_isLocalDiffeomorphOn_and_bijOn IE IM t hpi hU he
