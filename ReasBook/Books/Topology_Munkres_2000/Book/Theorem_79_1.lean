module

public import Topology_Munkres_2000.Book.Definition_79_1.Equiv
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v w

namespace IsCoveringMap

/-- Helper for Theorem 79.1: transporting the target basepoint along reflexivity does not change
the induced fundamental-group homomorphism. -/
private lemma fundamentalGroupMapOfEq_refl
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  -- Evaluate both homomorphisms on a loop class; reflexive endpoint transport is trivial.
  ext γ
  simp [FundamentalGroup.mapOfEq_apply]

/-- Helper for Theorem 79.1: an inclusion of transported fundamental-group ranges gives the
range inclusion required by the covering-space lifting criterion. -/
private lemma map_range_le_mapOfEq_range_of_fundamentalGroupMapRange_le
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (b₀ : B) (e₀ : E) (e₀' : E') (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h_range : hp.fundamentalGroupMapRange he₀ ≤ hp'.fundamentalGroupMapRange he₀') :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p', hp'.continuous⟩ (he₀'.trans he₀.symm)).range := by
  -- Move both selected fibers to the same literal basepoint, where the two range descriptions
  -- reduce to the same fundamental-group maps.
  subst b₀
  simpa only [fundamentalGroupMapRange, fundamentalGroupMapOfEq_refl] using h_range

/-- Helper for Theorem 79.1: mutually commuting lifts between connected covering spaces are
 two-sided inverses when they match at the selected basepoints. -/
private lemma mutualLifts_inverse
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PreconnectedSpace E] [PreconnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (h : C(E, E')) (k : C(E', E))
    (h_base : h e₀ = e₀') (k_base : k e₀' = e₀)
    (h_lifts : p' ∘ h = p) (k_lifts : p ∘ k = p') :
    Function.LeftInverse k h ∧ Function.RightInverse k h := by
  -- Uniqueness of lifts identifies the first composite with the identity on `E`.
  have kh_projection : p ∘ (k ∘ h) = p ∘ id := by
    funext e
    exact congrFun k_lifts (h e) |>.trans (congrFun h_lifts e)
  have kh_base : (k ∘ h) e₀ = id e₀ := by
    simp only [Function.comp_apply, id_eq, h_base, k_base]
  have kh_eq : k ∘ h = id :=
    hp.eq_of_comp_eq (k.continuous.comp h.continuous) continuous_id kh_projection e₀ kh_base
  -- The symmetric uniqueness argument identifies the other composite with the identity on `E'`.
  have hk_projection : p' ∘ (h ∘ k) = p' ∘ id := by
    funext e'
    exact congrFun h_lifts (k e') |>.trans (congrFun k_lifts e')
  have hk_base : (h ∘ k) e₀' = id e₀' := by
    simp only [Function.comp_apply, id_eq, k_base, h_base]
  have hk_eq : h ∘ k = id :=
    hp'.eq_of_comp_eq (h.continuous.comp k.continuous) continuous_id hk_projection e₀' hk_base
  constructor
  · intro e
    exact congrFun kh_eq e
  · intro e'
    exact congrFun hk_eq e'

/-- Helper for Theorem 79.1: mutually inverse continuous maps that commute with the projections
 determine an equivalence of maps into the common base. -/
private lemma equivalentOfContinuousMapInverses
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E']
    {p : E → B} {p' : E' → B} (h : C(E, E')) (k : C(E', E))
    (h_left : Function.LeftInverse k h) (h_right : Function.RightInverse k h)
    (h_commutes : p = p' ∘ h) : CoveringMap.Equivalent p p' := by
  -- Package the inverse laws first as an equivalence, then add continuity in both directions.
  let hEquiv : E ≃ E' :=
    { toFun := h
      invFun := k
      left_inv := h_left
      right_inv := h_right }
  let hHomeomorph : E ≃ₜ E' :=
    { hEquiv with
      continuous_toFun := h.continuous
      continuous_invFun := k.continuous }
  exact CoveringMap.equivalent_iff.mpr ⟨hHomeomorph, h_commutes⟩

/-- Theorem 79.1: covering projections with equal corresponding fundamental-group
subgroups are equivalent by a homeomorphism commuting with the projections. -/
theorem equivalent_of_fundamentalGroupMapRange_eq
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (b₀ : B) (e₀ : E) (e₀' : E') (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h_range : hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₀') :
    CoveringMap.Equivalent p p' := by
  -- Lift `p` through `p'` using the given equality of corresponding subgroups.
  have h_base_eq : p' e₀' = p e₀ := he₀'.trans he₀.symm
  have h_range_le :
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p', hp'.continuous⟩ h_base_eq).range :=
    map_range_le_mapOfEq_range_of_fundamentalGroupMapRange_le hp hp' b₀ e₀ e₀' he₀ he₀'
      h_range.le
  obtain ⟨h, h_spec, -⟩ :=
    hp'.existsUnique_continuousMap_lifts_of_range_le h_base_eq h_range_le
  -- Reverse the subgroup equality to construct a lift in the other direction.
  have k_base_eq : p e₀ = p' e₀' := he₀.trans he₀'.symm
  have k_range_le :
      (FundamentalGroup.map ⟨p', hp'.continuous⟩ e₀').range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ k_base_eq).range :=
    map_range_le_mapOfEq_range_of_fundamentalGroupMapRange_le hp' hp b₀ e₀' e₀ he₀' he₀
      h_range.ge
  obtain ⟨k, k_spec, -⟩ :=
    hp.existsUnique_continuousMap_lifts_of_range_le k_base_eq k_range_le
  -- Covering-map uniqueness makes the two lifts inverse, so they form the required homeomorphism.
  obtain ⟨h_left, h_right⟩ :=
    mutualLifts_inverse hp hp' e₀ e₀' h k h_spec.1 k_spec.1 h_spec.2 k_spec.2
  exact equivalentOfContinuousMapInverses h k h_left h_right h_spec.2.symm

end IsCoveringMap
