module

public import Topology_Munkres_2000.Book.Definition_79_1.Equiv
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
import Topology_Munkres_2000.Book.Lemma_79_1

public section

universe u v w

namespace FundamentalGroup

/-- Helper for Theorem 79.2: a reflexive endpoint identification in `mapOfEq` gives the
ordinary induced map. -/
private lemma mapOfEq_refl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  -- Compare the maps on loop classes and remove the reflexive endpoint transport.
  ext γ
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, map_apply]

end FundamentalGroup

namespace CoveringMap.Equiv

/-- Helper for Theorem 79.2: equivalences into one covering are determined by their value at
one point of a preconnected source. -/
private lemma eq_of_apply_eq
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PreconnectedSpace E] {p : E → B} {p' : E' → B} (hp' : IsCoveringMap p')
    (h k : CoveringMap.Equiv p p') (e : E)
    (he : h.toHomeomorph e = k.toHomeomorph e) : h = k := by
  -- Uniqueness of covering lifts first identifies the homeomorphisms pointwise.
  apply CoveringMap.Equiv.ext
  apply Homeomorph.ext
  exact congrFun (hp'.eq_of_comp_eq h.toHomeomorph.continuous k.toHomeomorph.continuous
    (h.commutes.symm.trans k.commutes) e he)

end CoveringMap.Equiv

namespace IsCoveringMap

/-- Helper for Theorem 79.2: unique pointed lifts between two coverings are classified by
inclusion of their pointed fundamental-group ranges. -/
private lemma existsUnique_pointedLift_iff_fundamentalGroupMapRange_le
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (b₀ : B) (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀) :
    (∃! h : C(E, E'), h e₀ = e₀' ∧ p' ∘ h = p) ↔
      hp.fundamentalGroupMapRange he₀ ≤ hp'.fundamentalGroupMapRange he₀' := by
  -- Move to a literal common basepoint and apply the general lifting lemma.
  subst b₀
  simpa only [fundamentalGroupMapRange, FundamentalGroup.mapOfEq_refl,
    ContinuousMap.coe_mk] using
    (existsUnique_continuousMap_lifts_iff_range_le
      p' hp' ⟨p, hp.continuous⟩ e₀ e₀' he₀')

/-- Helper for Theorem 79.2: a pointed continuous lift induces inclusion of the corresponding
fundamental-group ranges. -/
private lemma fundamentalGroupMapRange_le_of_pointedLift
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    {e₀ : E} {e₀' : E'} {b₀ : B} (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h : C(E, E')) (h_base : h e₀ = e₀') (h_lifts : p' ∘ h = p) :
    hp.fundamentalGroupMapRange he₀ ≤ hp'.fundamentalGroupMapRange he₀' := by
  -- The covering uniqueness theorem upgrades the supplied lift to the unique pointed lift.
  have h_spec : h e₀ = e₀' ∧ p' ∘ h = p := ⟨h_base, h_lifts⟩
  have h_unique : ∀ k : C(E, E'), k e₀ = e₀' ∧ p' ∘ k = p → k = h := by
    intro k hk
    apply ContinuousMap.ext
    exact congrFun (hp'.eq_of_comp_eq k.continuous h.continuous
      (hk.2.trans h_lifts.symm) e₀ (hk.1.trans h_base.symm))
  have h_existsUnique : ∃! k : C(E, E'), k e₀ = e₀' ∧ p' ∘ k = p :=
    ExistsUnique.intro h h_spec h_unique
  exact (existsUnique_pointedLift_iff_fundamentalGroupMapRange_le
    hp hp' e₀ e₀' b₀ he₀ he₀').mp h_existsUnique

/-- Helper for Theorem 79.2: a pointed equivalence of connected coverings identifies their
fundamental-group ranges. -/
private lemma fundamentalGroupMapRange_eq_of_pointedEquiv
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    {e₀ : E} {e₀' : E'} {b₀ : B} (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h : CoveringMap.Equiv p p') (h_base : h.toHomeomorph e₀ = e₀') :
    hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₀' := by
  -- The equivalence and its inverse give the two subgroup inclusions.
  let hMap : C(E, E') := ⟨h.toHomeomorph, h.toHomeomorph.continuous⟩
  let kMap : C(E', E) := ⟨h.toHomeomorph.symm, h.toHomeomorph.symm.continuous⟩
  have hMap_base : hMap e₀ = e₀' := h_base
  have hMap_lifts : p' ∘ hMap = p := h.commutes.symm
  have kMap_base : kMap e₀' = e₀ := by
    rw [← h_base]
    exact h.toHomeomorph.symm_apply_apply e₀
  have kMap_lifts : p ∘ kMap = p' := h.symm_commutes.symm
  apply le_antisymm
  · exact fundamentalGroupMapRange_le_of_pointedLift
      hp hp' he₀ he₀' hMap hMap_base hMap_lifts
  · exact fundamentalGroupMapRange_le_of_pointedLift
      hp' hp he₀' he₀ kMap kMap_base kMap_lifts

/-- Helper for Theorem 79.2: mutually pointed lifts between connected coverings are inverse
functions. -/
private lemma mutualPointedLifts_inverse
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PreconnectedSpace E] [PreconnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (h : C(E, E')) (k : C(E', E))
    (h_base : h e₀ = e₀') (k_base : k e₀' = e₀)
    (h_lifts : p' ∘ h = p) (k_lifts : p ∘ k = p') :
    Function.LeftInverse k h ∧ Function.RightInverse k h := by
  -- Uniqueness identifies `k ∘ h` with the identity on the first covering.
  have kh_projection : p ∘ (k ∘ h) = p ∘ id := by
    funext e
    exact congrFun k_lifts (h e) |>.trans (congrFun h_lifts e)
  have kh_base : (k ∘ h) e₀ = id e₀ := by
    simp only [Function.comp_apply, id_eq, h_base, k_base]
  have kh_eq : k ∘ h = id :=
    hp.eq_of_comp_eq (k.continuous.comp h.continuous) continuous_id kh_projection e₀ kh_base
  -- The symmetric uniqueness argument identifies `h ∘ k` with the other identity.
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

/-- Helper for Theorem 79.2: equality of pointed fundamental-group ranges constructs a pointed
equivalence of the corresponding connected coverings. -/
private lemma exists_pointedEquiv_of_fundamentalGroupMapRange_eq
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (b₀ : B) (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h_range : hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₀') :
    ∃ h : CoveringMap.Equiv p p', h.toHomeomorph e₀ = e₀' := by
  -- The two subgroup inclusions produce pointed lifts in opposite directions.
  obtain ⟨h, h_spec, -⟩ :=
    (existsUnique_pointedLift_iff_fundamentalGroupMapRange_le
      hp hp' e₀ e₀' b₀ he₀ he₀').mpr h_range.le
  obtain ⟨k, k_spec, -⟩ :=
    (existsUnique_pointedLift_iff_fundamentalGroupMapRange_le
      hp' hp e₀' e₀ b₀ he₀' he₀).mpr h_range.ge
  -- Uniqueness makes the lifts inverse, allowing them to be packaged as a homeomorphism.
  obtain ⟨h_left, h_right⟩ := mutualPointedLifts_inverse
    hp hp' e₀ e₀' h k h_spec.1 k_spec.1 h_spec.2 k_spec.2
  let hEquiv : E ≃ E' :=
    { toFun := h
      invFun := k
      left_inv := h_left
      right_inv := h_right }
  let hHomeomorph : E ≃ₜ E' :=
    { hEquiv with
      continuous_toFun := h.continuous
      continuous_invFun := k.continuous }
  have h_commutes : p = p' ∘ hHomeomorph := h_spec.2.symm
  let hCoveringEquiv : CoveringMap.Equiv p p' :=
    { toHomeomorph := hHomeomorph
      commutes := h_commutes }
  have hCoveringEquiv_base : hCoveringEquiv.toHomeomorph e₀ = e₀' := h_spec.1
  exact ⟨hCoveringEquiv, hCoveringEquiv_base⟩

/-- Theorem 79.2. Two pointed connected covering maps are uniquely equivalent over the base
exactly when their induced fundamental-group ranges agree. -/
theorem existsUnique_equiv_iff_fundamentalGroupMapRange_eq
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    (p : E → B) (p' : E' → B) (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (b₀ : B) (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀) :
    (∃! h : CoveringMap.Equiv p p', h.toHomeomorph e₀ = e₀') ↔
      hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₀' := by
  constructor
  · rintro ⟨h, h_base, -⟩
    -- A pointed equivalence and its inverse give equality of the two subgroup ranges.
    exact fundamentalGroupMapRange_eq_of_pointedEquiv hp hp' he₀ he₀' h h_base
  · intro h_range
    -- Mutual pointed lifts supply existence; lift uniqueness supplies the outer uniqueness.
    obtain ⟨h, h_base⟩ := exists_pointedEquiv_of_fundamentalGroupMapRange_eq
      hp hp' e₀ e₀' b₀ he₀ he₀' h_range
    refine ExistsUnique.intro h h_base ?_
    intro k k_base
    exact CoveringMap.Equiv.eq_of_apply_eq hp' k h e₀ (k_base.trans h_base.symm)

end IsCoveringMap
