module

public import Mathlib.Topology.UnitInterval

public section

universe u

namespace unitInterval

/-- Helper for Definition 61.2: deleting a point from `unitInterval` leaves a connected
set exactly when the point is an endpoint. -/
lemma isConnected_compl_singleton_iff (p : unitInterval) :
    IsConnected (({p} : Set unitInterval)ᶜ) ↔ p = 0 ∨ p = 1 := by
  constructor
  · intro hp
    -- If the deleted point were interior, connectedness would force the deleted point
    -- to lie in its own complement.
    by_contra hp_endpoint
    rw [not_or] at hp_endpoint
    have hzero : (0 : unitInterval) ∈ (({p} : Set unitInterval)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h ↦ hp_endpoint.1 h.symm
    have hone : (1 : unitInterval) ∈ (({p} : Set unitInterval)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h ↦ hp_endpoint.2 h.symm
    have hp_mem : p ∈ Set.Icc (0 : unitInterval) 1 := ⟨bot_le, le_top⟩
    have hp_compl := hp.Icc_subset hzero hone hp_mem
    exact hp_compl (Set.mem_singleton_iff.mpr rfl)
  · rintro (rfl | rfl)
    · -- Removing `0` leaves the half-open interval `(0, 1]`.
      have hcompl : (({0} : Set unitInterval)ᶜ) = Set.Ioc 0 1 := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ioc]
        constructor
        · intro hx
          exact ⟨unitInterval.pos_iff_ne_zero.mpr hx, unitInterval.le_one'⟩
        · intro hx
          exact unitInterval.pos_iff_ne_zero.mp hx.1
      rw [hcompl]
      exact isConnected_Ioc zero_lt_one
    · -- Removing `1` leaves the half-open interval `[0, 1)`.
      have hcompl : (({1} : Set unitInterval)ᶜ) = Set.Ico 0 1 := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ico]
        constructor
        · intro hx
          exact ⟨unitInterval.nonneg', unitInterval.lt_one_iff_ne_one.mpr hx⟩
        · intro hx
          exact unitInterval.lt_one_iff_ne_one.mp hx.2
      rw [hcompl]
      exact isConnected_Ico zero_lt_one

end unitInterval

namespace Topology

/-- An arc is a topological space homeomorphic to the unit interval. -/
class IsArc (X : Type u) [TopologicalSpace X] : Prop where
  /-- An arc admits a homeomorphism to the unit interval. -/
  homeomorphic_unitInterval : Nonempty (X ≃ₜ unitInterval)

namespace IsArc

/-- An endpoint of an arc is a point whose singleton complement is connected. -/
def IsEndpoint {X : Type u} [TopologicalSpace X] [IsArc X] (p : X) : Prop :=
  IsConnected (({p} : Set X)ᶜ)

/-- An interior point of an arc is a point that is not an endpoint. -/
def IsInteriorPoint {X : Type u} [TopologicalSpace X] [IsArc X] (p : X) : Prop :=
  ¬ IsEndpoint p

/-- A space is an arc exactly when it is homeomorphic to the unit interval. -/
theorem iff_nonempty_homeomorph_unitInterval (X : Type u) [TopologicalSpace X] :
    IsArc X ↔ Nonempty (X ≃ₜ unitInterval) := by
  constructor
  · exact fun h ↦ h.homeomorphic_unitInterval
  · exact fun h ↦ ⟨h⟩

/-- Definition 61.2: under coordinates on an arc, its endpoints are exactly the points
corresponding to `0` and `1`. -/
theorem isEndpoint_iff {X : Type u} [TopologicalSpace X] [IsArc X]
    (e : X ≃ₜ unitInterval) (p : X) :
    IsEndpoint p ↔ p = e.symm 0 ∨ p = e.symm 1 := by
  -- Transport the punctured arc to the corresponding punctured unit interval.
  rw [IsEndpoint, ← e.isConnected_image, e.image_compl, Set.image_singleton,
    unitInterval.isConnected_compl_singleton_iff]
  -- Translate the two endpoint equations back through the coordinate homeomorphism.
  have coordinate_eq (x : unitInterval) : e p = x ↔ p = e.symm x :=
    e.toEquiv.apply_eq_iff_eq_symm_apply
  rw [coordinate_eq 0, coordinate_eq 1]

/-- Under coordinates on an arc, the interior points are those distinct from both endpoints. -/
theorem isInteriorPoint_iff {X : Type u} [TopologicalSpace X] [IsArc X]
    (e : X ≃ₜ unitInterval) (p : X) :
    IsInteriorPoint p ↔ p ≠ e.symm 0 ∧ p ≠ e.symm 1 := by
  -- Interior points are precisely the negation of the two endpoint alternatives.
  rw [IsInteriorPoint, isEndpoint_iff e p, not_or]

end IsArc

end Topology

namespace unitInterval

/-- The unit interval is an arc. -/
instance instIsArc : Topology.IsArc unitInterval :=
  ⟨⟨Homeomorph.refl unitInterval⟩⟩

end unitInterval
