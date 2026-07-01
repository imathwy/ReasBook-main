import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

noncomputable section

section InducedFromSubrepresentation

variable {k : Type u} {G : Type v} [Semiring k] [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (H : Subgroup G)
variable (W : Subrepresentation (ρ.comp H.subtype))

/-- If two elements of `G` lie in the same left coset of `H`, then they send an `H`-stable
submodule `W` to the same submodule of `V`. -/
-- Proof sketch: from the left-coset relation write one representative as the other multiplied by
-- an element of `H`; because `W` is stable under the restricted action of `H`, applying that
-- element preserves `W`, so mapping `W` by the two operators gives the same image.
private theorem leftQuotientSubmodule_eq_of_leftRel {s t : G}
    (hst : QuotientGroup.leftRel H s t) :
    W.toSubmodule.map (ρ s) = W.toSubmodule.map (ρ t) := by
  rw [le_antisymm_iff]
  constructor
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    -- Replace the representative `s` by `t = s * h`; this is the coset-change step.
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h⁻¹ w, W.apply_mem_toSubmodule h⁻¹ hw, ?_⟩
    -- The inverse subgroup element sends the witness back into `W`, so the image is unchanged.
    change ρ t (ρ h⁻¹ w) = ρ s w
    calc
      ρ t (ρ h⁻¹ w) = ρ (s * h) (ρ h⁻¹ w) := by
        congr 1
        simp [h]
      _ = ρ s (ρ h (ρ h⁻¹ w)) := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ s w := by
        simp
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    -- The reverse inclusion uses the same subgroup element to move the witness back.
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h w, W.apply_mem_toSubmodule h hw, ?_⟩
    change ρ s (ρ h w) = ρ t w
    calc
      ρ s (ρ h w) = ρ (s * h) w := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ t w := by
        congr 1
        simp [h]

/-- The family of translates of `W` indexed by the left cosets `G ⧸ H`. -/
def leftQuotientSubmodule : G ⧸ H → Submodule k V :=
  Quotient.lift
    (fun g : G ↦ W.toSubmodule.map (ρ g))
    (fun _ _ h ↦ leftQuotientSubmodule_eq_of_leftRel ρ H W h)

@[simp] theorem leftQuotientSubmodule_mk (g : G) :
    ρ.leftQuotientSubmodule H W (g : G ⧸ H) = W.toSubmodule.map (ρ g) :=
  rfl

/-- Definition 3-3.3-1: the representation `ρ` is induced by the restricted representation on an
`H`-stable subspace `W` when the transported subspaces indexed by the left cosets `G ⧸ H` are
the summands of an internal direct sum decomposition of `V`. -/
def IsInducedFromSubrepresentation : Prop :=
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  DirectSum.IsInternal (ρ.leftQuotientSubmodule H W)

end InducedFromSubrepresentation

section IsMonomial

variable {k : Type u} {G : Type v} [DivisionRing k] [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- A representation is monomial if it is induced from a one-dimensional subrepresentation of a
subgroup. -/
def IsMonomial (ρ : Representation k G V) : Prop :=
  ∃ H : Subgroup G, ∃ W : Subrepresentation (ρ.comp H.subtype),
    Module.finrank k W.toSubmodule = 1 ∧
      ρ.IsInducedFromSubrepresentation H W

end IsMonomial

end

end Representation
