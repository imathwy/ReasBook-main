import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {R : Type*} [Zero R] [LE R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.7.10 introduces the normal cone to a set `C` at a point `a`,
  equivalently the set of dual vectors whose pairings with all displacements `x - a` into `C` are
  nonpositive, with the base-point feasibility condition `a ∈ C` built into the owner so that the
  normal cone is empty off `C`.
- `core/canonical`: the primitive owner data are the source-facing inequalities
  `∀ x ∈ C, 0 ≤ ⟪a - x, x⋆⟫` together with feasibility `a ∈ C`; this keeps the declaration at the
  weakest statement layer needed to define the notion.
- `bridge/view`: under stronger ordered-ring assumptions, `normalCone C a` is exactly the canonical
  dual cone `PointedCone.dual p ((a - ·) '' C)` with the same feasibility condition.
- Primitive data vs derived API: the primitive public owner is the set `normalCone C a`; the
  bridge to `PointedCone.dual` and the companion pointwise-sign theorem
  `mem_normalCone_iff_sub_nonpos` are derived API.
- Ambient structure: the owner uses only subtraction in `M`, a raw pairing `HasPairing M N R`,
  and ordered-zero data on `R`.
- Domain-style sampling: the relevant declarations are `HasPairing`, `HasLinearPairing`,
  `PointedCone.dual`, `PointedCone.mem_dual`, and the adjacent bounded dual owner `barrierCone`.
- Layer target: `source-facing`.
-/
/-- Definition 2.7.10: the normal cone to a set `C` at a point `a`, written `N(a | C)` after
`open scoped Rockafellar`, as a source-facing feasible-point inequality owner. -/
def normalCone (C : Set M) (a : M) : Set N :=
  {xStar | a ∈ C ∧ ∀ x ∈ C, 0 ≤ (⟪a - x, xStar⟫ₚ : R)}

end

/-- Explicit normal-cone notation when both pairing codomain and dual carrier must be fixed. -/
scoped[Rockafellar] notation3:max "N[" R_ "," N_ "](" a " | " C ")" =>
  normalCone (R := R_) (N := N_) C a

/-- Explicit normal-cone notation when only the pairing codomain must be fixed. -/
scoped[Rockafellar] notation3:max "N[" R_ "](" a " | " C ")" =>
  normalCone (R := R_) C a

/-- Canonical source-facing normal-cone notation when the ambient pairing data are inferable. -/
scoped[Rockafellar] notation3:max "N(" a " | " C ")" => normalCone C a

section

universe u

variable {R : Type*} [Zero R] [LE R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R]

open scoped Rockafellar

/-- Membership in the normal cone is exactly the source-facing feasibility-plus-inequality
condition. -/
@[simp] theorem mem_normalCone_iff {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ ∀ x ∈ C, 0 ≤ (⟪a - x, xStar⟫ₚ : R) :=
  Iff.rfl

end

section

universe u

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type u} {N : Type*}
variable [AddCommMonoid M] [Sub M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [HasLinearPairing M N R]

open scoped Rockafellar

local notation "p" => (HasLinearPairing.pairingLinear : M →ₗ[R] N →ₗ[R] R)

/-- Bridge to the canonical dual-cone owner: over an ordered semiring, the source-facing normal
cone is exactly the feasible-point view of the dual cone of displacement vectors. -/
theorem mem_normalCone_iff_mem_dual_displacement {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ xStar ∈ PointedCone.dual p ((a - ·) '' C) := by
  constructor
  · rintro ⟨ha, hineq⟩
    refine ⟨ha, ?_⟩
    rw [PointedCone.mem_dual]
    intro y hy
    rcases hy with ⟨x, hxC, rfl⟩
    exact hineq x hxC
  · rintro ⟨ha, hdual⟩
    refine ⟨ha, ?_⟩
    intro x hxC
    exact (PointedCone.mem_dual.mp hdual) ⟨x, hxC, rfl⟩

end

section

universe u

variable {R : Type*} [Preorder R] [AddGroup R] [AddLeftMono R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R] [HasPairingSubLeft M N R]

open scoped Rockafellar

/-- Additive-order companion view: membership in the normal cone is equivalent to the textbook
nonpositivity condition on displacements `x - a`, with only the additive order data needed for the
sign flip. -/
theorem mem_normalCone_iff_sub_nonpos {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ ∀ x ∈ C, (⟪x - a, xStar⟫ₚ : R) ≤ 0 := by
  rw [mem_normalCone_iff]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun x hx => ?_⟩
    have hsub : (⟪a - x, xStar⟫ₚ : R) = - (⟪x - a, xStar⟫ₚ : R) := by
      calc
        (⟪a - x, xStar⟫ₚ : R) = (⟪a, xStar⟫ₚ : R) - (⟪x, xStar⟫ₚ : R) :=
          HasPairingSubLeft.pairing_sub_left a x xStar
        _ = -((⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R)) := by
            simp [sub_eq_add_neg]
        _ = - (⟪x - a, xStar⟫ₚ : R) := by
            rw [HasPairingSubLeft.pairing_sub_left x a xStar]
    have h' : 0 ≤ (-(⟪x - a, xStar⟫ₚ : R)) := by
      simpa [hsub] using h x hx
    exact neg_nonneg.mp h'
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun x hx => ?_⟩
    have hsub : (⟪a - x, xStar⟫ₚ : R) = - (⟪x - a, xStar⟫ₚ : R) := by
      calc
        (⟪a - x, xStar⟫ₚ : R) = (⟪a, xStar⟫ₚ : R) - (⟪x, xStar⟫ₚ : R) :=
          HasPairingSubLeft.pairing_sub_left a x xStar
        _ = -((⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R)) := by
            simp [sub_eq_add_neg]
        _ = - (⟪x - a, xStar⟫ₚ : R) := by
            rw [HasPairingSubLeft.pairing_sub_left x a xStar]
    have h' : 0 ≤ (-(⟪x - a, xStar⟫ₚ : R)) := neg_nonneg.mpr (h x hx)
    simpa [hsub] using h'

variable [AddRightMono R]

/-- A normal vector at `a` defines a pairing functional whose supremum on `C` is attained at
`a`. -/
theorem isMaxOn_pairing_of_mem_normalCone {C : Set M} {a : M} {xStar : N}
    (hxStar : xStar ∈ N[R](a | C)) :
    IsMaxOn (fun x : M ↦ (⟪x, xStar⟫ₚ : R)) C a := by
  rcases (mem_normalCone_iff_sub_nonpos.mp hxStar) with ⟨_, hxStar_nonpos⟩
  rw [isMaxOn_iff]
  intro x hxC
  have hsub : (⟪x - a, xStar⟫ₚ : R) = (⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R) :=
    HasPairingSubLeft.pairing_sub_left x a xStar
  have hle : (⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R) ≤ 0 := by
    simpa [hsub] using hxStar_nonpos x hxC
  exact sub_nonpos.mp hle

end
