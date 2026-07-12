import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import Mathlib.LinearAlgebra.Dual.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.0.6 says that every textbook half-space, whether closed or open,
  contains a point.
- `core/canonical`: the primitive owner abstraction is a scalar-valued linear functional
  `f : X →ₗ[𝕜] 𝕜`; pairing-flip maps are bridge instances of that owner.
- `bridge/view`: the chapter constructors `closedHalfSpaceLE`, `closedHalfSpaceGE`,
  `openHalfSpaceLT`, and `openHalfSpaceGT`, together with the predicates `Set.IsClosedHalfSpace`
  and `Set.IsOpenHalfSpace`, are the source-facing half-space view of that owner layer.
- Primitive data vs derived API: the primitive data are the half-space constructors and the
  nontriviality witness on the cutting linear functional; nonemptiness is derived directly from
  surjectivity of a nonzero scalar-valued linear functional, combined with order-endpoint
  witnesses below and above the threshold for strict inequalities.
- Domain-style sampling: the relevant declarations are
  `Module.Dual.range_eq_top_of_ne_zero`, `LinearMap.range_eq_top`, and, at the bridge layer,
  `HasLinearPairing.pairingLinear.flip` with the chapter half-space owners.
- Layer target: `source-facing`, with the supporting API proved owner-first from the canonical
  intrinsic linear-functional owner layer rather than from downstream affine-hyperplane
  infrastructure.
-/

namespace LinearMap

/-- A nonzero scalar-valued linear functional is surjective. -/
theorem surjective_of_ne_zero_scalar (f : X →ₗ[𝕜] 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Function.Surjective f := by
  exact LinearMap.range_eq_top.mp <| Module.Dual.range_eq_top_of_ne_zero (f := f) hf

/-- Every scalar value is attained by a nonzero scalar-valued linear functional. -/
theorem exists_eq_of_ne_zero_scalar (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    ∃ x : X, f x = β :=
  surjective_of_ne_zero_scalar (f := f) hf β

/-- The closed sublevel preimage of a nonzero scalar-valued linear functional is nonempty. -/
theorem preimage_Iic_nonempty_of_ne_zero_scalar [Preorder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (f ⁻¹' Set.Iic β).Nonempty := by
  rcases exists_eq_of_ne_zero_scalar (f := f) β hf with ⟨x, hx⟩
  exact ⟨x, by simp [hx]⟩

/-- The closed superlevel preimage of a nonzero scalar-valued linear functional is nonempty. -/
theorem preimage_Ici_nonempty_of_ne_zero_scalar [Preorder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (f ⁻¹' Set.Ici β).Nonempty := by
  rcases exists_eq_of_ne_zero_scalar (f := f) β hf with ⟨x, hx⟩
  exact ⟨x, by simp [hx]⟩

/-- The strict sublevel set of a nonzero scalar-valued linear functional is nonempty when the
codomain has no minimum. -/
theorem sublevel_lt_nonempty_of_ne_zero_scalar [LT 𝕜] [NoMinOrder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    {x : X | f x < β}.Nonempty := by
  rcases exists_lt β with ⟨γ, hγlt⟩
  rcases exists_eq_of_ne_zero_scalar (f := f) γ hf with ⟨x, hx⟩
  exact ⟨x, by simpa [hx] using hγlt⟩

/-- The strict superlevel set of a nonzero scalar-valued linear functional is nonempty when the
codomain has no maximum. -/
theorem superlevel_gt_nonempty_of_ne_zero_scalar [LT 𝕜] [NoMaxOrder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    {x : X | β < f x}.Nonempty := by
  rcases exists_gt β with ⟨γ, hβltγ⟩
  rcases exists_eq_of_ne_zero_scalar (f := f) γ hf with ⟨x, hx⟩
  exact ⟨x, by simpa [hx] using hβltγ⟩

end LinearMap

end

section LinearOwnerClosedOrder

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

namespace Set

/-- Every intrinsic closed linear half-space is nonempty. -/
theorem IsClosedLinearHalfSpace.nonempty {s : Set X} (hs : closedLinearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with ⟨f, β, hf, rfl | rfl⟩
  · exact LinearMap.preimage_Iic_nonempty_of_ne_zero_scalar (f := f) β hf
  · exact LinearMap.preimage_Ici_nonempty_of_ne_zero_scalar (f := f) β hf

end Set

end LinearOwnerClosedOrder

section LinearOwnerOpenOrder

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [Preorder 𝕜]
variable [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

namespace Set

/-- Every intrinsic open linear half-space is nonempty. -/
theorem IsOpenLinearHalfSpace.nonempty {s : Set X} (hs : openLinearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with ⟨f, β, hf, rfl | rfl⟩
  · exact LinearMap.sublevel_lt_nonempty_of_ne_zero_scalar (f := f) β hf
  · exact LinearMap.superlevel_gt_nonempty_of_ne_zero_scalar (f := f) β hf

/-- Every intrinsic linear half-space is nonempty. -/
theorem IsLinearHalfSpace.nonempty {s : Set X} (hs : linearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with hs | hs
  · exact hs.nonempty
  · exact hs.nonempty

end Set

end LinearOwnerOpenOrder

section ClosedOrder

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem closedHalfSpaceLE_nonempty (b : Y) (β : 𝕜)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (closedHalfSpaceLE b β : Set X).Nonempty := by
  rcases LinearMap.preimage_Iic_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_closedHalfSpaceLE_iff] using hx⟩

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem closedHalfSpaceGE_nonempty (b : Y) (β : 𝕜)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (closedHalfSpaceGE b β : Set X).Nonempty := by
  rcases LinearMap.preimage_Ici_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_closedHalfSpaceGE_iff] using hx⟩

namespace Set

/-- Every closed half-space is nonempty. -/
theorem IsClosedHalfSpace.nonempty {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsClosedLinearHalfSpace.nonempty (hs.toClosedLinearHalfSpace)

end Set

end ClosedOrder

section OpenOrder

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented open half-space `openHalfSpaceLT b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem openHalfSpaceLT_nonempty (b : Y) (β : 𝕜)
    [NoMinOrder 𝕜]
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (openHalfSpaceLT b β : Set X).Nonempty := by
  rcases LinearMap.sublevel_lt_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_openHalfSpaceLT_iff] using hx⟩

/-- The right-oriented open half-space `openHalfSpaceGT b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem openHalfSpaceGT_nonempty (b : Y) (β : 𝕜)
    [NoMaxOrder 𝕜]
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (openHalfSpaceGT b β : Set X).Nonempty := by
  rcases LinearMap.superlevel_gt_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_openHalfSpaceGT_iff] using hx⟩

namespace Set

/-- Every open half-space is nonempty. -/
theorem IsOpenHalfSpace.nonempty {s : Set X}
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
    (hs : openHalfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsOpenLinearHalfSpace.nonempty (hs.toOpenLinearHalfSpace)

end Set

end OpenOrder

section Proposition

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Proposition 2.0.6: every textbook half-space is nonempty. -/
theorem IsHalfSpace.nonempty {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsLinearHalfSpace.nonempty (hs.toLinearHalfSpace)

end Set

/-- Proposition 2.0.6: every textbook half-space, whether closed or open, is nonempty. -/
theorem nonempty_of_halfSpace {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    s.Nonempty :=
  hs.nonempty

end Proposition
