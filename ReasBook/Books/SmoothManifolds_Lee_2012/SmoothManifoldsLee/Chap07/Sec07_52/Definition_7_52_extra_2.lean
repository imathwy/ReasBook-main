import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local mathlib
-- API search was used instead. The source-facing owner here is `IsLinearAction`; the canonical
-- core layer is `DistribMulAction G V` together with `SMulCommClass G 𝕜 V`, with
-- `DistribMulAction.toLinearEquiv` and `Representation.ofDistribMulAction` as the owner-level
-- derived API.

universe uK uG uV

section

variable {𝕜 : Type uK} [Semiring 𝕜]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommMonoid V] [Module 𝕜 V]
variable [MulAction G V]

/-- Definition 7.52-extra-2: a group action of `G` on the `𝕜`-module `V` is a linear action if,
for each `g : G`, the map `x ↦ g • x` is linear. For the source vector-space case, this is exactly
Lee's algebraic linearity condition; the Lie-group smoothness refinement belongs to later items. -/
class IsLinearAction (𝕜 : Type uK) [Semiring 𝕜] (G : Type uG) [Group G] (V : Type uV)
    [AddCommMonoid V] [Module 𝕜 V] [MulAction G V] : Prop where
  map_add (g : G) (x y : V) : g • (x + y) = g • x + g • y
  map_smul (g : G) (a : 𝕜) (x : V) : g • (a • x) = a • (g • x)

/-- Linearity witnesses form a subsingleton because `IsLinearAction` is a proposition. -/
instance instSubsingletonIsLinearAction : Subsingleton (IsLinearAction 𝕜 G V) :=
  inferInstance

namespace IsLinearAction

/-- In a linear action, each action map sends `0` to `0`. -/
theorem smul_zero (h : IsLinearAction 𝕜 G V) (g : G) : g • (0 : V) = 0 := by
  simpa using h.map_smul g (0 : 𝕜) (0 : V)

/-- A linear action canonically upgrades the ambient action to a `DistribMulAction`. -/
abbrev toDistribMulAction (h : IsLinearAction 𝕜 G V) : DistribMulAction G V where
  smul := (· • ·)
  one_smul := fun v ↦ one_smul G v
  mul_smul := fun g₁ g₂ v ↦ mul_smul g₁ g₂ v
  smul_zero := h.smul_zero
  smul_add := h.map_add

/-- A linear action canonically commutes with scalar multiplication. -/
abbrev toSMulCommClass (h : IsLinearAction 𝕜 G V) : SMulCommClass G 𝕜 V where
  smul_comm := h.map_smul

/-- For a fixed group element in a linear action, the action map is the canonical linear
equivalence coming from the induced distributive action. -/
def toLinearEquiv (h : IsLinearAction 𝕜 G V) (g : G) : V ≃ₗ[𝕜] V := by
  let _ : DistribMulAction G V := h.toDistribMulAction
  let _ : SMulCommClass G 𝕜 V := h.toSMulCommClass
  exact DistribMulAction.toLinearEquiv 𝕜 V g

/-- The representation canonically associated to a linear action. -/
noncomputable def toRepresentation (h : IsLinearAction 𝕜 G V) :
    Representation 𝕜 G V := by
  let _ : DistribMulAction G V := h.toDistribMulAction
  let _ : SMulCommClass G 𝕜 V := h.toSMulCommClass
  exact Representation.ofDistribMulAction 𝕜 G V

/-- The canonical linear equivalence attached to `g` acts by the original group action. -/
@[simp] theorem toLinearEquiv_apply (h : IsLinearAction 𝕜 G V) (g : G) (v : V) :
    h.toLinearEquiv g v = g • v := by
  simp [toLinearEquiv]

/-- The associated representation acts by the original group action on `V`. -/
@[simp] theorem toRepresentation_apply (h : IsLinearAction 𝕜 G V) (g : G) (v : V) :
    h.toRepresentation g v = g • v := by
  simp [toRepresentation]

end IsLinearAction

end
