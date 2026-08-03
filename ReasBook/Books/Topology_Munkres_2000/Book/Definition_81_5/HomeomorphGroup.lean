module

public import Mathlib.Topology.Algebra.ConstMulAction

public section

open Set Topology

universe u

namespace HomeomorphGroup

variable {X : Type u} [TopologicalSpace X] (G : Subgroup (X ≃ₜ X))

/-- A subgroup of self-homeomorphisms acts on the space by evaluation. -/
instance instMulAction : MulAction G X where
  smul g x := (g : X ≃ₜ X) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Evaluation by each element of a self-homeomorphism subgroup is continuous. -/
theorem continuous_const_smul (g : G) : Continuous fun x : X ↦ g • x :=
  (g : X ≃ₜ X).continuous

/-- Evaluation by every element of a self-homeomorphism subgroup is continuous. -/
instance instContinuousConstSMul : ContinuousConstSMul G X where
  continuous_const_smul := continuous_const_smul G

/-- The orbit space for a subgroup of self-homeomorphisms acting by evaluation. -/
abbrev OrbitSpace : Type u :=
  MulAction.orbitRel.Quotient G X

/-- The standard notation `X / G` for the orbit space of an evaluation action. -/
scoped[HomeomorphGroup] notation:70 X:70 " / " G:71 =>
  HomeomorphGroup.OrbitSpace (G : Subgroup (X ≃ₜ X))

/-- The canonical projection from a space to its orbit space. -/
@[expose]
def mk (x : X) : OrbitSpace G :=
  Quotient.mk'' x

/-- The named orbit projection agrees with the underlying quotient constructor. -/
@[simp]
theorem mk_eq_quotient_mk (x : X) :
    mk G x = Quotient.mk (MulAction.orbitRel G X) x :=
  rfl

/-- Membership in an evaluation orbit is witnessed by a self-homeomorphism in the subgroup. -/
theorem mem_orbit_iff {x y : X} :
    y ∈ MulAction.orbit G x ↔ ∃ g : G, (g : X ≃ₜ X) x = y :=
  Iff.rfl

/-- Two points have the same image in the orbit space exactly when one lies in the other's orbit. -/
theorem mk_eq_mk_iff {x y : X} : mk G x = mk G y ↔ y ∈ MulAction.orbit G x := by
  constructor
  · intro h
    exact MulAction.mem_orbit_symm.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  · intro h
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_symm.mpr h))

/-- The canonical orbit attached to a quotient point agrees with the evaluation orbit. -/
theorem quotientOrbit_mk (x : X) :
    MulAction.orbitRel.Quotient.orbit (mk G x) = MulAction.orbit G x :=
  MulAction.orbitRel.Quotient.orbit_mk x

/-- The canonical projection equips the orbit type with the quotient topology. -/
theorem isQuotientMap_mk : IsQuotientMap (mk G) :=
  isQuotientMap_quotient_mk'

end HomeomorphGroup
