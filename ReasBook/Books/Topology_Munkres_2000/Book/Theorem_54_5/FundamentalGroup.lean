module

import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

public section

namespace Circle

private def periodHom : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) where
  toFun n := ⟨n • (2 * Real.pi), ⟨n, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' m n := by ext; simp [add_smul]

private theorem periodHom_bijective : Function.Bijective periodHom := by
  constructor
  · intro m n h
    apply (smul_left_injective ℤ (show (2 * Real.pi : ℝ) ≠ 0 by positivity))
    exact congr_arg Subtype.val h
  · intro x
    rcases x.property with ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩

/-- Integer multiples identify `ℤ` with the period group of `Circle.exp`. -/
def periodAddEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddEquiv.ofBijective periodHom periodHom_bijective

/-- The standard exponential covering identifies `π₁(S¹, 1)` with `ℤ`. -/
def fundamentalGroupEquivInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  (isAddQuotientCoveringMap_exp.fundamentalGroupEquiv ⟨0, by simp⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans <|
      (AddEquiv.toMultiplicative periodAddEquiv).symm

end Circle

end
