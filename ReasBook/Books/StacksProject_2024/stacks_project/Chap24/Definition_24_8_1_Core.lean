import StacksProject_2024.stacks_project.Chap24.Definition_24_4_1_Core

open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Definition 24.8.1 (1): a graded `(\mathcal A, \mathcal B)`-bimodule on a ringed site is a
right graded `\mathcal B`-module together with a compatible left graded `\mathcal A`-action. -/
@[stacks 0FR5]
structure GradedBimodule
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (A B : GradedAlgebraSheaf 𝒪) where
  /-- The underlying right graded `\mathcal B`-module. -/
  toRightModule : GradedModuleSheaf B
  /-- The left graded `\mathcal A`-action on local sections. -/
  leftMul :
    ∀ n m (U : Cᵒᵖ),
      A.sections U n →ₗ[𝒪.obj.obj U]
        toRightModule.sections U m →ₗ[𝒪.obj.obj U] toRightModule.sections U (n + m)
  /-- The left action commutes with restriction. -/
  map_leftMul :
    ∀ {n m : ℤ} {U V : Cᵒᵖ} (f : U ⟶ V)
      (a : A.sections U n) (x : toRightModule.sections U m),
      (((toRightModule (n + m)).val.map f).hom) (leftMul n m U a x) =
        leftMul n m V (((A n).val.map f).hom a) (((toRightModule m).val.map f).hom x)
  /-- The left action is associative with the multiplication on `\mathcal A`. -/
  left_assoc :
    ∀ i j k (U : Cᵒᵖ)
      (a : A.sections U i) (a' : A.sections U j) (x : toRightModule.sections U k),
      HEq (leftMul (i + j) k U (A.mul U i j a a') x)
        (leftMul i (j + k) U a (leftMul j k U a' x))
  /-- The unit of `\mathcal A^0` acts trivially on the left. -/
  one_left :
    ∀ n (U : Cᵒᵖ) (x : toRightModule.sections U n),
      HEq (leftMul 0 n U (A.one U) x) x
  /-- The left `\mathcal A`-action commutes with the given right `\mathcal B`-action. -/
  middle_assoc :
    ∀ i j k (U : Cᵒᵖ)
      (a : A.sections U i) (x : toRightModule.sections U j) (b : B.sections U k),
      HEq (toRightModule.smul (i + j) k U (leftMul i j U a x) b)
        (leftMul i (j + k) U a (toRightModule.smul j k U x b))

namespace GradedBimodule

/- Source-facing notation: the Stacks Project writes the category of graded
`(\mathcal A, \mathcal B)`-bimodules as `\mathrm{Mod}(\mathcal A, \mathcal B)`. This scoped
notation exposes the canonical owner `GradedBimodule 𝒪 A B`. -/
scoped[SheafOfModules.RingedSite.GradedBimodule] notation:max "Mod(" A ", " B ")" =>
  _root_.SheafOfModules.RingedSite.GradedBimodule _ A B

end GradedBimodule

end

end SheafOfModules.RingedSite
