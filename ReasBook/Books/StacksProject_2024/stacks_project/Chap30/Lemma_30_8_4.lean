import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_14_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the mathlib fixed symmetric-power and exterior-power
module owners (`SymmetricPower` and `ExteriorAlgebra.exteriorPower`). Local Chapter 17 supplies
`SheafOfModules.IsFiniteLocallyFreeOfRank` and stalk modules, while Chapter 29 supplies the
projective-bundle presentation `ProjectiveBundleOver`; Chapter 30 precedent states higher direct
images as `((Scheme.Modules.pushforward f).rightDerived q).obj ℱ`. -/

/-- The stalkwise target modeling `Sym^d(\mathcal E)`, with negative degree interpreted as the
zero module. -/
abbrev projectiveBundleSymmetricPowerStalk
    (S : Scheme.{u}) (E : S.Modules) (d : ℤ) (x : S) :
    ModuleCat (S.presheaf.stalk x) :=
  if 0 ≤ d then
    ModuleCat.of (S.presheaf.stalk x)
      (SymmetricPower (S.presheaf.stalk x) (ULift.{u, 0} (Fin d.toNat))
        (RingedSpace.stalkModuleCat E x))
  else
    ModuleCat.of (S.presheaf.stalk x) PUnit

/-- In nonnegative degree, the symmetric-power stalk target is the usual fixed symmetric power of
the stalk module. -/
theorem projectiveBundleSymmetricPowerStalk_of_nonneg
    (S : Scheme.{u}) (E : S.Modules) (d : ℤ) (x : S) (hd : 0 ≤ d) :
    projectiveBundleSymmetricPowerStalk S E d x =
      ModuleCat.of (S.presheaf.stalk x)
        (SymmetricPower (S.presheaf.stalk x) (ULift.{u, 0} (Fin d.toNat))
          (RingedSpace.stalkModuleCat E x)) := sorry

/-- In negative degree, the symmetric-power stalk target is the zero module. -/
theorem projectiveBundleSymmetricPowerStalk_of_neg
    (S : Scheme.{u}) (E : S.Modules) (d : ℤ) (x : S) (hd : ¬ 0 ≤ d) :
    projectiveBundleSymmetricPowerStalk S E d x =
      ModuleCat.of (S.presheaf.stalk x) PUnit := sorry

/-- The stalkwise target modeling
`\mathcal Hom_{\mathcal O_S}(\operatorname{Sym}^{-n-1-d}(\mathcal E) \otimes
\bigwedge^{n+1}\mathcal E, \mathcal O_S)`, with negative symmetric degree interpreted as zero. -/
abbrev projectiveBundleTopCohomologyStalk
    (S : Scheme.{u}) (E : S.Modules) (n : ℕ) (d : ℤ) (x : S) :
    ModuleCat (S.presheaf.stalk x) :=
  if 0 ≤ -((n : ℤ) + 1) - d then
    ModuleCat.of (S.presheaf.stalk x)
      ((SymmetricPower (S.presheaf.stalk x)
            (ULift.{u, 0} (Fin (-((n : ℤ) + 1) - d).toNat))
            (RingedSpace.stalkModuleCat E x) ⊗[S.presheaf.stalk x]
          (⋀[S.presheaf.stalk x]^(n + 1) (RingedSpace.stalkModuleCat E x))) →ₗ[
            S.presheaf.stalk x] S.presheaf.stalk x)
  else
    ModuleCat.of (S.presheaf.stalk x) PUnit

/-- In the range where `-n - 1 - d` is nonnegative, the top-cohomology stalk target is the
linear dual of the tensor product of the fixed symmetric power and the top exterior power. -/
theorem projectiveBundleTopCohomologyStalk_of_nonneg
    (S : Scheme.{u}) (E : S.Modules) (n : ℕ) (d : ℤ) (x : S)
    (hd : 0 ≤ -((n : ℤ) + 1) - d) :
    projectiveBundleTopCohomologyStalk S E n d x =
      ModuleCat.of (S.presheaf.stalk x)
        ((SymmetricPower (S.presheaf.stalk x)
              (ULift.{u, 0} (Fin (-((n : ℤ) + 1) - d).toNat))
              (RingedSpace.stalkModuleCat E x) ⊗[S.presheaf.stalk x]
            (⋀[S.presheaf.stalk x]^(n + 1) (RingedSpace.stalkModuleCat E x))) →ₗ[
              S.presheaf.stalk x] S.presheaf.stalk x) := sorry

/-- Outside the range where `-n - 1 - d` is nonnegative, the top-cohomology stalk target is the
zero module. -/
theorem projectiveBundleTopCohomologyStalk_of_neg
    (S : Scheme.{u}) (E : S.Modules) (n : ℕ) (d : ℤ) (x : S)
    (hd : ¬ 0 ≤ -((n : ℤ) + 1) - d) :
    projectiveBundleTopCohomologyStalk S E n d x =
      ModuleCat.of (S.presheaf.stalk x) PUnit := sorry

section

variable (S : Scheme.{u}) (n : ℕ)
variable (P : ProjectiveBundleOver S)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) P.module]
variable [HasInjectiveResolutions P.scheme.Modules]
variable (Od : P.scheme.Modules)

/-- Lemma 30.8.4 (1): for the structure morphism
`\pi : \mathbf P(\mathcal E) \to S` of a projective bundle whose presenting module is finite
locally free of constant rank `n + 1`, the degree-`0` higher direct image of
`\mathcal O_{\mathbf P(\mathcal E)}(d)` identifies with `\operatorname{Sym}^d(\mathcal E)`.
The target sheaf is supplied with its stalkwise fixed-symmetric-power specification because the
current project has no global fixed-degree symmetric-power sheaf owner. -/
@[stacks 01XX]
theorem projectiveBundleTwistHigherDirectImage_zero
    (hn : 1 ≤ n) (d : ℤ)
    (SymdE : S.Modules)
    (hSymdE : ∀ x : S,
      IsIsomorphic (RingedSpace.stalkModuleCat SymdE x)
        (projectiveBundleSymmetricPowerStalk S P.module d x)) :
    IsIsomorphic
      (((Scheme.Modules.pushforward P.hom).rightDerived 0).obj Od)
      SymdE := sorry

/-- Lemma 30.8.4 (2): for the structure morphism
`\pi : \mathbf P(\mathcal E) \to S`, all higher direct images of
`\mathcal O_{\mathbf P(\mathcal E)}(d)` vanish outside degrees `0` and `n`. -/
@[stacks 01XX]
theorem projectiveBundleTwistHigherDirectImage_isZero_of_ne_zero_ne_top
    (hn : 1 ≤ n) (d : ℤ) (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od) := sorry

/-- Lemma 30.8.4 (3): for the structure morphism
`\pi : \mathbf P(\mathcal E) \to S`, the degree-`n` higher direct image of
`\mathcal O_{\mathbf P(\mathcal E)}(d)` identifies with
`\mathcal Hom_{\mathcal O_S}(\operatorname{Sym}^{-n-1-d}(\mathcal E) \otimes
\bigwedge^{n+1}\mathcal E, \mathcal O_S)`. The target sheaf is supplied with its stalkwise
internal-Hom specification because the current project has no global fixed-degree symmetric-power
sheaf owner. -/
@[stacks 01XX]
theorem projectiveBundleTwistHigherDirectImage_top
    (hn : 1 ≤ n) (d : ℤ)
    (TopdE : S.Modules)
    (hTopdE : ∀ x : S,
      IsIsomorphic (RingedSpace.stalkModuleCat TopdE x)
        (projectiveBundleTopCohomologyStalk S P.module n d x)) :
    IsIsomorphic
      (((Scheme.Modules.pushforward P.hom).rightDerived n).obj Od)
      TopdE := sorry

end

section

variable {S S' : Scheme.{u}} (g : S' ⟶ S)
variable (n q : ℕ)
variable (P : ProjectiveBundleOver S) (P' : ProjectiveBundleOver S')
variable [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) P.module]
variable [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) P'.module]
variable [HasInjectiveResolutions P.scheme.Modules]
variable [HasInjectiveResolutions P'.scheme.Modules]
variable (Od : P.scheme.Modules) (Od' : P'.scheme.Modules)
variable (Target : S.Modules) (Target' : S'.Modules)

/-- Lemma 30.8.4 (4): the projective-bundle cohomology identifications are compatible with base
change. This statement records the reusable commutative square: after pulling back the chosen
identification on `S`, the base-change map on higher direct images agrees with the chosen
identification on `S'` followed by the target comparison. -/
@[stacks 01XX]
theorem projectiveBundleTwistHigherDirectImage_baseChange_compatible
    (hn : 1 ≤ n) (d : ℤ)
    (ident :
      (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od) ≅ Target)
    (ident' :
      (((Scheme.Modules.pushforward P'.hom).rightDerived q).obj Od') ≅ Target')
    (higherBaseChange :
      ((Scheme.Modules.pullback g).obj
        (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od)) ⟶
        (((Scheme.Modules.pushforward P'.hom).rightDerived q).obj Od'))
    (targetBaseChange :
      ((Scheme.Modules.pullback g).obj Target) ⟶ Target') :
    (Scheme.Modules.pullback g).map ident.hom ≫ targetBaseChange =
      higherBaseChange ≫ ident'.hom := sorry

variable {S : Scheme.{u}} (n q : ℕ)
variable (P P' : ProjectiveBundleOver S)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) P.module]
variable [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) P'.module]
variable [HasInjectiveResolutions P.scheme.Modules]
variable [HasInjectiveResolutions P'.scheme.Modules]
variable (Od : P.scheme.Modules) (Od' : P'.scheme.Modules)
variable (Target Target' : S.Modules)

/-- Lemma 30.8.4 (5): the projective-bundle cohomology identifications are compatible with an
isomorphism between the locally free sheaves defining the projective bundles. The explicit
isomorphisms on higher direct images and on the algebraic target sheaves are parameters so the
statement can be instantiated by whichever projective-bundle and twist owners are available. -/
@[stacks 01XX]
theorem projectiveBundleTwistHigherDirectImage_iso_compatible
    (hn : 1 ≤ n) (d : ℤ)
    (moduleIso : P.module ≅ P'.module)
    (ident :
      (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od) ≅ Target)
    (ident' :
      (((Scheme.Modules.pushforward P'.hom).rightDerived q).obj Od') ≅ Target')
    (higherIso :
      (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od) ≅
        (((Scheme.Modules.pushforward P'.hom).rightDerived q).obj Od'))
    (targetIso : Target ≅ Target') :
    ident.hom ≫ targetIso.hom = higherIso.hom ≫ ident'.hom := sorry

end

end AlgebraicGeometry
