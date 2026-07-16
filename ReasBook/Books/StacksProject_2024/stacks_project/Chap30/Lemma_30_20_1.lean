import StacksProject_2024.stacks_project.Chap10.Definition_10_70_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_19_3
import StacksProject_2024.stacks_project.Chap30.Lemma_30_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` was attempted for Rees-algebra and ideal-power cohomology
recall but timed out. Local Chapter 30 Lemma 30.19.3 provides the graded-module-sheaf cohomology
owner used by the source proof, Lemma 30.24.2 provides `idealSheafDataOfIdealOnSpec`, and Chapter
10 provides the canonical Rees algebra owner `reesAlgebra I` with grading `reesAlgebraGrade I`.
The unavailable Artin-Rees helper import contains an `idealPowerProductSubobject` API, but its
import closure is currently broken, so this file uses the canonical kernel of restriction to the
closed subscheme cut out by the pulled-back ideal power. The tag evidence is consistent for Stacks
tag `02O8`. -/

/-- The pulled-back ideal sheaf on `X` determined by `I ⊂ A` and `f : X -> Spec(A)`. -/
abbrev pulledBackIdealSheafDataOfIdealOnSpec {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) : X.IdealSheafData :=
  (idealSheafDataOfIdealOnSpec I).comap f

/-- The ideal sheaf for the power `(f^{-1} I)^n` on `X`, written affine-openwise. -/
abbrev pulledBackIdealPowerIdealSheaf {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (n : ℕ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦ (pulledBackIdealSheafDataOfIdealOnSpec I f).ideal U ^ n

/-- The canonical restriction map `F -> i_{n,*} i_n^* F` to the closed subscheme cut out by
`(f^{-1} I)^n`. -/
noncomputable abbrev idealPowerProductRestrictionMap {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (n : ℕ) :
    F ⟶ (pushforward (pulledBackIdealPowerIdealSheaf I f n).subschemeι).obj
      ((pullback (pulledBackIdealPowerIdealSheaf I f n).subschemeι).obj F) :=
  (pullbackPushforwardAdjunction (pulledBackIdealPowerIdealSheaf I f n).subschemeι).unit.app F

/-- The canonical sheaf `I^n F` on `X`, realized as the kernel of restriction to the closed
subscheme defined by `(f^{-1} I)^n`. -/
noncomputable abbrev idealPowerProductSheaf {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (n : ℕ) :
    X.Modules :=
  kernel (idealPowerProductRestrictionMap I f F n)

/-- The canonical inclusion `I^n F -> F`. -/
noncomputable abbrev idealPowerProductSheafι {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (n : ℕ) :
    idealPowerProductSheaf I f F n ⟶ F :=
  kernel.ι (idealPowerProductRestrictionMap I f F n)

/-- The degree-`n` summand `H^p(X, I^n F)` for the canonical ideal-power family. -/
abbrev idealPowerProductCohomologyPiece {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p n : ℕ) : Type u :=
  (schemeModuleCohomology (idealPowerProductSheaf I f F n) p : Type u)

/-- The defining normal form for the canonical ideal-power cohomology summand. -/
theorem idealPowerProductCohomologyPiece_def {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p n : ℕ) :
    idealPowerProductCohomologyPiece I f F p n =
      (schemeModuleCohomology (idealPowerProductSheaf I f F n) p : Type u) := sorry

/-- The direct sum `⊕ n ≥ 0, H^p(X, I^n F)` for the canonical ideal-power family. -/
abbrev idealPowerProductCohomologyDirectSum {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) : Type u :=
  DirectSum ℕ fun n : ℕ ↦ idealPowerProductCohomologyPiece I f F p n

/-- The defining normal form for the canonical ideal-power cohomology direct sum. -/
theorem idealPowerProductCohomologyDirectSum_def {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) :
    idealPowerProductCohomologyDirectSum I f F p =
      DirectSum ℕ fun n : ℕ ↦ idealPowerProductCohomologyPiece I f F p n := sorry

/-- On affine opens, the canonical sheaf `I^n F` has sections
`((f^{-1} I)(U))^n F(U)`. -/
theorem range_idealPowerProductSheafι_app_eq_affine_idealPower_smul_top {A : Type u}
    [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (U : X.affineOpens) (n : ℕ) :
    LinearMap.range (((idealPowerProductSheafι I f F n).val.app (op U.1)).hom) =
      (pulledBackIdealSheafDataOfIdealOnSpec I f).ideal U ^ n •
        (⊤ : Submodule Γ(X, U.1) (F.val.obj (op U.1))) := sorry

/-- The zeroth canonical ideal-power sheaf is the original coherent sheaf. -/
theorem idealPowerProductSheaf_zero {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) :
    idealPowerProductSheaf I f F 0 = F := sorry

/-- Lemma 30.20.1: let `A` be a Noetherian ring and `I ⊂ A` an ideal. For
`B = ⊕ n ≥ 0, I^n`, a proper morphism `f : X -> Spec(A)`, and a coherent sheaf `F` on `X`,
the graded `B`-module `⊕ n ≥ 0, H^p(X, I^n F)` is finite for every `p ≥ 0`. Here `B` is the
canonical Rees algebra `reesAlgebra I`, and the summands use the canonical kernel realization of
`I^n F` for the pulled-back ideal sheaf `(f^{-1} I)^n`. The remaining module typeclass is the
source-induced Rees action on this displayed canonical direct sum. -/
@[stacks 02O8]
theorem properCoherentIdealPowerCohomology_finite_over_reesAlgebra
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (p : ℕ)
    [Module (reesAlgebra I) (idealPowerProductCohomologyDirectSum I f F p)] :
    Module.Finite (reesAlgebra I) (idealPowerProductCohomologyDirectSum I f F p) := sorry

end AlgebraicGeometry.Scheme.Modules
