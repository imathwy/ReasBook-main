import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open AlgebraicGeometry
open RingedSpace.Hom
open SheafOfModules.RingedSite (restrictionAlong)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {R A : CommRingCat.{u}}

/-- The structure-sheaf morphism on affine spectra induced by a ring map `R ⟶ A`. -/
abbrev affineStructureSheafMap (φ : R ⟶ A) :=
  inverseImageStructureSheafHomComm (Spec.map φ).toShHom

/-- The canonical restriction-of-scalars morphism type for relative differential operators on
`Spec(A) ⟶ Spec(R)`. -/
abbrev affineDifferentialOperatorHom
    (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules) :=
  (restrictionAlong (affineStructureSheafMap φ)).obj ℱ ⟶
    (restrictionAlong (affineStructureSheafMap φ)).obj 𝒢

/-- Differential operators on affine global sections over the ring map `R ⟶ A`. -/
abbrev affineGlobalSectionsDifferentialOperators
    (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules) (k : ℕ) :=
  let M := Γ(ℱ, ⊤)
  let N := Γ(𝒢, ⊤)
  let _ : Algebra R A := φ.hom.toAlgebra
  let _ : Module A M := Module.compHom M (Scheme.ΓSpecIso A).inv.hom
  let _ : Module A N := Module.compHom N (Scheme.ΓSpecIso A).inv.hom
  let _ : Module R M := Module.compHom M φ.hom
  let _ : Module R N := Module.compHom N φ.hom
  let _ : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  differential_operators_order_le R A M k N

/-- Apply a relative sheaf morphism on `Spec(A) ⟶ Spec(R)` to an affine global section. -/
abbrev affineApplyRestrictedSection
    (φ : R ⟶ A) {ℱ 𝒢 : (Spec A).Modules}
    (D : affineDifferentialOperatorHom φ ℱ 𝒢) (m : Γ(ℱ, ⊤)) :
    Γ(𝒢, ⊤) :=
  show Γ(𝒢, ⊤) from
    SheafOfModules.sectionsMap D
      (show ((restrictionAlong (affineStructureSheafMap φ)).obj ℱ).sections from m)

-- Semantic recall: `Scheme.ΓSpecIso` gives the affine-global-sections algebra structure, and
-- Chapter 18 already packages relative sheaf differential operators by
-- `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`. The source-facing affine item is the
-- resulting existence-and-uniqueness comparison between a differential operator on sections and a
-- sheaf differential operator over `Spec(A) ⟶ Spec(R)`.

/-- Lemma 29.33.1: for a ring map `R ⟶ A`, let `f : Spec(A) ⟶ Spec(R)` be the corresponding
morphism of affine schemes. If `ℱ` is a quasi-coherent `\mathcal O_{Spec(A)}`-module, then every
order-`k` differential operator on global sections `Γ(ℱ, \top) → Γ(𝒢, \top)` over `R ⟶ A`
extends uniquely to an order-`k` differential operator `ℱ → 𝒢`. Equivalently, the global-sections
map `Diff^k_{X/S}(ℱ, 𝒢) → Diff^k_{A/R}(Γ(X, ℱ), Γ(X, 𝒢))` is bijective for
`X = Spec(A)` and `S = Spec(R)`. -/
theorem existsUnique_affineDifferentialOperator_of_globalSections
    (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules) [ℱ.IsQuasicoherent]
    (k : ℕ)
    (D : affineGlobalSectionsDifferentialOperators φ ℱ 𝒢 k) :
    ∃! Dsheaf : affineDifferentialOperatorHom φ ℱ 𝒢,
      SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder
          (affineStructureSheafMap φ) Dsheaf k ∧
        ∀ m : Γ(ℱ, ⊤), affineApplyRestrictedSection φ Dsheaf m = D.1 m := by
  sorry

end

end AlgebraicGeometry
