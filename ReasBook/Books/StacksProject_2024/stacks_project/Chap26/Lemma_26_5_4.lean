import Mathlib
import StacksProject_2024.stacks_project.Chap26.Lemma_26_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open PrimeSpectrum
open scoped AlgebraicGeometry PrimeSpectrum

noncomputable section

universe u

section

variable (R : CommRingCat.{u})
variable (M : ModuleCat R)

-- Semantic recall: the canonical affine owners for this item are `Scheme.ΓSpecIso`,
-- `StructureSheaf.globalSectionsIso`, `StructureSheaf.toBasicOpenₗ`, `Stalk.stalkIso`,
-- `tilde.isoTop`, `tilde.toStalk`, `tilde.toTildeΓNatIso`, and the comparison maps from
-- `Lemma_26_5_1`.

/-- Lemma 26.5.4 (1): the global sections of the structure sheaf on `Spec(R)` identify with `R`.
-/
noncomputable abbrev specGlobalSectionsIso :
    (Spec R).presheaf.obj (Opposite.op ⊤) ≅ R :=
  Scheme.ΓSpecIso R

/-- `specGlobalSectionsIso` is definitionally the canonical affine global-sections isomorphism. -/
theorem specGlobalSectionsIso_def :
    specGlobalSectionsIso R = Scheme.ΓSpecIso R := sorry

/-- Lemma 26.5.4 (2): the global sections of `\widetilde M` identify with `M` as an
`R`-module. -/
noncomputable abbrev tildeGlobalSectionsIso :
    M ≅ (@AlgebraicGeometry.moduleSpecΓFunctor R).obj (AlgebraicGeometry.tilde M) :=
  AlgebraicGeometry.tilde.isoTop M

/-- `tildeGlobalSectionsIso` is definitionally the canonical affine `\widetilde{(-)}`-`Γ`
comparison isomorphism. -/
theorem tildeGlobalSectionsIso_def :
    tildeGlobalSectionsIso R M = AlgebraicGeometry.tilde.isoTop M := sorry

/-- Lemma 26.5.4 (3): for `f ∈ R`, the sections of the structure sheaf on `D(f)` identify with
the localization `R_f`. -/
noncomputable abbrev structureSheafSectionsBasicOpenIso (f : R) :
    Localization.Away f ≃ₐ[R] ((Spec.structureSheaf R).obj.obj (Opposite.op <| D(f))) :=
  IsLocalization.algEquiv (.powers f) _ _

/-- Lemma 26.5.4 (4): for `f ∈ R`, the sections of `\widetilde M` on `D(f)` identify with the
localized module `M_f`. -/
noncomputable abbrev tildeSectionsBasicOpenIso (f : R) :
    LocalizedModule.Away f M ≃ₗ[R]
      ((AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj
        (Opposite.op <| D(f))) :=
  IsLocalizedModule.iso (.powers f) (AlgebraicGeometry.tilde.toOpen M (D(f))).hom

/-- Lemma 26.5.4 (5): if `D(g) ⊆ D(f)`, then under the canonical localization identifications the
restriction map on the structure sheaf is the comparison map `R_f → R_g` from Lemma `26.5.1`. -/
theorem structureSheafRestriction_basicOpen_eq_awayToAwayRingHom
    (f g : R) (h : D(g) ≤ D(f)) :
    CommRingCat.ofHom
        (structureSheafSectionsBasicOpenIso R f).toRingHom ≫
      (Spec.structureSheaf R).1.map (homOfLE h).op =
      CommRingCat.ofHom (awayToAwayRingHom f g h) ≫
        CommRingCat.ofHom (structureSheafSectionsBasicOpenIso R g).toRingHom := sorry

/-- Lemma 26.5.4 (6): if `D(g) ⊆ D(f)`, then under the canonical localization identifications the
restriction map on `\widetilde M` is the comparison map `M_f → M_g` from Lemma `26.5.1`. -/
theorem tildeRestriction_basicOpen_eq_awayToAwayModuleMap
    (f g : R) (h : D(g) ≤ D(f)) :
    ModuleCat.ofHom (tildeSectionsBasicOpenIso R M f).toLinearMap ≫
        (AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.map
          (homOfLE h).op =
      ModuleCat.ofHom (awayToAwayModuleMap f g h) ≫
        ModuleCat.ofHom (tildeSectionsBasicOpenIso R M g).toLinearMap := sorry

/-- Lemma 26.5.4 (7): the stalk of the structure sheaf at `x` identifies with the localization
`R_x`. -/
noncomputable abbrev structureSheafStalkIso (x : PrimeSpectrum R) :
    Localization.AtPrime x.asIdeal ≃ₐ[R] (Spec.structureSheaf R).presheaf.stalk x :=
  IsLocalization.algEquiv x.asIdeal.primeCompl _ _

/-- `structureSheafStalkIso` is definitionally the canonical stalk-localization isomorphism. -/
theorem structureSheafStalkIso_def (x : PrimeSpectrum R) :
    structureSheafStalkIso R x = IsLocalization.algEquiv x.asIdeal.primeCompl _ _ := sorry

/-- Lemma 26.5.4 (8): the stalk of `\widetilde M` at `x` identifies with the localized module
`M_x`. -/
noncomputable abbrev tildeStalkIso (x : PrimeSpectrum R) :
    LocalizedModule x.asIdeal.primeCompl M ≃ₗ[R]
      ((AlgebraicGeometry.tilde M).presheaf.stalk x) :=
  IsLocalizedModule.iso x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom

/-- `tildeStalkIso` is definitionally the canonical localized-module identification at a stalk. -/
theorem tildeStalkIso_def (x : PrimeSpectrum R) :
    tildeStalkIso R M x =
      IsLocalizedModule.iso x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom := sorry

/-- Lemma 26.5.4 (9): the identification of `M` with the global sections of `\widetilde M` is
functorial in `M`, via the unit isomorphism of the affine `\widetilde{(-)} \dashv \Gamma`
adjunction. -/
noncomputable abbrev tildeGlobalSectionsNatIso :
    𝟭 (ModuleCat R) ≅
      AlgebraicGeometry.tilde.functor R ⋙ (@AlgebraicGeometry.moduleSpecΓFunctor R) :=
  @AlgebraicGeometry.tilde.toTildeΓNatIso R

/-- `tildeGlobalSectionsNatIso` is definitionally the canonical affine unit isomorphism. -/
theorem tildeGlobalSectionsNatIso_def :
    tildeGlobalSectionsNatIso R = @AlgebraicGeometry.tilde.toTildeΓNatIso R := sorry

/-- Lemma 26.5.4 (10): the affine associated-module functor `M ↦ \widetilde M` is exact. -/
theorem tildeFunctor_exact :
    exactFunctor (ModuleCat R) (Spec R).Modules (AlgebraicGeometry.tilde.functor R) := sorry

end
