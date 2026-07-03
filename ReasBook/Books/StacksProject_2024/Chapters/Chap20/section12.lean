import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_12_1 (from Chap20) -/
universe u v

open CategoryTheory Opposite TopologicalSpace TopCat

variable {X : TopCat.{u}}

/- Domain-style sampling for Definition 20.12.1:
- primary domain: set-valued presheaves on a topological space, with flasqueness expressed through
  restriction morphisms;
- sampled owner API:
  `TopCat.Presheaf.IsFlasque`,
  `TopCat.Sheaf.IsFlasque`,
  `CategoryTheory.epi_iff_surjective`,
- source/core/bridge triage:
  `source-facing`: the Stacks-project condition that every restriction map `F(V) → F(U)` is
  surjective for `U ≤ V`;
  `core/canonical`: `TopCat.Presheaf.IsFlasque F`;
  `bridge/view`: the `Type`-valued reformulation of the epi field as surjectivity of restriction
  maps.

Primitive data are only the presheaf `F` and the owner predicate `Presheaf.IsFlasque F`, whose
single field asks that every restriction morphism be epi. The elementwise surjectivity condition
is derived API from that owner, so this file should recall `Presheaf.IsFlasque` directly and keep
the restriction-surjectivity formulation only as a thin companion theorem.
-/

/- Definition 20.12.1: a presheaf of sets on a topological space `X` is flasque (or flabby) in
the canonical mathlib sense `TopCat.Presheaf.IsFlasque`. -/
recall Presheaf.IsFlasque

-- Proof sketch: unwind `TopCat.Presheaf.IsFlasque`, which asks that every restriction morphism be
-- an epimorphism; for `Type`-valued presheaves, epimorphisms are exactly surjective maps by
-- `CategoryTheory.epi_iff_surjective`.
/-- A set-valued presheaf is flasque exactly when each restriction map along an inclusion of open
sets is surjective. -/
theorem presheaf_isFlasque_iff_restriction_surjective
    (F : X.Presheaf (Type v)) :
    Presheaf.IsFlasque F ↔
      ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), Function.Surjective (F.map (homOfLE hUV).op) := by
  constructor
  · intro h U V hUV
    let _ : Epi (F.map (homOfLE hUV).op) := h.epi (homOfLE hUV).op
    exact (CategoryTheory.epi_iff_surjective _).1 inferInstance
  · intro h
    exact ⟨fun i ↦ (CategoryTheory.epi_iff_surjective _).2 (by
      simpa using h (leOfHom i.unop))⟩

/-! ### Lemma_20_12_2 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.12.2:
- primary domain: sheaves of modules on a ringed space, viewed through their underlying abelian
  sheaves and the flasqueness predicate;
- sampled owner declarations:
  `(RingedSpace.ringCatSheaf X)`,
  `(RingedSpace.Modules X)`,
  `moduleUnderlyingSheaf`,
  `TopCat.Sheaf.IsFlasque`;
- best owner abstraction: the Chapter 20 ringed-space owner `(RingedSpace.Modules X)`, with
  `moduleUnderlyingSheaf` as the canonical bridge to the flasque sheaf statement;
- primitive data: a ringed space `X`, an object `ℐ : (RingedSpace.Modules X)`, and the categorical
  injectivity hypothesis `Injective ℐ`;
- derived API: flasqueness of the underlying abelian sheaf.

Source/core/bridge triage:
- `source-facing`: the statement that injective `\mathcal O_X`-modules are flasque;
- `core/canonical`: `(RingedSpace.Modules X)` and `TopCat.Sheaf.IsFlasque`;
- `bridge/view`: `moduleUnderlyingSheaf`.

This file should therefore reuse the earlier Chapter 20 owner declarations rather than duplicate a
local `ringedSpaceRingCatSheaf` abbreviation. -/

-- Proof sketch: by the flasqueness owner API from Definition `20.12.1`, it suffices to show that
-- every restriction morphism of the underlying additive sheaf is epi. For `AddCommGrpCat` this is
-- equivalent to surjectivity, and Lemma `20.8.1` supplies that surjectivity for injective
-- `\mathcal O_X`-modules.
/-- Lemma 20.12.2: for a ringed space `(X, \mathcal{O}_X)`, any injective `\mathcal{O}_X`-module
is flasque as a sheaf of abelian groups. -/
theorem module_isFlasque_of_injective
    {X : RingedSpace.{u}} (ℐ : (RingedSpace.Modules X))
    (hℐ : Injective ℐ) :
    TopCat.Sheaf.IsFlasque (moduleUnderlyingSheaf ℐ) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_12_3 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.12.3:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on a ringed space, computed from
  injective resolutions by taking sections over an open subset;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `moduleUnderlyingSheaf`,
  `SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)`,
  `CategoryTheory.Sheaf.cohomologyOver_eq_homology_sections_of_injectiveResolution`;
- best owner abstraction: the Chapter 20 ringed-space owner `(RingedSpace.Modules X)`, together with the
  canonical underlying-abelian-sheaf bridge `moduleUnderlyingSheaf`; sections over `U` are the
  evaluation functor on `(RingedSpace.ringCatSheaf X)`, followed by the standard forgetful functor to abelian
  groups;
- primitive data: a ringed space `X`, an open subset `U`, a module `ℱ : (RingedSpace.Modules X)`, and an
  injective resolution `I : InjectiveResolution ℱ`;
- derived API: flasqueness of `moduleUnderlyingSheaf ℱ` and vanishing of the positive homology of
  the sections complex `Γ(U, I^•)`.

Source/core/bridge triage:
- `source-facing`: the vanishing statement for the positive homology of the sections complex of a
  chosen injective resolution;
- `core/canonical`: `(RingedSpace.Modules X)`, `moduleUnderlyingSheaf`, and evaluation on `U`;
- `bridge/view`: forgetting the `Γ(U, \mathcal O_X)`-module structure on sections down to
  `AddCommGrpCat`.

This file should therefore reuse the ringed-space owners already introduced in Chapter 20 rather
than spelling the same module category and underlying-sheaf data through raw
`ringedSpaceRingCatSheaf` composites. -/

instance moduleSectionsToAddCommGrp_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)) ⋙
      forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms := by
  letI : (SheafOfModules.forget (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms := by
    infer_instance
  letI : (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).PreservesZeroMorphisms := by
    infer_instance
  letI : (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    by infer_instance
  change
    (((SheafOfModules.forget (RingedSpace.ringCatSheaf X) ⋙
        PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)) ⋙
        forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms)
  infer_instance

-- Proof sketch: resolve `ℱ` by an injective resolution `I`, note from Lemma `20.12.2` that the
-- injective terms are flasque, and then apply the flasque-resolution criterion from the proof of
-- Lemma `13.15.6` to the sections functor on `U`. This forces the positive homology of the
-- sections complex `Γ(U, I^\bullet)` to vanish.
/-- Lemma 20.12.3: if an `\mathcal O_X`-module on a ringed space is flasque, then for every open
subset `U` and every injective resolution `I^\bullet` of that module, the positive homology of the
sections complex `Γ(U, I^\bullet)` vanishes; taking `U = X` recovers the global-sections case. -/
theorem flasque_module_higherSectionsHomology_isZero
    {X : RingedSpace.{u}}
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    (U : Opens X.carrier) (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque (moduleUnderlyingSheaf ℱ))
    (n : ℕ) (I : InjectiveResolution ℱ) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)).obj
        ((((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)) ⋙
            forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_12_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

-- Proof sketch: apply the Čech-to-cohomology spectral sequence of Lemma `20.11.5` to `ℱ`. By
-- Lemma `20.12.3`, all positive cohomology presheaves `\underline H^q(\mathcal F)` vanish because
-- `ℱ` is flasque, so the spectral sequence is concentrated in the `q = 0` row. The same lemma
-- also gives `H^p(U, \mathcal F) = 0` for `p > 0`, forcing the surviving row
-- `\check H^p(\mathcal U, \mathcal F)` to vanish.
/-- Lemma 20.12.4: if `\mathcal F` is a flasque `\mathcal O_X`-module on a ringed space `X`,
then for every open covering `𝒰` of `U`, the positive-degree Čech cohomology
`\check H^p(\mathcal U, \mathcal F)` vanishes. -/
theorem ringedSpaceCechCohomology_isZero_of_pos_of_flasque
    (h𝒰 : iSup (fun i ↦ (𝒰 i).left) = U)
    (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((ringedSpaceCechCohomologyDegree U 𝒰 p).obj.obj
        ((SheafOfModules.forget ((RingedSpace.ringCatSheaf X))).obj ℱ)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_12_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(RingedSpace.Hom.pushforward f).Additive]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

-- Proof sketch: by Lemma `20.7.3`, the underlying abelian sheaf of `R^p f_* ℱ` is the
-- sheafification of the presheaf `V ↦ H^p(f⁻¹(V), ℱ)`. Lemma `20.12.3` shows these cohomology
-- groups vanish for `p > 0` when `ℱ` is flasque, so the associated sheaf is zero; hence the
-- higher direct image itself is the zero `\mathcal O_Y`-module.
/-- Lemma 20.12.5: if an `\mathcal O_X`-module on a ringed space is flasque, then every positive
higher direct image along a morphism of ringed spaces is zero. -/
theorem higherDirectImageModule_isZero_of_flasque
    (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero (((RingedSpace.Hom.pushforward f).rightDerived p).obj ℱ) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_12_6 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {ι κ : Type u}

/-- The open subset obtained by taking an arbitrary union of finite Čech intersections of a
covering `𝒰`. -/
abbrev cech_union_of_finite_intersections
    (𝒰 : ι → Opens X) (s : κ → Σ n : ℕ, Fin (n + 1) → ι) : Opens X :=
  iSup fun k ↦ cech_intersection 𝒰 (s k).2

-- Proof sketch: each finite Čech intersection `U_{i_0 ... i_p}` is contained in every one of its
-- factors, hence in the union of the covering. Taking the supremum over the family `s` preserves
-- this containment.
/-- Any union of finite intersections of the members of `𝒰` is contained in the open set covered
by `𝒰`. -/
theorem cech_union_of_finite_intersections_le_cover
    (U : Opens X) (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U)
    (s : κ → Σ n : ℕ, Fin (n + 1) → ι) :
    cech_union_of_finite_intersections 𝒰 s ≤ U := sorry

-- Proof sketch: follow the textbook reduction to a flasque sheaf on the auxiliary space of
-- nonempty subsets of the index set. The surjectivity hypothesis exactly gives flasqueness of the
-- transported sheaf there, its Čech complex for the basic cover agrees with the Čech complex of
-- `(𝒰, ℱ)`, and Lemma `20.12.4` then forces the positive-degree Čech cohomology to vanish.
/-- Lemma 20.12.6: if every restriction map from `ℱ(U)` to an arbitrary union of finite
intersections of the covering opens is surjective, then the positive-degree Čech cohomology of
the covering with coefficients in `ℱ` vanishes. -/
theorem cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections
    (U : Opens X) (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U)
    (ℱ : X.Sheaf AddCommGrpCat.{u})
    (hres : ∀ {κ : Type u} (s : κ → Σ n : ℕ, Fin (n + 1) → ι),
      Function.Surjective
        (ℱ.1.map (homOfLE (cech_union_of_finite_intersections_le_cover U 𝒰 h𝒰 s)).op))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cech_cohomology 𝒰 ℱ.1 p) := sorry
