import Mathlib
import StacksProject_2024.Chap15.«15_6_3_1»
import StacksProject_2024.Chap15.Lemma_15_90_11
import StacksProject_2024.Chap15.Lemma_15_90_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

local notation "Away" => LocalizedModule.Away
local notation "fBase" => fun i ↦ algebraMap R S (f i)

/- Domain-style sampling for 15.90.14:
- primary domain: formal glueing for module categories and categorical equivalences;
- sampled owner declarations:
  `Glue`,
  `formalGlueingCan`,
  `formalGlueingCanAdjunction`,
  `Functor.IsEquivalence`;
- best owner abstraction: the source-facing statement should be the equivalence witness for the
  canonical functor `formalGlueingCan S f`;
- primitive data: only the canonical functor `formalGlueingCan S f` and the hypotheses
  `[Module.Flat R S]` and `Ideal.span (Set.range f) = ⊤`;
- derived API: the typeclass instance below. Any inverse functor and unit/counit isomorphisms are
  already provided canonically by `Functor.inv` and `Functor.asEquivalence`, so they should not be
  re-exposed here as parallel local owners.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCan_isEquivalence_of_flat_of_span_eq_top`;
- `core/canonical`: `Functor.IsEquivalence`;
- `bridge/view`: the instance `formalGlueingCan_isEquivalence`.
-/

-- Proof sketch: combine the right quasi-inverse from Lemma `15.90.12` with the module glueing
-- existence-and-uniqueness statement from Algebra, Lemma `10.24.5`. When `Ideal.span (Set.range f)
-- = ⊤`, every formal glueing datum comes from a unique `R`-module, giving essential surjectivity of
-- `Can`; together with the quasi-inverse statement of Lemma `15.90.12`, this yields an equivalence.
/-- Helper for Lemma 15.90.14: when the `fᵢ` span the unit ideal, the quotient map appearing in
Lemma `15.90.12` is the unique map between the zero quotients `R / ⊤` and `S / ⊤`. -/
lemma formalGlueing_quotientMap_bijective_of_span_eq_top
    (hspan : Ideal.span (Set.range f) = ⊤) :
    let I : Ideal R := Ideal.span (Set.range f)
    Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map) := by
  let q :
      R ⧸ (⊤ : Ideal R) →+* S ⧸ Ideal.map (algebraMap R S) (⊤ : Ideal R) :=
    Ideal.quotientMap (Ideal.map (algebraMap R S) (⊤ : Ideal R)) (algebraMap R S) Ideal.le_comap_map
  letI : Unique (S ⧸ Ideal.map (algebraMap R S) (⊤ : Ideal R)) := by
    -- The target quotient is also the zero ring because the image of `⊤` is `⊤`.
    simpa [Ideal.map_top] using (show Unique (S ⧸ (⊤ : Ideal S)) from inferInstance)
  have hq : Function.Bijective q := by
    constructor
    · intro x y _
      -- Both source points agree because `R / ⊤` is a subsingleton.
      exact Subsingleton.elim _ _
    · intro y
      -- Every target point is equal to the image of `0` for the same reason.
      exact ⟨0, Subsingleton.elim _ _⟩
  -- Replace `I` by `⊤` using the span hypothesis to match Lemma `15.90.12`.
  dsimp
  rw [hspan]
  simpa [Ideal.map_top, q] using hq

/-- Helper for Lemma 15.90.14: Lemma `15.90.12` upgrades the adjunction unit of the canonical
formal glueing functor to an isomorphism when the cover spans the unit ideal. -/
theorem formalGlueingCan_unit_isIso_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    IsIso ((formalGlueingCanAdjunction (S := S) (f := f)).unit) := by
  let e :=
    formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
      (S := S) (f := f)
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance))
      (formalGlueing_quotientMap_bijective_of_span_eq_top (S := S) (f := f) hspan)
  -- The quasi-inverse isomorphism from Lemma `15.90.12` identifies the adjunction unit with an
  -- isomorphism, which is the exact hypothesis needed for the standard fully faithful criterion.
  simpa using (formalGlueingCanAdjunction (S := S) (f := f)).isIso_unit_of_iso e

/-- Helper for Lemma 15.90.14: the canonical object attached to the glued module recovers the
original local module in degree `i`. -/
noncomputable def formalGlueingCan_gluedModule_localIso
    (X : Glue S f) (i : Fin t) :
    ((formalGlueingCan S f).obj (ModuleCat.of R X.glue.gluedModule)).glue.localModule i ≅
      X.glue.localModule i :=
  (X.glue.localizedProjectionLinearEquiv i).toModuleIso

/-- Helper for Lemma 15.90.14: the local component of the canonical map
`Can(X.glue.gluedModule) ⟶ X` is exactly the localized projection from the glued module to the
`i`-th local piece. -/
@[simp] theorem formalGlueingCan_gluedModule_localIso_hom_hom
    (X : Glue S f) (i : Fin t) :
    (formalGlueingCan_gluedModule_localIso (S := S) (f := f) X i).hom.hom =
      X.glue.localizedProjection i := by
  -- The module-category isomorphism is defined by packaging the canonical linear equivalence.
  rfl

/-- Helper for Lemma 15.90.14: the inverse local component is the inverse of the canonical
localized projection equivalence. -/
@[simp] theorem formalGlueingCan_gluedModule_localIso_inv_hom_apply
    (X : Glue S f) (i : Fin t) (x : X.glue.localModule i) :
    ((formalGlueingCan_gluedModule_localIso (S := S) (f := f) X i).inv.hom) x =
      (X.glue.localizedProjectionLinearEquiv i).symm x := by
  -- Unpacking `toModuleIso` exposes the inverse linear map of the localized projection equivalence.
  rfl

/-- Helper for Lemma 15.90.14: after localizing away from `f_i`, the base of
`Can(X.glue.gluedModule)` matches the base of `X` by the standard base-change comparison and the
canonical glued-module local equivalence. -/
noncomputable def formalGlueingCan_gluedModule_localizedBaseIso
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (f i))
        (Away (f i) ((formalGlueingCan S f).obj (ModuleCat.of R X.glue.gluedModule)).base) ≅
      ModuleCat.of (Localization.Away (f i)) (Away (f i) X.base) :=
  awayBaseChangeComparisonIso S (f i) (ModuleCat.of R X.glue.gluedModule) ≪≫
    (TensorProduct.AlgebraTensorModule.congr
      (X.glue.localizedProjectionLinearEquiv i)
      (.refl R S)).toModuleIso ≪≫
    (X.comparisonIso i).symm

/-- Helper for Lemma 15.90.14: the localized base comparison becomes the expected two-step source
proof transport after composing with the comparison isomorphism of `X`. -/
@[simp] theorem formalGlueingCan_gluedModule_localizedBaseIso_hom_comp_comparison
    (X : Glue S f) (i : Fin t) :
    (formalGlueingCan_gluedModule_localizedBaseIso (S := S) (f := f) X i).hom ≫
        (X.comparisonIso i).hom =
      (awayBaseChangeComparisonIso S (f i) (ModuleCat.of R X.glue.gluedModule) ≪≫
        (TensorProduct.AlgebraTensorModule.congr
          (X.glue.localizedProjectionLinearEquiv i)
          (.refl R S)).toModuleIso).hom := by
  -- Cancel the final inverse comparison isomorphism; the remaining composite is definitionally the
  -- transport used in the localized source-proof comparison square.
  simp [formalGlueingCan_gluedModule_localizedBaseIso]
  rfl

/-- Helper for Lemma 15.90.14: after applying `R → S`, the images of the cover elements still
generate the unit ideal on the base side. This is the cover needed for the second gluing step in
the source proof. -/
lemma formalGlueing_image_span_eq_top
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range (fun i ↦ algebraMap R S (f i))) = ⊤ := by
  -- Map the unit-ideal relation along `R → S`; the image of the range is the new standard cover.
  calc
    Ideal.span (Set.range (fun i ↦ algebraMap R S (f i))) =
        Ideal.span ((algebraMap R S) '' Set.range f) := by
          rw [Set.image_eq_range]
    _ = Ideal.map (algebraMap R S) (Ideal.span (Set.range f)) := by
          rw [Ideal.map_span]
    _ = Ideal.map (algebraMap R S) ⊤ := by rw [hspan]
    _ = ⊤ := by simp

/-- Helper for Lemma 15.90.14: extending scalars back to a ring that already acts on the module
recovers the original module. This is the standard tensor-counit bridge needed to transport the
`S`-side cover data through base-change squares. -/
private noncomputable def formalGlueing_extendScalarsSelfIso
    {A : Type u} [CommRing A] [Algebra R A] (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R M) ≅ M :=
  moduleCatExtendScalarsTensorIso R A (ModuleCat.of R M) ≪≫
    (Algebra.TensorProduct.rid R A (↑M)).toLinearEquiv.toModuleIso

/-- Helper for Lemma 15.90.14: localizing `R → S` away from `f_i` gives the ring map on the
`S`-side cover used by the source proof. -/
private noncomputable abbrev formalGlueingAwayBaseAlg (i : Fin t) :
    Localization.Away (f i) →ₐ[R] Localization.Away (fBase i) :=
  Localization.awayMapₐ (Algebra.ofId R S) (f i)

/-- Helper for Lemma 15.90.14: the underlying ring map of the `S`-side localization transport. -/
private noncomputable abbrev formalGlueingAwayBaseMap (i : Fin t) :
    Localization.Away (f i) →+* Localization.Away (fBase i) :=
  (formalGlueingAwayBaseAlg (S := S) (f := f) i).toRingHom

/-- Helper for Lemma 15.90.14: the localized base-change square for the image cover commutes. -/
private theorem formalGlueingAwayBaseSquare_comm (i : Fin t) :
    (formalGlueingAwayBaseMap (S := S) (f := f) i).comp
        (algebraMap R (Localization.Away (f i))) =
      (algebraMap S (Localization.Away (fBase i))).comp (algebraMap R S) := by
  -- Both composites send `x : R` to the standard localization class of `algebraMap R S x`.
  let hyMap :
      Submonoid.powers (f i) ≤
        Submonoid.comap (Algebra.ofId R S).toRingHom (Submonoid.powers (fBase i)) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  have hmap (x : R) :
      (formalGlueingAwayBaseAlg (S := S) (f := f) i)
          (algebraMap R (Localization.Away (f i)) x) =
        algebraMap S (Localization.Away (fBase i)) (algebraMap R S x) := by
    -- Rewrite both sides as localization classes and compare them through `Localization.awayMapₐ`.
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (f i))
      (Localization.Away (f i)) x]
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (fBase i))
      (Localization.Away (fBase i)) (algebraMap R S x)]
    simpa [formalGlueingAwayBaseAlg, Localization.awayMapₐ, hyMap] using
      (IsLocalization.map_mk' (Q := Localization.Away (fBase i)) hyMap x
        (1 : Submonoid.powers (f i)))
  ext x
  simpa [formalGlueingAwayBaseMap] using hmap x

/-- Helper for Lemma 15.90.14: the image-cover localization is an algebra over the original
away-localization. -/
private instance formalGlueingAwayBaseAlgebra (i : Fin t) :
    Algebra (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  (formalGlueingAwayBaseAlg (S := S) (f := f) i).toAlgebra

/-- Helper for Lemma 15.90.14: the image-cover localization sits in the expected scalar tower. -/
private instance formalGlueingAwayBaseTower (i : Fin t) :
    IsScalarTower R (Localization.Away (f i)) (Localization.Away (fBase i)) :=
  IsScalarTower.of_algebraMap_eq' (formalGlueingAwayBaseSquare_comm (S := S) (f := f) i).symm

/-- Helper for Lemma 15.90.14: on the `S`-side cover, the local module is the scalar extension of
the original local module along `R_{f_i} → S_{φ(f_i)}`. -/
private noncomputable abbrev formalGlueing_imageLocal
    (X : Glue S f) (i : Fin t) :
    ModuleCat (Localization.Away (fBase i)) :=
  (ModuleCat.extendScalars (formalGlueingAwayBaseMap (S := S) (f := f) i)).obj
    (X.glue.localModule i)

/-- Helper for Lemma 15.90.14: the canonical module `S ⊗[R] X.glue.gluedModule` realizes the
`i`-th local piece of the image cover after localizing at `φ(f_i)`. -/
private noncomputable def formalGlueing_imageCanonicalLocalIso
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i))
        (Away (fBase i)
          ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R X.glue.gluedModule))) ≅
      formalGlueing_imageLocal (S := S) (f := f) X i :=
  -- First localize the canonical `S`-module, then commute localization with base change, and
  -- finally identify the localized glued module with the prescribed local piece.
  (awayExtendScalarsIso (R := S) (fBase i)
      ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R X.glue.gluedModule))).symm ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap (S := S) (f := f) i)
        (algebraMap S (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R S)
        (formalGlueingAwayBaseSquare_comm (S := S) (f := f) i)).iso.app
          (ModuleCat.of R X.glue.gluedModule)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap (S := S) (f := f) i)).mapIso
      ((awayExtendScalarsIso (f i) (ModuleCat.of R X.glue.gluedModule)) ≪≫
        (X.glue.localizedProjectionLinearEquiv i).toModuleIso)

/-- Helper for Lemma 15.90.14: the canonical `S`-module
`S ⊗[R] X.glue.gluedModule` viewed through `Can` for the image cover
`i ↦ φ(f_i)`. -/
private noncomputable def formalGlueing_imageCanonicalObj
    (X : Glue S f) : Glue S fBase :=
  (formalGlueingCan S fBase).obj
    ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R X.glue.gluedModule))

/-- Helper for Lemma 15.90.14: localizing the canonical image-cover object at the overlap
`D(φ(f_i)φ(f_j))` transports its `k`-th local module to the explicit image local piece. -/
private noncomputable def formalGlueing_imageCanonicalOverlapIsoApp
    (X : Glue S f) (k : Fin t) (i : Fin t) (j : Fin t) :
    ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) ((formalGlueing_imageCanonicalObj (S := S) (f := f) X).glue.localModule k)) ≅
      ModuleCat.of (Localization.Away (fBase i * fBase j))
        (Away (fBase i * fBase j) (formalGlueing_imageLocal (S := S) (f := f) X k)) :=
  -- Localize the already constructed canonical local comparison to the pairwise overlap.
  (LinearEquiv.extendScalarsOfIsLocalization
      (Submonoid.powers (fBase i * fBase j))
      (Localization.Away (fBase i * fBase j))
      (awayLocalizeLinearEquiv (fBase i * fBase j)
        ((formalGlueing_imageCanonicalLocalIso (S := S) (f := f) X k).toLinearEquiv.restrictScalars S))).toModuleIso

/-- Helper for Lemma 15.90.14: the original base module `X.base` realizes the same image-cover
datum on `D(φ(f_i))` after localizing and transporting its comparison isomorphisms. -/
private noncomputable def formalGlueing_imageBaseLocalIso
    (X : Glue S f) (i : Fin t) :
    ModuleCat.of (Localization.Away (fBase i)) (Away (fBase i) X.base) ≅
      formalGlueing_imageLocal (S := S) (f := f) X i :=
  -- Follow the source proof literally: localize `X.base`, identify it with the localization of
  -- `S ⊗[R] X.base`, commute base change across `R_{f_i} → S_{φ(f_i)}`, and finish with the
  -- given comparison isomorphism of `X`.
  (awayExtendScalarsIso (R := S) (fBase i) (ModuleCat.of S X.base)).symm ≪≫
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (fBase i)))).mapIso
      (formalGlueing_extendScalarsSelfIso (R := R) (A := S) X.base) ≪≫
    (((moduleCatBaseChangeSquare
        (formalGlueingAwayBaseMap (S := S) (f := f) i)
        (algebraMap S (Localization.Away (fBase i)))
        (algebraMap R (Localization.Away (f i)))
        (algebraMap R S)
        (formalGlueingAwayBaseSquare_comm (S := S) (f := f) i)).iso.app
          (ModuleCat.of R X.base)).symm) ≪≫
    (ModuleCat.extendScalars (formalGlueingAwayBaseMap (S := S) (f := f) i)).mapIso
      ((awayExtendScalarsIso (f i) (ModuleCat.of R X.base)) ≪≫ X.comparisonIso i)

/-- Helper for Lemma 15.90.14: an `S`-linear map is bijective once all of its away-localizations
at the cover elements `fᵢ` are bijective. This is the Lean bridge from the source proof's
uniqueness on the `S`-cover `D(φ(f_i))` back to the existing locality criterion over `R`. -/
lemma formalGlueing_bijective_of_span_localizedAway
    (hspan : Ideal.span (Set.range f) = ⊤)
    {M N : ModuleCat.{max u v} S} (g : M ⟶ N)
    (hlocal : ∀ i : Fin t,
      Function.Bijective
        (LocalizedModule.map (Submonoid.powers (f i)) (g.hom.restrictScalars R))) :
    Function.Bijective g.hom := by
  -- Apply the standard local-to-global bijectivity criterion to the underlying `R`-linear map.
  have hR :
      Function.Bijective (g.hom.restrictScalars R) := by
    refine _root_.bijective_of_localized_span (Set.range f) hspan (g.hom.restrictScalars R) ?_
    intro r
    rcases r with ⟨r, i, rfl⟩
    simpa using hlocal i
  simpa using hR

/-- Helper for Lemma 15.90.14: once the canonical base morphism is known to be locally bijective,
the locality criterion upgrades it to the required base isomorphism. -/
noncomputable def formalGlueing_iso_of_span_localizedAway
    (hspan : Ideal.span (Set.range f) = ⊤)
    {M N : ModuleCat.{max u v} S} (g : M ⟶ N)
    (hlocal : ∀ i : Fin t,
      Function.Bijective
        (LocalizedModule.map (Submonoid.powers (f i)) (g.hom.restrictScalars R))) :
    M ≅ N :=
  (LinearEquiv.ofBijective g.hom <|
    formalGlueing_bijective_of_span_localizedAway (S := S) (f := f) hspan g hlocal).toModuleIso

/-- Helper for Lemma 15.90.14: exactness of the standard localization Cech complex over the
`S`-cover identifies an `S`-module with the kernel of its compatibility map. -/
noncomputable def away_localization_family_linearEquiv_ker_of_span_eq_top
    (hspanS : Ideal.span (Set.range fBase) = ⊤)
    (N : ModuleCat.{max u v} S) :
    N ≃ₗ[S] LinearMap.ker (awayLocalizationCompatibilityMap N fBase) := by
  let α : N →ₗ[S] ∀ i : Fin t, Away (fBase i) N :=
    awayLocalizationFamilyMap N fBase
  let β :
      (∀ i : Fin t, Away (fBase i) N) →ₗ[S]
        ∀ i : Fin t, ∀ j : Fin t, Away (fBase i * fBase j) N :=
    awayLocalizationCompatibilityMap N fBase
  let α' : N →ₗ[S] LinearMap.ker β :=
    LinearMap.codRestrict (LinearMap.ker β) α (by
      intro x
      -- Exactness records that every localization family coming from a global section satisfies
      -- the pairwise compatibility equations.
      refine LinearMap.mem_ker.2 ?_
      exact (away_localization_glueing_exact N fBase hspanS).2.2 ⟨x, rfl⟩)
  have hInj : Function.Injective α' := by
    intro x y hxy
    -- The kernel-valued map has the same underlying localization family map as `α`.
    have hα : α x = α y := by
      exact congrArg Subtype.val hxy
    exact (away_localization_glueing_exact N fBase hspanS).1 hα
  have hSurj : Function.Surjective α' := by
    intro y
    -- Exactness identifies the compatibility kernel with the image of the family map.
    rcases ((away_localization_glueing_exact N fBase hspanS).2 y.1).1 y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  -- The exact Cech sequence now upgrades the family map to a linear equivalence onto the kernel.
  exact LinearEquiv.ofBijective α' ⟨hInj, hSurj⟩

/-- Helper for Lemma 15.90.14: once a glued module is identified with the standard compatibility
kernel on the `S`-cover, exactness realizes it as the underlying global `S`-module. -/
noncomputable def away_module_glueing_realizationIso_of_span_eq_top
    (hspanS : Ideal.span (Set.range fBase) = ⊤)
    (glue : AwayModuleGlueing fBase) {N : ModuleCat.{max u v} S}
    (eKer : glue.gluedModule ≃ₗ[S] LinearMap.ker (awayLocalizationCompatibilityMap N fBase)) :
    ModuleCat.of S glue.gluedModule ≅ N :=
  (eKer.trans
    (away_localization_family_linearEquiv_ker_of_span_eq_top
      (R := R) (S := S) (f := f) hspanS N).symm).toModuleIso

/-- Helper for Lemma 15.90.14: the essential-surjectivity step reduces to constructing the
canonical base comparison `S ⊗[R] X.glue.gluedModule ≅ X.base` promised by the source proof. -/
noncomputable def formalGlueingCan_gluedModule_baseIso_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) (X : Glue S f) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R X.glue.gluedModule) ≅
      X.base := by
  -- Route correction: the source proof first compares the two `S`-module realizations of the
  -- image cover `D(φ(f_i))`, namely `X.base` and `S ⊗[R] X.glue.gluedModule`, before packaging the
  -- local comparison maps into an isomorphism in the formal glueing category.
  have hspanS :
      Ideal.span (Set.range (fun i ↦ algebraMap R S (f i))) = ⊤ :=
    formalGlueing_image_span_eq_top (S := S) (f := f) hspan
  -- The exactness owner above reduces the source proof to a single structural step: construct the
  -- common `S`-cover glueing datum together with its kernel comparison, then exactness turns that
  -- kernel identification into the required global base isomorphism.
  let _ := hspanS
  let _ :=
    away_localization_family_linearEquiv_ker_of_span_eq_top
      (R := R) (S := S) (f := f) hspanS X.base
  let _ :=
    away_module_glueing_realizationIso_of_span_eq_top
      (R := R) (S := S) (f := f) hspanS
  let _ := formalGlueing_imageBaseLocalIso (S := S) (f := f) X
  let _ := formalGlueing_imageCanonicalLocalIso (S := S) (f := f) X
  let _ := formalGlueing_imageCanonicalObj (S := S) (f := f) X
  let _ := formalGlueing_imageCanonicalOverlapIsoApp (S := S) (f := f) X
  let _ := hspan
  -- TODO: use the explicit image-cover object over `fBase` built above, transport its overlap
  -- localizations through `formalGlueing_imageCanonicalOverlapIsoApp`, and compare its glued module
  -- with the standard localization kernels of `X.base` and `S ⊗[R] X.glue.gluedModule`.
  sorry

/-- Helper for Lemma 15.90.14: the essential-surjectivity step reduces to constructing the
canonical isomorphism from `Can(X.glue.gluedModule)` back to `X`. -/
noncomputable def formalGlueingCan_gluedModule_objIso_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) (X : Glue S f) :
    ((formalGlueingCan S f).obj (ModuleCat.of R X.glue.gluedModule)) ≅ X := by
  -- Route correction: once the source-faithful base comparison is isolated as a separate helper,
  -- the remaining step is to package that base isomorphism with the canonical local isomorphisms
  -- via `FormalGlueingDatum.Hom.ext`.
  let _ :=
    formalGlueingCan_gluedModule_baseIso_of_span_eq_top (S := S) (f := f) hspan X
  let _ := formalGlueingCan_gluedModule_localIso (S := S) (f := f) X
  -- TODO: after the base isomorphism is upgraded with its localized comparison formula, assemble
  -- the morphism in `Glue` from that base map and the local maps
  -- `formalGlueingCan_gluedModule_localIso`, then close the inverse identities by
  -- `FormalGlueingDatum.Hom.ext`.
  sorry

/-- Helper for Lemma 15.90.14: Lemma `15.90.12` upgrades to full faithfulness of the canonical
formal glueing functor by the standard adjunction criterion `L ⋙ R ≅ 𝟭`. -/
noncomputable def formalGlueingCan_fullyFaithful_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    (formalGlueingCan S f).FullyFaithful := by
  let e :
      formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭 (ModuleCat R) :=
    formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
      (S := S) (f := f)
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance))
      (formalGlueing_quotientMap_bijective_of_span_eq_top (S := S) (f := f) hspan)
  -- Lemma `15.90.12` already supplies the source-faithful composite-isomorphic-to-identity input,
  -- so the adjunction criterion yields full faithfulness with no further local calculations.
  exact (formalGlueingCanAdjunction (S := S) (f := f)).fullyFaithfulLOfCompIsoId e

/-- Helper for Lemma 15.90.14: the remaining source-proof content is essential surjectivity of
`Can`, obtained by gluing the local modules and then comparing the two induced `S`-modules on the
standard cover. -/
lemma formalGlueingCan_essSurj_of_flat_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.EssSurj (formalGlueingCan S f) := by
  refine ⟨fun X ↦ ?_⟩
  -- The source proof picks the glued module itself as the preimage object; the only remaining work
  -- is the canonical objectwise isomorphism `Can(X.glue.gluedModule) ≅ X`.
  exact ⟨ModuleCat.of R X.glue.gluedModule,
    ⟨formalGlueingCan_gluedModule_objIso_of_span_eq_top (S := S) (f := f) hspan X⟩⟩

/-- Lemma 15.90.14: if `φ : R → S` is a flat ring map and the generators `f₁, \ldots, fₜ`
generate the unit ideal of `R`, then the canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, …, fₜ)` is an equivalence of categories, where
`Glue(R → S, f₁, …, fₜ)` is the genuine formal glueing category from Remark `15.90.10`. -/
theorem formalGlueingCan_isEquivalence_of_flat_of_span_eq_top [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) := by
  let hFF := formalGlueingCan_fullyFaithful_of_span_eq_top (S := S) (f := f) hspan
  -- Once Lemma `15.90.12` gives full faithfulness and the source glued-module argument supplies
  -- essential surjectivity, the canonical equivalence criterion is immediate.
  exact
    { faithful := hFF.faithful
      full := hFF.full
      essSurj := formalGlueingCan_essSurj_of_flat_of_span_eq_top (S := S) (f := f) hspan }

/-- The equivalence instance attached to formal glueing when the `fᵢ` generate the unit ideal. -/
noncomputable instance formalGlueingCan_isEquivalence [Module.Flat R S]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Functor.IsEquivalence (formalGlueingCan S f) :=
  formalGlueingCan_isEquivalence_of_flat_of_span_eq_top f hspan

end
