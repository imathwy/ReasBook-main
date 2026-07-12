import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Lemma_15_90_11
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u w

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/-- Helper for Lemma 15.90.13: an `R_{f_i}`-module is automatically an `R`-module in the expected
scalar tower. -/
private instance formalGlueing_localized_module_tower
    (a : R) (M : ModuleCat.{max u w} (Localization.Away a)) :
    IsScalarTower R (Localization.Away a) M :=
  IsScalarTower.restrictScalars R (Localization.Away a) M

/-- Helper for Lemma 15.90.13: tensoring an `R_{a}`-module with the base ring `S` still carries
the expected scalar tower from `R` through `R_a`. -/
private instance formalGlueing_localized_tensor_module_tower
    (a : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] :
    IsScalarTower R (Localization.Away a) (TensorProduct R M S) where
  smul_assoc r s x := by
    -- Proof comment: the tensor product scalar action comes from the left tensor factor, so the
    -- scalar-tower compatibility reduces to the corresponding associativity on `M`.
    induction x using TensorProduct.induction_on with
    | zero =>
        rfl
    | tmul m t =>
        rfl
    | add x y hx hy =>
        simp [smul_add, hx, hy]

/- Domain-style sampling:
- primary domain: formal glueing for module categories, with the genuine glueing category carrying
  comparison and overlap isomorphisms.
- inspected owner declarations:
  `FormalGlueingDatum`,
  `FormalGlueingDatum.Hom`,
  `AwayModuleGlueing`,
  `LocalizedModule.equivTensorProduct`,
  `formalGlueingCan`.
- best owner abstraction:
  the source-facing category `FormalGlueingDatum f` from `Remark 15.90.10`, with the overlap side
  built from the chapter-local localization-glueing owner `AwayModuleGlueing` and with genuine
  glueing morphisms encoded by `FormalGlueingDatum.Hom`.
- primitive data:
  the base `S`-module, the localized `R_(fᵢ)`-modules, the comparison isomorphisms, and the
  overlap isomorphisms.
- derived API in this file:
  exactness of `formalGlueingCan S f` under flatness and preservation of colimits by
  `formalGlueingCan S f`.
- layer:
  `source-facing`; this lemma is about the actual glueing category `Glue(R → S, f₁, …, fₜ)`, not a
  surrogate product presentation.
-/

-- Proof sketch: under flatness, localization and tensor product are exact on the comparison and
-- overlap terms, so the canonical functor `Can` is exact on the abelian glueing category.
/-- Helper for Lemma 15.90.13: forget a formal glueing datum to its base `S`-module. -/
noncomputable def formalGlueingBaseForget :
    Glue S f ⥤ ModuleCat.{max u w} S where
  obj X := X.base
  map φ := φ.base

/-- Helper for Lemma 15.90.13: forget a formal glueing datum to its `i`-th localized module. -/
noncomputable def formalGlueingLocalForget (i : Fin t) :
    Glue S f ⥤ ModuleCat.{max u w} (Localization.Away (f i)) where
  obj X := X.glue.localModule i
  map φ := φ.glue.localMap i

/-- Helper for Lemma 15.90.13: record the base and all local pieces of a formal glueing datum at
once. -/
noncomputable def formalGlueingComponentsForget :
    Glue S f ⥤
      ModuleCat.{max u w} S ×
        ((i : Fin t) → ModuleCat.{max u w} (Localization.Away (f i))) where
  obj X := ⟨X.base, fun i ↦ X.glue.localModule i⟩
  map φ := ⟨φ.base, fun i ↦ φ.glue.localMap i⟩

/-- Helper for Lemma 15.90.13: the component functor detects morphisms because formal glueing
morphisms are determined by their base and local components. -/
noncomputable instance formalGlueingComponentsForget_faithful :
    Functor.Faithful (formalGlueingComponentsForget (S := S) (f := f)) where
  map_injective := by
    intro X Y φ ψ h
    -- Equality of the component tuple gives equality of the base map and each local map.
    change
      (φ.base, fun i ↦ φ.glue.localMap i) =
        (ψ.base, fun i ↦ ψ.glue.localMap i) at h
    apply FormalGlueingDatum.Hom.ext
    · exact congrArg Prod.fst h
    · intro i
      exact congrFun (congrArg Prod.snd h) i

/-- Helper for Lemma 15.90.13: localizing a composite of `R`-linear maps between `A`-modules
agrees with the composite of the localized maps. -/
lemma formalGlueing_localized_map_comp
    {A : Type u} [CommRing A] [Algebra R A] (a : R)
    {M N P : ModuleCat.{max u w} A} (g : M ⟶ N) (h : N ⟶ P) :
    ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers a) (((g ≫ h).hom).restrictScalars R)) =
      ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers a) (g.hom.restrictScalars R)) ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers a) (h.hom.restrictScalars R)) := by
  -- The away-localization owner composes pointwise on localization generators.
  ext x
  change
    (LocalizedModule.map (Submonoid.powers a)
      ((h.hom.restrictScalars R).comp (g.hom.restrictScalars R))) x =
      ((LocalizedModule.map (Submonoid.powers a) (h.hom.restrictScalars R)).comp
        (LocalizedModule.map (Submonoid.powers a) (g.hom.restrictScalars R))) x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      rw [LinearMap.comp_apply]
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
      rfl

/-- Helper for Lemma 15.90.13: localizing the identity map gives the identity morphism on the
away-localized module category. -/
lemma formalGlueing_localized_map_id
    {A : Type u} [CommRing A] [Algebra R A] (a : R)
    (M : ModuleCat.{max u w} A) :
    ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers a) (LinearMap.id : M →ₗ[R] M)) =
      𝟙 (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) := by
  -- The localization owner acts pointwise on generators, so the identity map stays the identity.
  ext x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      change
        (LocalizedModule.map (Submonoid.powers a) (LinearMap.id : M →ₗ[R] M))
            (LocalizedModule.mk y s) =
          LocalizedModule.mk y s
      rw [LocalizedModule.map_mk]
      rfl

-- Proof sketch: first identify the raw tensor/local linear maps, then package the result back in
-- `ModuleCat`.
/-- Helper for Lemma 15.90.13: the underlying tensor-local linear maps compose pointwise on pure
tensors. -/
lemma formalGlueing_tensor_local_map_comp_raw
    (a : R) {M N P : ModuleCat.{max u w} (Localization.Away a)}
    (g : M ⟶ N) (h : N ⟶ P) :
    ((LinearMap.extendScalarsOfIsLocalizationEquiv
        (Submonoid.powers a) (Localization.Away a))
        (TensorProduct.map (((g ≫ h).hom).restrictScalars R)
          (LinearMap.id : S →ₗ[R] S))) =
      (((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers a) (Localization.Away a))
          (TensorProduct.map (h.hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))).comp
        (((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers a) (Localization.Away a))
          (TensorProduct.map (g.hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))) := by
  -- Proof comment: the owner-level tensor/localization construction already composes on pure
  -- tensors, so extensionality reduces the claim to reflexivity.
  ext x
  rfl

-- TODO: rebuild this helper with the correctly typed equality of `ModuleCat` morphisms, starting
-- from the linear-map composition identity before packaging it with `ModuleCat.ofHom`.
lemma formalGlueing_tensor_local_map_comp
    (a : R) {M N P : ModuleCat.{max u w} (Localization.Away a)}
    (g : M ⟶ N) (h : N ⟶ P) :
    ModuleCat.ofHom
        ((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers a) (Localization.Away a))
          (TensorProduct.map (((g ≫ h).hom).restrictScalars R)
            (LinearMap.id : S →ₗ[R] S))) =
      (ModuleCat.ofHom
          ((LinearMap.extendScalarsOfIsLocalizationEquiv
            (Submonoid.powers a) (Localization.Away a))
            (TensorProduct.map (g.hom.restrictScalars R)
              (LinearMap.id : S →ₗ[R] S)))) ≫
        (ModuleCat.ofHom
          ((LinearMap.extendScalarsOfIsLocalizationEquiv
            (Submonoid.powers a) (Localization.Away a))
            (TensorProduct.map (h.hom.restrictScalars R)
              (LinearMap.id : S →ₗ[R] S)))) := by
  -- Proof comment: after correcting the order of the raw linear-map composition, the
  -- corresponding `ModuleCat` morphisms agree pointwise on the tensor owner.
  ext x
  rfl

/-- Helper for Lemma 15.90.13: the away-localization/extension-of-scalars comparison sends the
standard pure tensor to the denominator-`1` localization generator. -/
lemma formalGlueing_awayExtendScalarsIso_hom_apply_one_tmul
    (a : R) (M : ModuleCat.{max u w} R) (x : M) :
    ((awayExtendScalarsIso (R := R) a M).hom.hom) ((1 : Localization.Away a) ⊗ₜ[R] x) =
      (LocalizedModule.mk x 1 : LocalizedModule.Away a M) := sorry

/-- Helper for Lemma 15.90.13: `awayExtendScalarsIso` is natural in the underlying `R`-linear
module map. -/
lemma formalGlueing_awayExtendScalarsIso_naturality
    (a : R) {M N : ModuleCat.{max u w} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away a))).map g ≫
        (awayExtendScalarsIso (R := R) a N).hom =
      (awayExtendScalarsIso (R := R) a M).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers a) g.hom) := sorry

/-- Helper for Lemma 15.90.13: the base component of `Can` is the flat extension-of-scalars
functor, so it already preserves finite limits. -/
-- TODO: re-express this through the owner-level base-component functor with the universe-aligned
-- `PreservesFiniteLimits` instance for `ModuleCat.extendScalars`.
lemma formalGlueingCan_base_preserves_finite_limits [Module.Flat R S] :
    PreservesFiniteLimits
      (formalGlueingCan S f ⋙ formalGlueingBaseForget (S := S) (f := f)) := by
  -- Proof comment: the base component of `Can` is definitionally `extendScalars` to `S`.
  let F : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} S :=
    ModuleCat.extendScalars (algebraMap R S)
  change PreservesFiniteLimits F
  let hflat : (algebraMap R S).Flat :=
    RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance)
  letI : PreservesFiniteLimits F := by
    dsimp [F]
    exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (f := algebraMap R S) hflat
  infer_instance

/-- Helper for Lemma 15.90.13: the `i`-th local component of `Can` is the canonical localization
extension-of-scalars functor. -/
-- TODO: replace the brittle tensor induction with the canonical naturality lemma for
-- `awayExtendScalarsIso` on the local component of `formalGlueingCan`.
noncomputable def formalGlueingLocalForget_comp_can_natIso (i : Fin t) :
    ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))) ≅
      formalGlueingCan S f ⋙ formalGlueingLocalForget (S := S) (f := f) i := by
  -- Proof comment: on each object this is exactly the owner comparison `awayExtendScalarsIso`,
  -- and the naturality square is the file-local bridge above.
  refine NatIso.ofComponents (fun M ↦ awayExtendScalarsIso (R := R) (f i) M) ?_
  intro M N g
  simpa using formalGlueing_awayExtendScalarsIso_naturality
    (R := R) (a := f i) g

/-- Helper for Lemma 15.90.13: each local component of `Can` preserves finite limits because it is
nat-isomorphic to localization as extension of scalars along a flat algebra map. -/
-- TODO: deduce this from the repaired natural isomorphism above and the flatness of
-- `R → R_{f_i}`.
lemma formalGlueingCan_local_preserves_finite_limits [Module.Flat R S] (i : Fin t) :
    PreservesFiniteLimits
      (formalGlueingCan S f ⋙ formalGlueingLocalForget (S := S) (f := f) i) := by
  -- Proof comment: transfer finite-limit preservation across the repaired local-component
  -- natural isomorphism from flat extension of scalars to `R_{f_i}`.
  let F : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} (Localization.Away (f i)) :=
    ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))
  let hflat : (algebraMap R (Localization.Away (f i))).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (show Module.Flat R (Localization.Away (f i)) from inferInstance)
  letI : PreservesFiniteLimits F := by
    dsimp [F]
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (f := algebraMap R (Localization.Away (f i))) hflat
  let e : F ≅ formalGlueingCan S f ⋙ formalGlueingLocalForget (S := S) (f := f) i :=
    formalGlueingLocalForget_comp_can_natIso (R := R) (S := S) (f := f) i
  exact preservesFiniteLimits_of_natIso e

/-- Helper for Lemma 15.90.13: after forgetting to the base component and all local components,
the canonical formal glueing functor still preserves finite limits. -/
-- TODO: rebuild this componentwise preserved-limit cone after the base and local preservation
-- lemmas are repaired.
lemma formalGlueingCan_components_preserves_limits_of_shape [Module.Flat R S]
    {J : Type _} [Category J] [Finite J] :
    PreservesLimitsOfShape J
      (formalGlueingCan S f ⋙ formalGlueingComponentsForget (S := S) (f := f)) := sorry

/-- Helper for Lemma 15.90.13: after forgetting to the base component and all local components,
the canonical formal glueing functor still preserves finite limits. -/
-- TODO: package the repaired shape-wise preservation lemma into `PreservesFiniteLimits`.
lemma formalGlueingCan_components_preserves_finite_limits [Module.Flat R S] :
    PreservesFiniteLimits
      (formalGlueingCan S f ⋙ formalGlueingComponentsForget (S := S) (f := f)) := sorry

/-- Helper for Lemma 15.90.13: the universal lift in the component product cone has the expected
base and local projections against every cone leg. -/
-- TODO: recover these componentwise factorization identities once the product-limit reflection
-- route is stabilized.
lemma formalGlueingComponentsForget_lift_fac
    {J : Type _} [Category J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c)) :
    (∀ j,
        Prod.fst (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s)) ≫
          (c.π.app j).base =
        (s.π.app j).base) ∧
      (∀ i j,
        (Prod.snd (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s)) i) ≫
          (c.π.app j).glue.localMap i =
        (s.π.app j).glue.localMap i) := sorry

/-- Helper for Lemma 15.90.13: after postcomposing with any cone leg, the componentwise lift
already satisfies the required overlap compatibility square. -/
-- TODO: derive this from the repaired component-factorization lemma and the overlap squares of the
-- cone legs.
lemma formalGlueingComponentsForget_lift_overlaps_comm_app
    {J : Type _} [Category J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c))
    (i j : Fin t) (k : J) :
    ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((Prod.snd
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              i).hom.restrictScalars R)) ≫
      (c.pt.glue.overlapIso i j).hom ≫
      ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          (((c.π.app k).glue.localMap j).hom.restrictScalars R)) =
    (s.pt.glue.overlapIso i j).hom ≫
      ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((Prod.snd
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              j).hom.restrictScalars R)) ≫
      ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          (((c.π.app k).glue.localMap j).hom.restrictScalars R)) := sorry

/-- Helper for Lemma 15.90.13: after postcomposing with any cone leg, the componentwise lift
already satisfies the required comparison square. -/
-- TODO: re-establish the postcomposed comparison identity once the tensor-local transport helper
-- is available in a stable form.
lemma formalGlueingComponentsForget_lift_comparison_comm_app [Module.Flat R S]
    {J : Type _} [Category J] [Finite J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c))
    (i : Fin t) (k : J) :
    ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i))
          ((Prod.fst
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              ).hom.restrictScalars R)) ≫
      (c.pt.comparisonIso i).hom ≫
      (ModuleCat.ofHom
        ((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (f i)) (Localization.Away (f i)))
          (TensorProduct.map
            (((c.π.app k).glue.localMap i).hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))) =
    (s.pt.comparisonIso i).hom ≫
      (ModuleCat.ofHom
        ((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (f i)) (Localization.Away (f i)))
          (TensorProduct.map
            ((Prod.snd
                (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
                i).hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))) ≫
      (ModuleCat.ofHom
        ((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (f i)) (Localization.Away (f i)))
          (TensorProduct.map
            (((c.π.app k).glue.localMap i).hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))) := sorry

/-- Helper for Lemma 15.90.13: forget the component product to its base `S`-module. -/
-- TODO: if the exactness route continues to use this helper, restore the explicit functor term.
noncomputable def formalGlueingComponentsBaseComponentForget :
    (ModuleCat.{max u w} S ×
      ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k)))) ⥤
      ModuleCat.{max u w} S where
  obj X := X.1
  map φ := φ.1
  map_id X := rfl
  map_comp φ ψ := rfl

/-- Helper for Lemma 15.90.13: forget the component product to the whole local family. -/
-- TODO: if the exactness route continues to use this helper, restore the explicit product
-- projection functor.
noncomputable def formalGlueingComponentsLocalFamilyForget :
    (ModuleCat.{max u w} S ×
      ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k)))) ⥤
      ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k))) where
  obj X := X.2
  map φ := φ.2
  map_id X := rfl
  map_comp φ ψ := rfl

/-- Helper for Lemma 15.90.13: evaluate the local family at the `j`-th localization. -/
-- TODO: restore the evaluation functor once the local-family descent route is resumed.
noncomputable def formalGlueingLocalFamilyEval (j : Fin t) :
    ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k))) ⥤
      ModuleCat.{max u w} (Localization.Away (f j)) where
  obj X := X j
  map φ := φ j
  map_id X := rfl
  map_comp φ ψ := rfl

/-- Helper for Lemma 15.90.13: localize an already `f_j`-localized module further away from
`f_i f_j`. -/
-- TODO: rebuild this functor with explicit `map_id` and `map_comp` proofs from
-- `formalGlueing_localized_map_comp`.
noncomputable def formalGlueingPairwiseLocalizeLocalComponent (i j : Fin t) :
    ModuleCat.{max u w} (Localization.Away (f j)) ⥤
      ModuleCat.{max u w} (Localization.Away (f i * f j)) where
  obj M := ModuleCat.of (Localization.Away (f i * f j)) (LocalizedModule.Away (f i * f j) M)
  map g := ModuleCat.ofHom
    (LocalizedModule.map (Submonoid.powers (f i * f j)) (g.hom.restrictScalars R))
  map_id M := formalGlueing_localized_map_id (R := R) (a := f i * f j) M
  map_comp g h := formalGlueing_localized_map_comp (R := R) (a := f i * f j) g h

/-- Helper for Lemma 15.90.13: localize the base `S`-module away from `f_i`. -/
-- TODO: rebuild this functor with explicit `map_id` and `map_comp` proofs from
-- `formalGlueing_localized_map_comp`.
noncomputable def formalGlueingLocalizedBaseComponent (i : Fin t) :
    ModuleCat.{max u w} S ⥤ ModuleCat.{max u w} (Localization.Away (f i)) where
  obj M := ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)
  map g := ModuleCat.ofHom
    (LocalizedModule.map (Submonoid.powers (f i)) (g.hom.restrictScalars R))
  map_id M := formalGlueing_localized_map_id (R := R) (a := f i) M
  map_comp g h := formalGlueing_localized_map_comp (R := R) (a := f i) g h

/-- Helper for Lemma 15.90.13: the further localization functor on the `j`-th local component is
restriction of scalars to `R` followed by flat scalar extension to `R_{f_if_j}`. -/
-- TODO: identify the repaired pairwise-localization functor with the canonical away-extension
-- owner through a stable natural isomorphism.
noncomputable def formalGlueingPairwiseLocalizeLocalComponent_natIso (i j : Fin t) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j))) ⋙
      ModuleCat.extendScalars (algebraMap R (Localization.Away (f i * f j)))) ≅
      formalGlueingPairwiseLocalizeLocalComponent (R := R) (f := f) i j := sorry

/-- Helper for Lemma 15.90.13: localizing the base component is restriction of scalars to `R`
followed by flat scalar extension to `R_{f_i}`. -/
-- TODO: identify the repaired localized-base functor with the away-extension owner.
noncomputable def formalGlueingLocalizedBaseComponent_natIso (i : Fin t) :
    (ModuleCat.restrictScalars (algebraMap R S) ⋙
      ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))) ≅
      formalGlueingLocalizedBaseComponent (R := R) (S := S) (f := f) i := sorry

/-- Helper for Lemma 15.90.13: further localizing the `j`-th local component preserves finite
limits because it is flat extension of scalars after restriction. -/
-- TODO: deduce this from the repaired pairwise-localization natural isomorphism.
lemma formalGlueingPairwiseLocalizeLocalComponent_preserves_finite_limits
    (i j : Fin t) [Module.Flat R (Localization.Away (f i * f j))] :
    PreservesFiniteLimits
      (formalGlueingPairwiseLocalizeLocalComponent (R := R) (f := f) i j) := sorry

/-- Helper for Lemma 15.90.13: localizing the base component preserves finite limits because it is
flat scalar extension after restriction. -/
-- TODO: deduce this from the repaired localized-base natural isomorphism.
lemma formalGlueingLocalizedBaseComponent_preserves_finite_limits
    (i : Fin t) [Module.Flat R (Localization.Away (f i))] :
    PreservesFiniteLimits
      (formalGlueingLocalizedBaseComponent (R := R) (S := S) (f := f) i) := sorry

/-- Helper for Lemma 15.90.13: forget the component product to the pairwise localization of the
`j`-th local factor. This is the explicit overlap descent functor from the source proof. -/
-- TODO: reassemble this composite once the local-family and pairwise-localization functors are
-- restored.
noncomputable def formalGlueingPairwiseLocalizedLocalComponentForget (i j : Fin t) :
    (ModuleCat.{max u w} S ×
      ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k)))) ⥤
      ModuleCat.{max u w} (Localization.Away (f i * f j)) :=
  formalGlueingComponentsLocalFamilyForget (R := R) (f := f) ⋙
    formalGlueingLocalFamilyEval (R := R) (f := f) j ⋙
    formalGlueingPairwiseLocalizeLocalComponent (R := R) (f := f) i j

/-- Helper for Lemma 15.90.13: forget the component product to the localization of the base
factor. This is the explicit comparison descent functor from the source proof. -/
-- TODO: reassemble this composite once the base projection and localized-base functors are
-- restored.
noncomputable def formalGlueingLocalizedBaseComponentForget (i : Fin t) :
    (ModuleCat.{max u w} S ×
      ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k)))) ⥤
      ModuleCat.{max u w} (Localization.Away (f i)) :=
  formalGlueingComponentsBaseComponentForget (R := R) (f := f) ⋙
    formalGlueingLocalizedBaseComponent (R := R) (S := S) (f := f) i

/-- Helper for Lemma 15.90.13: projecting a limiting component-product cone to the base component
still yields a limiting cone. -/
-- TODO: reprove this by adjoining the fixed local family to a base cone candidate.
noncomputable def formalGlueingComponentsForget_base_component_isLimit
    {J : Type _} [Category J] {K : J ⥤ Glue S f} {c : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c)) :
    IsLimit
      ((formalGlueingComponentsForget (S := S) (f := f) ⋙
          formalGlueingComponentsBaseComponentForget (R := R) (f := f)).mapCone c) := sorry

/-- Helper for Lemma 15.90.13: projecting a limiting component-product cone to the whole local
family still yields a limiting cone. -/
-- TODO: reprove this by adjoining the fixed base component to a local-family cone candidate.
noncomputable def formalGlueingComponentsForget_local_family_isLimit
    {J : Type _} [Category J] {K : J ⥤ Glue S f} {c : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c)) :
    IsLimit
      ((formalGlueingComponentsForget (S := S) (f := f) ⋙
          formalGlueingComponentsLocalFamilyForget (R := R) (f := f)).mapCone c) := sorry

/-- Helper for Lemma 15.90.13: evaluating a limiting cone in the local-family category at the
`j`-th component still yields a limiting cone. -/
-- TODO: reprove this by adjoining the evaluated component back into the full local-family cone.
noncomputable def formalGlueingLocalFamilyEval_isLimit
    {J : Type _} [Category J]
    {K : J ⥤ ((k : Fin t) → ModuleCat.{max u w} (Localization.Away (f k)))} {c : Cone K}
    (hc : IsLimit c) (j : Fin t) :
    IsLimit ((formalGlueingLocalFamilyEval (R := R) (f := f) j).mapCone c) := sorry

/-- Helper for Lemma 15.90.13: the explicit pairwise-localized `j`-local cone obtained by applying
the overlap descent functor to the limiting component cone. -/
-- TODO: reinstate this abbreviation after the overlap descent functor has been rebuilt.
noncomputable abbrev formalGlueingComponentsForget_pairwise_localized_local_cone
    {J : Type _} [Category J] {K : J ⥤ Glue S f} (c : Cone K) (i j : Fin t) :
    Cone
      (K ⋙ formalGlueingComponentsForget (S := S) (f := f) ⋙
        formalGlueingPairwiseLocalizedLocalComponentForget (R := R) (f := f) i j) :=
  ((formalGlueingComponentsForget (S := S) (f := f)) ⋙
    formalGlueingPairwiseLocalizedLocalComponentForget (R := R) (f := f) i j).mapCone c

/-- Helper for Lemma 15.90.13: the legs of the explicit pairwise-localized local cone are exactly
the localized `j`-local maps appearing in the overlap app lemma. -/
-- TODO: recover this definitional computation after the repaired cone abbreviation is in place.
lemma formalGlueingComponentsForget_pairwise_localized_local_cone_π_app
    {J : Type _} [Category J] {K : J ⥤ Glue S f} (c : Cone K) (i j : Fin t) (k : J) :
    (formalGlueingComponentsForget_pairwise_localized_local_cone
        (R := R) (S := S) (f := f) c i j).π.app k =
      ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          (((c.π.app k).glue.localMap j).hom.restrictScalars R)) := by
  -- Unfolding the composite forgetful functors shows that the cone leg is the localized local map.
  rfl

/-- Helper for Lemma 15.90.13: the explicit pairwise-localized local cone obtained from the
component-product limit cone is itself limiting. -/
-- TODO: rebuild this by composing the repaired local-family limit descent, evaluation, and
-- pairwise-localization preservation lemmas.
noncomputable def formalGlueingComponentsForget_pairwise_localized_local_isLimit
    [Module.Flat R (Localization.Away (f i * f j))]
    {J : Type _} [Category J] [Finite J] {K : J ⥤ Glue S f} {c : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c))
    (i j : Fin t) :
    IsLimit
      (formalGlueingComponentsForget_pairwise_localized_local_cone
        (R := R) (S := S) (f := f) c i j) := sorry

/-- Helper for Lemma 15.90.13: the explicit localized base cone obtained by applying the
comparison descent functor to the limiting component cone. -/
-- TODO: reinstate this abbreviation after the localized-base descent functor has been rebuilt.
noncomputable abbrev formalGlueingComponentsForget_localized_base_cone
    {J : Type _} [Category J] {K : J ⥤ Glue S f} (c : Cone K) (i : Fin t) :
    Cone
      (K ⋙ formalGlueingComponentsForget (S := S) (f := f) ⋙
        formalGlueingLocalizedBaseComponentForget (R := R) (f := f) i) :=
  ((formalGlueingComponentsForget (S := S) (f := f)) ⋙
    formalGlueingLocalizedBaseComponentForget (R := R) (f := f) i).mapCone c

/-- Helper for Lemma 15.90.13: the legs of the explicit localized base cone are exactly the
localized base maps appearing after cancelling the comparison isomorphisms. -/
-- TODO: recover this definitional computation after the repaired localized-base cone abbreviation
-- is in place.
lemma formalGlueingComponentsForget_localized_base_cone_π_app
    {J : Type _} [Category J] {K : J ⥤ Glue S f} (c : Cone K) (i : Fin t) (k : J) :
    (formalGlueingComponentsForget_localized_base_cone
        (R := R) (S := S) (f := f) c i).π.app k =
      ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i))
          (((c.π.app k).base).hom.restrictScalars R)) := by
  -- Unfolding the base projection and base localization functor gives the stated localized leg.
  rfl

/-- Helper for Lemma 15.90.13: the postcomposed overlap identities descend to the raw overlap
square on the lifted local maps. -/
-- TODO: descend the postcomposed overlap identities by `IsLimit.hom_ext` once the explicit
-- pairwise-localized local cone is available again.
lemma formalGlueingComponentsForget_lift_overlaps_comm
    {J : Type _} [Category J] [Finite J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c))
    (i j : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((Prod.snd
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              i).hom.restrictScalars R)))
      (s.pt.glue.overlapIso i j).hom
      (c.pt.glue.overlapIso i j).hom
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i * f j))
          ((Prod.snd
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              j).hom.restrictScalars R))) := sorry

/-- Helper for Lemma 15.90.13: the postcomposed comparison identities descend to the raw
comparison square on the lifted base and local maps. -/
-- TODO: descend the postcomposed comparison identities by `IsLimit.hom_ext` once the explicit
-- localized-base cone is available again.
lemma formalGlueingComponentsForget_lift_comparison_comm [Module.Flat R S]
    {J : Type _} [Category J] [Finite J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c))
    (i : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i))
          ((Prod.fst
              (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
              ).hom.restrictScalars R)))
      (s.pt.comparisonIso i).hom
      (c.pt.comparisonIso i).hom
      (ModuleCat.ofHom
        ((LinearMap.extendScalarsOfIsLocalizationEquiv
          (Submonoid.powers (f i)) (Localization.Away (f i)))
          (TensorProduct.map
            ((Prod.snd
                (hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s))
                i).hom.restrictScalars R)
            (LinearMap.id : S →ₗ[R] S)))) := sorry

/-- Helper for Lemma 15.90.13: to apply faithful reflection, it remains to package the component
lift into a genuine morphism of formal glueing data. -/
-- TODO: assemble the component lift into a `FormalGlueingDatum.Hom` after the raw overlap and
-- comparison squares are restored.
lemma formalGlueingComponentsForget_lift_hom [Module.Flat R S]
    {J : Type _} [Category J] [Finite J] {K : J ⥤ Glue S f} {c s : Cone K}
    (hc : IsLimit ((formalGlueingComponentsForget (S := S) (f := f)).mapCone c)) :
    ∃ φ : s.pt ⟶ c.pt,
      (formalGlueingComponentsForget (S := S) (f := f)).map φ =
        hc.lift ((formalGlueingComponentsForget (S := S) (f := f)).mapCone s) := sorry

/-- Helper for Lemma 15.90.13: the component forgetful functor reflects finite limits because a
limiting cone on the base and all local pieces admits a unique lift whose comparison squares are
checked after applying the localized-base and tensorized-local comparison functors. -/
-- TODO: finish the faithful-reflection argument once the component lift has been restored.
lemma formalGlueingComponentsForget_reflects_finite_limits [Module.Flat R S] :
    ReflectsFiniteLimits (formalGlueingComponentsForget (S := S) (f := f)) := sorry

/-- Helper for Lemma 15.90.13: the remaining exactness input is finite-limit preservation of the
canonical formal glueing functor. -/
-- TODO: combine the repaired componentwise preservation and reflection lemmas.
lemma formalGlueingCan_preserves_finite_limits [Module.Flat R S] :
    PreservesFiniteLimits (formalGlueingCan S f) := sorry

/-- Lemma 15.90.13 (2): if `R → S` is flat, then the canonical formal glueing functor `Can` is
exact. -/
-- TODO: once `formalGlueingCan_preserves_finite_limits` is restored, close exactness via
-- `exactFunctor_iff`.
theorem formalGlueingCan_exact [Module.Flat R S] :
    exactFunctor (ModuleCat.{max u w} R) (Glue S f) (formalGlueingCan S f) := sorry

/-- Lemma 15.90.13 (3): the canonical formal glueing functor preserves all colimits because it is
a left adjoint by Lemma `15.90.11`. -/
@[stacks 05EN]
noncomputable instance formalGlueingCan_preservesColimits :
    PreservesColimits (formalGlueingCan S f) :=
  inferInstance

end
