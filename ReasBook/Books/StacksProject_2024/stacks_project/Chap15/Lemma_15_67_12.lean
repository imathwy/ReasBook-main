import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_71_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ} {d : ℕ}

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)

/-- Helper for Lemma 15.67.12: the stable degree-zero embedding of `A`-modules into `D(A)`. -/
private abbrev single₀A : ModuleCat A ⥤ DModA :=
  DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- Helper for Lemma 15.67.12: the stable degree-zero embedding of `B`-modules into `D(B)`. -/
private abbrev single₀B : ModuleCat B ⥤ DModB :=
  DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)

/-- Helper for Lemma 15.67.12: exact restriction of scalars on derived categories. -/
private abbrev restrictDerived : DModB ⥤ DModA :=
  Functor.mapDerivedCategory (ModuleCat.restrictScalars (algebraMap A B))

/- Domain-style sampling for Lemma 15.67.12:
- primary domain: tor-amplitude in derived categories under restriction of scalars;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ModuleHasTorDimensionLE`,
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`,
  `ModuleCat.single0Functor`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement remains a tor-amplitude bound after
  restriction of scalars, while the canonical owner layer is `HasTorAmplitudeIn` together with the
  exact derived restriction functor itself; this file is the source-facing specialization of
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct` obtained by testing against the
  canonical degree-zero object `B[0]`, not a new local wrapper around restriction of scalars;
- primitive data: the derived `B`-complex `K` and the module-level tor-dimension hypothesis on
  `B` over `A`;
- derived API: the restricted derived object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.

Source/core/bridge triage:
- `source-facing`: `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- `core/canonical`: `HasTorAmplitudeIn`, `ModuleHasTorDimensionLE`, and exact
  `Functor.mapDerivedCategory` for restriction of scalars;
- `bridge/view`: the canonical degree-zero embedding `ModuleCat.single0Functor` for `B[0]`,
  together with viewing a derived `B`-complex as a derived `A`-complex by restriction. -/

/-- Helper for Lemma 15.67.12: the identity map preserves addition on the restricted regular
`B`-module viewed as an `A`-module. -/
private theorem restrictScalars_regular_refl_map_add
    (x y : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) :
    (Equiv.refl B).toFun (x + y) = (Equiv.refl B).toFun x + (Equiv.refl B).toFun y :=
  rfl

/-- Helper for Lemma 15.67.12: the identity map preserves the `A`-scalar action on the restricted
regular `B`-module. -/
private theorem restrictScalars_regular_refl_map_smul
    (a : A)
    (x : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) :
    (Equiv.refl B).toFun (a • x) = (RingHom.id A) a • (Equiv.refl B).toFun x := by
  simpa [Algebra.smul_def]

/-- Helper for Lemma 15.67.12: the identity equivalence on `B` is `A`-linear for the restricted
regular module structure. -/
private noncomputable def restrictScalars_regular_linearEquiv :
    (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) ≃ₗ[A]
      (ModuleCat.of A B : ModuleCat A) :=
  { toEquiv := Equiv.refl B
    map_add' := restrictScalars_regular_refl_map_add (B := B)
    map_smul' := restrictScalars_regular_refl_map_smul (A := A) (B := B) }

/-- Helper for Lemma 15.67.12: the restricted regular `B`-module is definitionally the ordinary
`A`-module on `B`. -/
private noncomputable def restrictScalars_regular_iso_eq :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≅ ModuleCat.of A B :=
  (restrictScalars_regular_linearEquiv (A := A) (B := B)).toModuleIso

/-- Helper for Lemma 15.67.12: restricting the regular `B`-module to `A` is the canonical
`A`-module structure on `B`. -/
noncomputable def restrictScalars_regular_iso :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≅ ModuleCat.of A B :=
  restrictScalars_regular_iso_eq (A := A) (B := B)

/-- Helper for Lemma 15.67.12: restricting the degree-zero regular `B`-module to `A` commutes with
the degree-zero embedding into the derived category. -/
noncomputable def restrictScalars_single0_regular_iso :
    ((restrictDerived (A := A) (B := B)).obj
      (single₀B.obj (ModuleCat.of B B))) ≅
      single₀A.obj ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  -- Proof comment: compute derived restriction on a single complex via the exact cochain-level
  -- restriction functor.
  ((restrictDerived (A := A) (B := B)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app
        (ModuleCat.of B B))) ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B)) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars (algebraMap A B))
          (0 : ℤ)).app (ModuleCat.of B B)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))).symm

/-- Helper for Lemma 15.67.12: extend a chain-level free resolution to the cochain model used by
the source proof. -/
private abbrev resolutionView
    (P : ChainComplex (ModuleCat A) ℕ) : CochainComplex (ModuleCat A) ℤ :=
  P.extend ComplexShape.embeddingDownNat

/-- Helper for Lemma 15.67.12: the extended free-resolution model still represents `M[0]` in the
derived category of `A`-modules. -/
private noncomputable def resolution_view_iso_single_zero
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    DerivedCategory.Q.obj (resolutionView (A := A) P) ≅ (single₀A.obj M) := by
  let f :
      DerivedCategory.Q.obj (resolutionView (A := A) P) ⟶
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ (ModuleCat A)).obj M).extend ComplexShape.embeddingDownNat) :=
    DerivedCategory.Q.map (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat)
  have hf : IsIso f := by
    -- Proof comment: extending the augmentation by zero preserves the free-resolution
    -- quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e :
      DerivedCategory.Q.obj (resolutionView (A := A) P) ≅
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ (ModuleCat A)).obj M).extend ComplexShape.embeddingDownNat) :=
    asIso f
  -- Proof comment: rewrite the extended single complex back to the canonical derived object
  -- `M[0]`.
  exact
    e ≪≫
      (DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl)) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).symm

/-- Helper for Lemma 15.67.12: restricting scalars commutes with homology on derived module
categories. -/
private noncomputable def restrictScalars_homology_iso
    (L : DModB) (i : ℤ) :
    (HA i).obj ((restrictDerived (A := A) (B := B)).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj ((HB i).obj L) :=
  -- TODO: compare derived homology before and after restriction of scalars by passing to
  -- `Q.objPreimage L`, then use `homologyFunctorFactors` and `mapHomologyIso`.
  sorry

/-- Helper for Lemma 15.67.12: after restricting scalars from `B` to `A`, tensoring a `B`-complex
with the scalar-extended resolution view agrees with tensoring the restricted complex with the
original resolution view over `A`. -/
private noncomputable def tensor_resolution_model_restrict_iso
    (L₀ : CochainComplex (ModuleCat B) ℤ)
    (P : ChainComplex (ModuleCat A) ℕ) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomologicalComplex.tensorObj L₀
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (resolutionView (A := A) P)))) ≅
      HomologicalComplex.tensorObj
        (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L₀)
        (resolutionView (A := A) P) := by
  -- Proof comment: this is exactly the earlier restriction/base-change comparison, specialized to
  -- the free-resolution view `resolutionView P`.
  simpa [resolutionView] using
    (restrictScalars_tensorObj_extendScalars_iso (R := A) (R' := B) (algebraMap A B) L₀
      (resolutionView (A := A) P))

/-- Helper for Lemma 15.67.12: the source proof computes the `A`-linear test tensor object from
one chosen free `A`-resolution of `M`. -/
private noncomputable def tensor_resolution_model_iso_over_base_test
    (K : DModB)
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    let L₀ := DerivedCategory.Q.objPreimage K
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    let N_M := HomologicalComplex.tensorObj L₀ PB
    ((restrictDerived (A := A) (B := B)).obj (DerivedCategory.Q.obj N_M)) ≅
      (((restrictDerived (A := A) (B := B)).obj K) ⊗[A]^L (single₀A.obj M)) :=
  -- TODO: localize the chain-level tensor model, compare it with restriction of scalars via
  -- `tensor_resolution_model_restrict_iso`, and then pass back to derived tensor products.
  sorry

/-- Helper for Lemma 15.67.12: the degree-zero copy of the regular `B`-module is the tensor unit in
`D(B)`. -/
noncomputable def regular_single0_tensorUnit_iso :
    single₀B.obj (ModuleCat.of B B) ≅ 𝟙_ DModB :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app (ModuleCat.of B B)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat B)).app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B))).symm

/-- Helper for Lemma 15.67.12: tensoring with the degree-zero regular `B`-module is canonically the
identity on `D(B)`. -/
noncomputable def tensor_regular_single0_iso (K : DModB) :
    K ⊗[B]^L (single₀B.obj (ModuleCat.of B B)) ≅ K :=
  -- Proof comment: compare derived tensor product with the monoidal tensor, then use the right
  -- unitor after identifying `B[0]` with the tensor unit.
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      K (single₀B.obj (ModuleCat.of B B))).symm ≪≫
    whiskerLeftIso K regular_single0_tensorUnit_iso ≪≫
      ρ_ K

/-- Helper for Lemma 15.67.12: the degree-zero regular `B`-module is also a left tensor unit in
`D(B)`. -/
private noncomputable def regular_single0_left_tensor_iso (K : DModB) :
    (single₀B.obj (ModuleCat.of B B)) ⊗ K ≅ K :=
  whiskerRightIso regular_single0_tensorUnit_iso K ≪≫ λ_ K

/-- Helper for Lemma 15.67.12: the concrete tensor-resolution model for the regular object
`B[0]` collapses to the scalar-extended resolution itself. -/
private noncomputable def regular_tensor_resolution_iso
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    let L₀ := DerivedCategory.Q.objPreimage (single₀B.obj (ModuleCat.of B B))
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    let N_M := HomologicalComplex.tensorObj L₀ PB
    DerivedCategory.Q.obj N_M ≅ DerivedCategory.Q.obj PB :=
  -- TODO: identify the concrete tensor model with `B[0] ⊗ Q.obj PB` and collapse the left
  -- regular factor using `regular_single0_left_tensor_iso`.
  sorry

/-- Helper for Lemma 15.67.12: the `A`-linear test homology of `restrict(B[0])` against `M` is the
restriction of the homology of the scalar-extended free-resolution model. -/
private noncomputable def restrictScalars_regular_test_homology_iso
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π]
    (q : ℤ) :
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    (HA q).obj ((((restrictDerived (A := A) (B := B)).obj
        (single₀B.obj (ModuleCat.of B B))) ⊗[A]^L (single₀A.obj M))) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj (PB.homology q) :=
  -- TODO: compose `tensor_resolution_model_iso_over_base_test`,
  -- `restrictScalars_homology_iso`, and `regular_tensor_resolution_iso`.
  sorry

/-- Helper for Lemma 15.67.12: the tor-amplitude hypothesis on `restrict(B[0])` forces the
scalar-extended free-resolution model of `M ⊗_A^{\mathbf L} B` to have homology only in
degrees `[-d, 0]`. -/
private theorem extendScalars_resolution_homology_isZero_of_hB0
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π]
    (hB0 :
      HasTorAmplitudeIn
        ((restrictDerived (A := A) (B := B)).obj
          (single₀B.obj (ModuleCat.of B B)))
        (-(d : ℤ)) 0)
    (q : ℤ)
    (hq : q ∉ Set.Icc (-(d : ℤ)) 0) :
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    IsZero (PB.homology q) := by
  -- TODO: transport `hB0 M q hq` across `restrictScalars_regular_test_homology_iso` and then
  -- reflect zero objects through `isZero_of_restrictScalars_obj`.
  sorry

/-- Helper for Lemma 15.67.12: after restricting scalars to `A`, the right-unit comparison for
tensoring with `B[0]` still identifies the tensor object with the restricted complex. -/
noncomputable def restrictScalars_tensor_regular_single0_iso (K : DModB) :
    ((restrictDerived (A := A) (B := B)).obj
      (K ⊗[B]^L (single₀B.obj (ModuleCat.of B B)))) ≅
      ((restrictDerived (A := A) (B := B)).obj K) :=
  -- Proof comment: apply the exact derived restriction functor to the right-unit isomorphism.
  ((restrictDerived (A := A) (B := B)).mapIso
    (tensor_regular_single0_iso K))

/-- Helper for Lemma 15.67.12: tor-amplitude in a fixed interval is invariant under isomorphism in
`D(A)`. -/
private theorem hasTorAmplitudeIn_of_iso
    {K L : DModA} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Proof comment: transport the tested homology object along the tensor image of `e`.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
          ((derivedTensorProduct (single₀A.obj M)).mapIso e.symm))
  · intro h M i hi
    -- Proof comment: the reverse implication uses the inverse tensor transport.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
          ((derivedTensorProduct (single₀A.obj M)).mapIso e))

/-- Helper for Lemma 15.67.12: a tor-amplitude bound on `K` is witnessed by a bounded
termwise-flat cochain representative. -/
private theorem exists_flat_representative_of_hasTorAmplitudeIn
    (K : DModB)
    (hK : HasTorAmplitudeIn K a b) :
    ∃ (E : CochainComplex (ModuleCat B) ℤ) (_ : K ≅ DerivedCategory.Q.obj E),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ E.IsTermwiseFlat := by
  -- Route correction: the intended source-faithful witness is Lemma `15.67.3`, but importing that
  -- file rebuilds the broken upstream dependency `Lemma_15_67_2` in this workspace. Once that
  -- dependency is repaired, replace this placeholder with the direct call to
  -- `hasTorAmplitudeIn_iff_exists_flat_representative`.
  sorry

/-- Helper for Lemma 15.67.12: specializing the change-of-rings tensor estimate to the regular
module `B[0]` reduces the target theorem to the canonical right-unit isomorphism. -/
private theorem hasTorAmplitudeIn_restrictScalars_tensor_regular_single0
    (K : DModB)
    (hK : HasTorAmplitudeIn K a b)
    (hB0 :
      HasTorAmplitudeIn
        ((restrictDerived (A := A) (B := B)).obj
          (single₀B.obj (ModuleCat.of B B)))
        (-(d : ℤ)) 0) :
    HasTorAmplitudeIn
      ((restrictDerived (A := A) (B := B)).obj
        (K ⊗[B]^L (single₀B.obj (ModuleCat.of B B))))
      (a - (d : ℤ)) b := by
  -- TODO: finish the `B[0]` specialization of the proof of Lemma `15.67.10` by combining the
  -- free-resolution transport on `M ⊗_A^L B`, a bounded flat representative of `K`, and the
  -- first spectral sequence of the resulting tensor bicomplex.
  sorry

/-- Lemma 15.67.12: if `B` has tor dimension at most `d` as an `A`-module and `K^•` has
tor-amplitude in `[a, b]` over `B`, then `K^•`, viewed as a complex of `A`-modules by
restriction of scalars, has tor-amplitude in `[a - d, b]`. -/
theorem hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE
    (K : DModB)
    (hB : ModuleHasTorDimensionLE (ModuleCat.of A B) d)
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((restrictDerived (A := A) (B := B)).obj K)
      (a - (d : ℤ)) b := by
  have hRegular :
      HasTorAmplitudeIn
        (single₀A.obj ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)))
        (-(d : ℤ)) 0 := by
    -- Proof comment: identify the restricted regular module with the canonical `A`-module `B`,
    -- then transport the module tor-dimension hypothesis across the induced degree-zero isomorphism.
    exact
      (hasTorAmplitudeIn_of_iso (A := A) ((single₀A).mapIso restrictScalars_regular_iso)).2 <| by
        simpa [ModuleHasTorDimensionLE] using hB
  have hRestrictedRegular :
      HasTorAmplitudeIn
        ((restrictDerived (A := A) (B := B)).obj
          (single₀B.obj (ModuleCat.of B B)))
        (-(d : ℤ)) 0 := by
    -- Proof comment: the previous helper aligns the restricted `B[0]` object with the canonical
    -- degree-zero `A`-object of the underlying `A`-module `B`.
    exact
      (hasTorAmplitudeIn_of_iso (A := A) restrictScalars_single0_regular_iso).2 hRegular
  have hTensor :
      HasTorAmplitudeIn
        ((restrictDerived (A := A) (B := B)).obj
          (K ⊗[B]^L (single₀B.obj (ModuleCat.of B B))))
        (a - (d : ℤ)) b := by
    -- Route correction: isolate the exact `B[0]` specialization locally so the target file no
    -- longer depends on the broken upstream import chain through Lemma `15.67.10`.
    exact
      hasTorAmplitudeIn_restrictScalars_tensor_regular_single0
        (A := A) (B := B) (a := a) (b := b) (d := d) K hK hRestrictedRegular
  -- Proof comment: transport the tor-amplitude bound across the restricted right-unit comparison
  -- to replace `K ⊗^L_B B[0]` by `K`.
  exact
    (hasTorAmplitudeIn_of_iso (A := A)
      (restrictScalars_tensor_regular_single0_iso (A := A) (B := B) K)).1 hTensor

end

end CategoryTheory
