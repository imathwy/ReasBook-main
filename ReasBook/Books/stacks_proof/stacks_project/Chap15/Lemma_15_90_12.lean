import Mathlib
import StacksProject_2024.Chap15.«15_90_8_1»
import StacksProject_2024.Chap15.Remark_15_90_10
import StacksProject_2024.Chap15.Lemma_15_90_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

local notation "Away" => LocalizedModule.Away

/-
Domain-style sampling:
- primary domain: formal glueing for module categories, with the degree-zero module recovered from
  the canonical formal glueing short complex;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0`,
  `formalGlueingModuleComplex`,
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- best owner abstraction:
  the source-facing functors `formalGlueingCan` and `formalGlueingH0`, bridged through the owner
  kernel object `LinearMap.ker (formalGlueingModuleComplexBeta S f M)` attached to the formal
  glueing complex;
- primitive data:
  the module `M`, the canonical map `formalGlueingModuleComplexAlpha S f M`, and the kernel-level
  comparison between `H⁰(Can(M))` and `ker β`;
- derived API:
  the componentwise linear equivalence and the resulting natural isomorphism
  `formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`.

Source/core/bridge triage:
- `source-facing`: the natural isomorphism below;
- `core/canonical`: `formalGlueingCan`, `formalGlueingH0`, and
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- `bridge/view`: the kernel-level comparison between `H⁰(Can(M))` and
  `LinearMap.ker (formalGlueingModuleComplexBeta S f M)`.
-/

/-- Helper for Lemma 15.90.12: the image of the first map `α` in the formal glueing complex lands
in `ker β`. -/
private theorem formalGlueingAlpha_mem_kerBeta
    (M : ModuleCat R) (x : M) :
    formalGlueingModuleComplexAlpha S f M x ∈
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) := by
  change formalGlueingModuleComplexBeta S f M (formalGlueingModuleComplexAlpha S f M x) = 0
  simpa using LinearMap.congr_fun (formalGlueingModuleComplex_comp_eq_zero S f M) x

private noncomputable def formalGlueingAlphaToKerBeta
    (M : ModuleCat R) :
    M →ₗ[R] LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  (formalGlueingModuleComplexAlpha S f M).codRestrict _ (formalGlueingAlpha_mem_kerBeta (S := S) (f := f) M)

/-- Helper for Lemma 15.90.12: a module morphism acts on the source of the explicit `β`-map by
mapping the tensor component and each localization component. -/
private noncomputable def formalGlueingBetaSourceMap
    {M N : ModuleCat R} (φ : M ⟶ N) :
    (S ⊗[R] M) × ((i : Fin t) → Away (f i) M) →ₗ[R]
      (S ⊗[R] N) × ((i : Fin t) → Away (f i) N) :=
  LinearMap.prodMap
    (TensorProduct.map (LinearMap.id : S →ₗ[R] S) φ.hom)
    (LinearMap.pi fun i ↦
      ((LocalizedModule.map (Submonoid.powers (f i)) φ.hom).restrictScalars R).comp
        (LinearMap.proj i))

/-- Helper for Lemma 15.90.12: before passing to kernels, the source of the explicit glueing
complex is functorial in module morphisms. -/
private theorem formalGlueingBetaSourceMap_comp_alpha
    {M N : ModuleCat R} (φ : M ⟶ N) :
    formalGlueingBetaSourceMap (S := S) (f := f) φ ∘ₗ
        formalGlueingModuleComplexAlpha S f M =
      formalGlueingModuleComplexAlpha S f N ∘ₗ φ.hom := by
  -- Before passing to kernels, the source complex is already functorial: both sides send `x` to
  -- `(1 ⊗ φ(x), i ↦ φ(x)/1)`.
  ext x <;>
    simp [formalGlueingBetaSourceMap, formalGlueingModuleComplexAlpha, awayLocalizationFamilyMap]

/-- Helper for Lemma 15.90.12: the base component of `Can(M)` is extension of scalars to `S`. -/
private theorem formalGlueingCan_obj_base
    (M : ModuleCat R) :
    ((formalGlueingCan S f).obj M).base =
      (ModuleCat.extendScalars (algebraMap R S)).obj M := by
  rfl

/-- Helper for Lemma 15.90.12: the `i`-th local component of `Can(M)` is the away localization of
`M` at `f i`. -/
private theorem formalGlueingCan_obj_localModule
    (M : ModuleCat R) (i : Fin t) :
    ((formalGlueingCan S f).obj M).glue.localModule i =
      ModuleCat.of (Localization.Away (f i)) (Away (f i) M) := by
  rfl

/-- Helper for Lemma 15.90.12: transporting a tensor element to the base of `Can(M)` and back is
the identity. -/
private theorem formalGlueingCanBaseIso_hom_inv_apply
    (M : ModuleCat R) (x : S ⊗[R] M) :
    (formalGlueingCanBaseIso M).hom.hom ((formalGlueingCanBaseIso M).inv.hom x) = x := by
  -- This is the `hom ≫ inv = 𝟙` triangle identity evaluated on the tensor element.
  simpa using Iso.hom_inv_id_apply (formalGlueingCanBaseIso M) x

/-- Helper for Lemma 15.90.12: transporting a base element of `Can(M)` to the tensor model and
back is the identity. -/
private theorem formalGlueingCanBaseIso_inv_hom_apply
    (M : ModuleCat R) (x : ((formalGlueingCan S f).obj M).base) :
    (formalGlueingCanBaseIso M).inv.hom ((formalGlueingCanBaseIso M).hom.hom x) = x := by
  -- This is the `inv ≫ hom = 𝟙` triangle identity evaluated on the canonical base owner.
  simpa using Iso.inv_hom_id_apply (formalGlueingCanBaseIso M) x

/-- Helper for Lemma 15.90.12: reindexing an away localization along an equality preserves the
denominator-`1` generator. -/
private theorem formalGlueingCan_awayEqLinearEquiv_apply_mk_one
    (M : Type _) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    awayEqLinearEquiv M h (LocalizedModule.mk m 1 : Away a M) =
      (LocalizedModule.mk m 1 : Away b M) := by
  -- The reindexing equivalence is definitional after replacing the equal denominator.
  cases h
  rfl

/-- Helper for Lemma 15.90.12: the iterated-localization equivalence sends a denominator-`1`
generator to the corresponding denominator-`1` generator in the direct localization. -/
private theorem formalGlueingCan_iteratedLocalizedIso_apply_mk_one
    (a b : R) (M : Type _) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] (m : M) :
    iteratedLocalizedIso a b M (LocalizedModule.mk m 1 : Away b M) =
      (LocalizedModule.mk m 1 : Away (a * b) M) := by
  -- Compare the iterated and direct localizations on the image of the original numerator.
  change
    awayMulLinearEquiv a b M
      ((LocalizedModule.map (Submonoid.powers b) ((alreadyLocalizedLinearEquiv a M).symm.toLinearMap))
        (LocalizedModule.mk m 1 : Away b M)) =
      (LocalizedModule.mk m 1 : Away (a * b) M)
  rw [LocalizedModule.map_mk]
  have hmk :
      (alreadyLocalizedLinearEquiv a M).symm m =
        (LocalizedModule.mk m 1 : Away a M) := by
    -- The inverse localized equivalence is characterized by the denominator-`1` generator.
    apply (alreadyLocalizedLinearEquiv a M).injective
    simpa using
      (IsLocalizedModule.linearEquiv_apply (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LinearMap.id : M →ₗ[R] M) m).symm
  simpa [hmk] using
    (IsLocalizedModule.linearEquiv_apply
      (Submonoid.powers b ⊔ Submonoid.powers a)
      (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
      m)

/-- Helper for Lemma 15.90.12: the inverse direct-localization equivalence sends the direct
denominator-`1` generator back to the iterated one. -/
private theorem formalGlueingCan_awayMulLinearEquiv_symm_apply_mk_one
    (a b : R) (M : Type _) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M).symm
        (LocalizedModule.mk m 1 : Away (a * b) M) =
      (LocalizedModule.mk (LocalizedModule.mk m 1) 1 :
        LocalizedModule.Away b (LocalizedModule.Away a M)) := by
  -- Apply the forward equivalence and use the standard generator formula there.
  apply (awayMulLinearEquiv a b M).injective
  simpa using
    (IsLocalizedModule.linearEquiv_apply
      (Submonoid.powers b ⊔ Submonoid.powers a)
      (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
      m).symm

/-- Helper for Lemma 15.90.12: the left direct-localization transport sends the iterated
denominator-`1` generator to the direct denominator-`1` generator. -/
private theorem formalGlueingCan_leftToDirect_apply_mk_one
    (M : ModuleCat R) (i j : Fin t) (m : M) :
    (((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f i) (f j) M)
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- First undo the iterated-localization wrapper, then compute in the direct localization.
  rw [LinearEquiv.trans_apply]
  calc
    (awayMulLinearEquiv (f i) (f j) M)
        ((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm
          (LocalizedModule.mk
            (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
            LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M))) =
      (awayMulLinearEquiv (f i) (f j) M)
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f j) (LocalizedModule.Away (f i) M)) := by
        congr 1
        apply (iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).injective
        rw [LinearEquiv.apply_symm_apply]
        simpa using
          (formalGlueingCan_iteratedLocalizedIso_apply_mk_one
            (a := f i) (b := f j) (M := LocalizedModule.Away (f i) M)
            (m := (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M))).symm
    _ = (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
        simpa using
          (IsLocalizedModule.linearEquiv_apply
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f i))
            (iteratedLocalizedModuleMkLinearMap
              (Submonoid.powers (f j)) (Submonoid.powers (f i)) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
            m)

/-- Helper for Lemma 15.90.12: the right direct-localization transport sends the iterated
denominator-`1` generator to the direct denominator-`1` generator. -/
private theorem formalGlueingCan_rightToDirect_apply_mk_one
    (M : ModuleCat R) (i j : Fin t) (m : M) :
    ((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
        (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
      awayEqLinearEquiv M (mul_comm (f j) (f i)))
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- Route correction: rewrite to the swapped-product owner, compute there with the already proved
  -- left-hand transport, and then transport back to `f i * f j`.
  calc
    (awayEqLinearEquiv M (mul_comm (f j) (f i)))
        (((iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
            awayMulLinearEquiv (f j) (f i) M)
          ((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j)))
            (LocalizedModule.mk
              (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
              LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)))) =
      (awayEqLinearEquiv M (mul_comm (f j) (f i)))
        (((iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
            awayMulLinearEquiv (f j) (f i) M)
          (LocalizedModule.mk
            (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
            LocalizedModule.Away (f j * f i) (LocalizedModule.Away (f j) M))) := by
        rw [formalGlueingCan_awayEqLinearEquiv_apply_mk_one
          (M := LocalizedModule.Away (f j) M) (h := mul_comm (f i) (f j))
          (m := (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M))]
    _ = (awayEqLinearEquiv M (mul_comm (f j) (f i)))
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f j * f i) M) := by
        congr 1
        simpa using
          (formalGlueingCan_leftToDirect_apply_mk_one (f := f) (M := M) (i := j) (j := i) (m := m))
    _ = (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
        simpa using
          (formalGlueingCan_awayEqLinearEquiv_apply_mk_one
            (M := M) (h := mul_comm (f j) (f i)) (m := m))

/-- Helper for Lemma 15.90.12: localizing the identity equivalence acts trivially on away
modules. -/
private theorem formalGlueingCan_awayLocalizeLinearEquiv_refl
    (a : R) (M : Type _) [AddCommGroup M] [Module R M] :
    awayLocalizeLinearEquiv a (LinearEquiv.refl R M) = LinearEquiv.refl R (LocalizedModule.Away a M) := by
  -- The localized identity equivalence is determined by its values on localization generators.
  ext x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      simp [awayLocalizeLinearEquiv]

/-- Helper for Lemma 15.90.12: localizing the identity equivalence fixes the denominator-`1`
generator. -/
private theorem formalGlueingCan_awayLocalizeLinearEquiv_refl_apply_mk_one
    (a : R) (M : Type _) [AddCommGroup M] [Module R M] (m : M) :
    awayLocalizeLinearEquiv a (LinearEquiv.refl R M)
        (LocalizedModule.mk m 1 : LocalizedModule.Away a M) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away a M) := by
  -- Specialize the identity-localization equivalence to the standard generator.
  simpa [formalGlueingCan_awayLocalizeLinearEquiv_refl]

/-- Helper for Lemma 15.90.12: the explicit three-factor overlap transport used by the canonical
glueing object. -/
private noncomputable abbrev formalGlueingCan_explicit_overlapLinearEquiv
    (M : ModuleCat R) (i j : Fin t) :
    LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M) ≃ₗ[Localization.Away (f i * f j)]
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) :=
  (((awayLocalizeLinearEquiv (f i * f j)
        (LinearEquiv.refl R (LocalizedModule.Away (f i) M))).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j))) ≪≫ₗ
      ((((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm ≪≫ₗ
            awayMulLinearEquiv (f i) (f j) M) ≪≫ₗ
          (((awayEqLinearEquiv (LocalizedModule.Away (f j) M)
                (mul_comm (f i) (f j))) ≪≫ₗ
              (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
              awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
            awayEqLinearEquiv M (mul_comm (f j) (f i))).symm).extendScalarsOfIsLocalization
          (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))) ≪≫ₗ
    (((awayLocalizeLinearEquiv (f i * f j)
          (LinearEquiv.refl R (LocalizedModule.Away (f j) M))).extendScalarsOfIsLocalization
          (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j))).symm)

/-- Helper for Lemma 15.90.12: the inverse of the right direct-localization transport sends the
direct denominator-`1` generator back to the iterated one. -/
private theorem formalGlueingCan_expanded_right_transport_symm_apply_mk_one
    (M : ModuleCat R) (i j : Fin t) (m : M) :
    (((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i))).symm).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) =
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
          LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)) := by
  -- Apply the forward transport to both sides, so the goal reduces to the direct generator
  -- formula just proved for the right-hand transport.
  let e :
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[R]
        LocalizedModule.Away (f i * f j) M :=
    (((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i)))
  apply (LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)) e).injective
  -- Both extended equivalences act by the underlying transport on the canonical denominator-`1`
  -- generator, so the computation is exactly `formalGlueingCan_rightToDirect_apply_mk_one`.
  rw [LinearEquiv.extendScalarsOfIsLocalization_apply, LinearEquiv.extendScalarsOfIsLocalization_apply]
  rw [LinearEquiv.apply_symm_apply]
  simpa [e] using
    (formalGlueingCan_rightToDirect_apply_mk_one (f := f) (M := M) (i := i) (j := j) (m := m)).symm

/-- Helper for Lemma 15.90.12: the explicit overlap transport sends the standard generator on the
`i`-side to the standard generator on the `j`-side. -/
private theorem formalGlueingCan_explicit_overlapLinearEquiv_mk_one
    (M : ModuleCat R) (i j : Fin t) (m : M) :
    formalGlueingCan_explicit_overlapLinearEquiv (f := f) M i j
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 :
            LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M)) =
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 :
          LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)) := by
  -- Route correction: strip the identity-localization wrappers first, then evaluate the two
  -- direct-localization transports in the middle on the denominator-`1` generator.
  let rightWrapper :
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[Localization.Away (f i * f j)]
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) :=
    (awayLocalizeLinearEquiv (f i * f j)
      (LinearEquiv.refl R (LocalizedModule.Away (f j) M))).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j))
  apply rightWrapper.injective
  -- After cancelling the outer identity wrappers, only the explicit middle transport remains.
  simp only [formalGlueingCan_explicit_overlapLinearEquiv, rightWrapper, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.extendScalarsOfIsLocalization_apply]
  rw [formalGlueingCan_awayLocalizeLinearEquiv_refl_apply_mk_one]
  have hleft := formalGlueingCan_leftToDirect_apply_mk_one (f := f) (M := M) (i := i) (j := j)
    (m := m)
  simp only [LinearEquiv.trans_apply] at hleft
  rw [hleft]
  have hright := formalGlueingCan_expanded_right_transport_symm_apply_mk_one
    (f := f) (M := M) (i := i) (j := j) (m := m)
  simp only [LinearEquiv.extendScalarsOfIsLocalization_apply] at hright
  rw [hright]
  simpa using
    (formalGlueingCan_awayLocalizeLinearEquiv_refl_apply_mk_one
    (a := f i * f j) (M := LocalizedModule.Away (f j) M)
    (m := (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M))).symm

/-- Helper for Lemma 15.90.12: the tensor-side codomain transport used to compare the explicit
`β`-complex with the public `H⁰` compatibility map for `Can(M)`. -/
private noncomputable abbrev formalGlueingCan_tensorComponentLinearEquiv
    (M : ModuleCat R) (i : Fin t) :
    LocalizedModule.Away (f i) (S ⊗[R] M) ≃ₗ[R]
      ((((formalGlueingCan S f).obj M).glue.localModule i) ⊗[R] S) :=
  (awayLocalizeLinearEquiv (f i)
      ((formalGlueingCanBaseIso M).symm.toLinearEquiv.restrictScalars R)).trans
    ((((formalGlueingCan S f).obj M).comparisonIso i).toLinearEquiv.restrictScalars R)

/-- Helper for Lemma 15.90.12: the forward base transport of `Can(M)` preserves addition. -/
private theorem formalGlueingCanBaseIso_hom_map_add
    (M : ModuleCat R) (x y : ((formalGlueingCan S f).obj M).base) :
    (formalGlueingCanBaseIso M).hom.hom (x + y) =
      (formalGlueingCanBaseIso M).hom.hom x + (formalGlueingCanBaseIso M).hom.hom y := by
  -- The forward comparison is a linear map, so addition is preserved on the base term.
  simpa using (formalGlueingCanBaseIso M).hom.hom.map_add x y

/-- Helper for Lemma 15.90.12: the explicit tensor branch of `β`, restricted to pairs whose
localization family already satisfies the overlap compatibility equations. -/
private noncomputable abbrev formalGlueingIteratedKernelTensorMap
    (M : ModuleCat R) :
    (S ⊗[R] M) × LinearMap.ker (awayLocalizationCompatibilityMap M f) →ₗ[R]
      ((i : Fin t) → Away (f i) (S ⊗[R] M)) :=
  (LinearMap.fst R
      ((i : Fin t) → Away (f i) (S ⊗[R] M))
      ((ij : Fin t × Fin t) → Away (f ij.1 * f ij.2) M)).comp <|
    (formalGlueingModuleComplexBeta S f M).comp <|
      LinearMap.prodMap
        (LinearMap.id : S ⊗[R] M →ₗ[R] S ⊗[R] M)
        ((LinearMap.ker (awayLocalizationCompatibilityMap M f)).subtype)

/-- Helper for Lemma 15.90.12: the canonical direct-localization transport on the `i`-side of the
public overlap owner for `Can(M)`. -/
private noncomputable abbrev formalGlueingCan_leftToDirect
    (M : ModuleCat R) (i j : Fin t) :
    LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M) ≃ₗ[R]
      LocalizedModule.Away (f i * f j) M :=
  (iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm ≪≫ₗ
    awayMulLinearEquiv (f i) (f j) M

/-- Helper for Lemma 15.90.12: the canonical direct-localization transport on the `j`-side of the
public overlap owner for `Can(M)`. -/
private noncomputable abbrev formalGlueingCan_rightToDirect
    (M : ModuleCat R) (i j : Fin t) :
    LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[R]
      LocalizedModule.Away (f i * f j) M :=
  (((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
      (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
      awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
    awayEqLinearEquiv M (mul_comm (f j) (f i)))

/-- Helper for Lemma 15.90.12: the public glued module of `Can(M)` is exactly the explicit overlap
kernel of `awayLocalizationCompatibilityMap`. -/
private noncomputable def formalGlueingCan_gluedModuleLinearEquiv_overlapKer
    (M : ModuleCat R) :
    ((formalGlueingCan S f).obj M).glue.gluedModule ≃ₗ[R]
      LinearMap.ker (awayLocalizationCompatibilityMap M f) := sorry

/-- Helper for Lemma 15.90.12: the kernel of the explicit tensor branch on the overlap kernel is
the same as the kernel of the full map `β`. -/
private noncomputable def formalGlueingKerBeta_iteratedKernelLinearEquiv
    (M : ModuleCat R) :
    LinearMap.ker (formalGlueingIteratedKernelTensorMap (S := S) (f := f) M) ≃ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) where
  toFun x :=
    ⟨(x.1.1, x.1.2.1), by
      -- The iterated-kernel input already satisfies the overlap equations, and its tensor branch
      -- vanishes by the outer kernel condition.
      apply (LinearMap.mem_ker).2
      apply Prod.ext
      · change formalGlueingIteratedKernelTensorMap (S := S) (f := f) M (x.1.1, x.1.2) = 0
        exact x.2
      · ext ij
        have hxOverlap :
            awayLocalizationCompatibilityMap M f x.1.2.1 = 0 :=
          (LinearMap.mem_ker).1 x.1.2.2
        exact congrArg (fun g ↦ g ij.1 ij.2) hxOverlap⟩
  invFun x :=
    ⟨(x.1.1, ⟨x.1.2, by
        -- The overlap branch of `β x = 0` is exactly the explicit compatibility condition.
        have hxBeta : formalGlueingModuleComplexBeta S f M (x.1.1, x.1.2) = 0 :=
          (LinearMap.mem_ker).1 x.2
        have hxBetaSnd :
            (formalGlueingModuleComplexBeta S f M (x.1.1, x.1.2)).2 = 0 :=
          congrArg Prod.snd hxBeta
        apply (LinearMap.mem_ker).2
        ext i j
        exact congrArg (fun g ↦ g (i, j)) hxBetaSnd⟩), by
      -- After recording the overlap equations in the second factor, the remaining kernel
      -- condition is precisely the tensor branch of `β x = 0`.
      have hxBeta : formalGlueingModuleComplexBeta S f M (x.1.1, x.1.2) = 0 :=
        (LinearMap.mem_ker).1 x.2
      change (formalGlueingModuleComplexBeta S f M (x.1.1, x.1.2)).1 = 0
      exact congrArg Prod.fst hxBeta⟩
  left_inv x := by
    -- Both transports keep the ambient tensor element and localization family unchanged.
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i
      rfl
  right_inv x := by
    -- The inverse just repackages the overlap equation into the inner kernel subtype.
    apply Subtype.ext
    apply Prod.ext <;> rfl
  map_add' x y := by
    -- The equivalence acts by the identity on the ambient pair data.
    apply Subtype.ext
    ext <;> rfl
  map_smul' r x := by
    -- Scalar multiplication is preserved componentwise on the same ambient pair data.
    apply Subtype.ext
    ext <;> rfl

/-- Helper for Lemma 15.90.12: after transporting the `i`-th public `H⁰` compatibility component
for `Can(M)` back through the canonical tensor comparison, one recovers exactly the `i`-th tensor
component of the explicit `β`-map on the iterated-kernel owner. -/
private theorem formalGlueingCan_h0Compatibility_component_via_betaTensor
    (M : ModuleCat R)
    (xBase : ((formalGlueingCan S f).obj M).base)
    (g : ((formalGlueingCan S f).obj M).glue.gluedModule)
    (i : Fin t) :
    (formalGlueingCan_tensorComponentLinearEquiv (S := S) (f := f) M i).symm
        (FormalGlueingDatum.h0CompatibilityMap ((formalGlueingCan S f).obj M) (xBase, g) i) =
      formalGlueingIteratedKernelTensorMap (S := S) (f := f) M
        ((formalGlueingCanBaseIso M).hom.hom xBase,
          formalGlueingCan_gluedModuleLinearEquiv_overlapKer (S := S) (f := f) M g) i := by
  -- TODO: transport the public `H⁰` compatibility component through the canonical tensor and
  -- overlap-kernel identifications for `Can(M)`.
  sorry

-- TODO: transport the public `H⁰(Can(M))` owner to the explicit iterated-kernel model by
-- rewriting the public glued-module and `h0CompatibilityMap` equations componentwise through the
-- canonical `Can(M)` overlap and comparison isomorphisms.
private noncomputable def formalGlueingCanH0LinearEquiv_iteratedKernel
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) ≃ₗ[R]
      LinearMap.ker (formalGlueingIteratedKernelTensorMap (S := S) (f := f) M) := sorry

private noncomputable def formalGlueingH0KerBetaLinearEquiv
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) ≃ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  (formalGlueingCanH0LinearEquiv_iteratedKernel (S := S) (f := f) M).trans
    (formalGlueingKerBeta_iteratedKernelLinearEquiv (S := S) (f := f) M)

private noncomputable def formalGlueingH0ToKerBeta
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) →ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  (formalGlueingH0KerBetaLinearEquiv (S := S) (f := f) M).toLinearMap

private noncomputable def formalGlueingKerBetaToH0
    (M : ModuleCat R) :
    LinearMap.ker (formalGlueingModuleComplexBeta S f M) →ₗ[R]
      ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) :=
  (formalGlueingH0KerBetaLinearEquiv (S := S) (f := f) M).symm.toLinearMap

/-- Helper for Lemma 15.90.12: the target of `β` carries the componentwise action induced by a
module morphism. -/
private noncomputable def formalGlueingCanH0LinearEquiv_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat R) :
    M ≃ₗ[R] ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) := sorry

-- Proof sketch: identify `H⁰(Can(M))` with the kernel of the second map `β` in the formal
-- glueing module complex. Lemma `15.90.9` gives `range(α) = ker(β)` and injectivity of `α`, so
-- the canonical map `M → ker(β)` is a linear equivalence. Transport this through the kernel-level
-- bridge to obtain the desired componentwise isomorphism.
-- Lemma `15.90.9` identifies the unit map `M ⟶ H^0(Can(M))` with the first map in the formal
-- glueing complex and proves that it is an isomorphism under the flatness and quotient
-- hypotheses, yielding a natural isomorphism `Can ⋙ H^0 ≅ 𝟭`.
/-- Lemma 15.90.12: assume `φ : R → S` is a flat ring map and `I = (f₁, \ldots, fₜ) ⊂ R` is an
ideal such that `R/I → S/IS` is an isomorphism. Then the degree-zero functor `H^0` of Remark
15.90.10 is a left quasi-inverse to the canonical functor `Can`. In the formalization, the
right-adjoint owner is already the canonical functor `formalGlueingH0 R S f` from Remark
`15.90.10`, so the content here is the natural isomorphism
`formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`. -/
@[stacks 05EM]
noncomputable def formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭 (ModuleCat R) := by
  -- TODO: complete the naturality square by comparing both sides after postcomposing with the
  -- explicit kernel model `formalGlueingH0ToKerBeta`.
  sorry

end
