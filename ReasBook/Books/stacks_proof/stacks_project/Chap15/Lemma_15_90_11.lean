import stacks_proof.stacks_project.Chap15.Remark_15_90_10
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/-- Helper for Lemma 15.90.11: the base component of the canonical glueing object is extension of
scalars to `S`. -/
private theorem formalGlueingCan_obj_base
    (M : ModuleCat.{max u w} R) :
    ((formalGlueingCan S f).obj M).base =
      (ModuleCat.extendScalars (algebraMap R S)).obj M := by
  rfl

/-- Helper for Lemma 15.90.11: the `i`-th local component of the canonical glueing object is the
localization of `M` away from `f i`. -/
private theorem formalGlueingCan_obj_localModule
    (M : ModuleCat.{max u w} R) (i : Fin t) :
    ((formalGlueingCan S f).obj M).glue.localModule i =
      ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M) := by
  rfl

/-- Helper for Lemma 15.90.11: every local component of a glueing datum is already localized away
from its indexing element. -/
private theorem formalGlueing_localModule_isLocalized_id
    (X : Glue S f) (i : Fin t) :
    IsLocalizedModule.Away (f i) (LinearMap.id : X.glue.localModule i →ₗ[R] X.glue.localModule i) := by
  -- The local component is a module over `R_{f_i}`, so the identity map exhibits it as already
  -- localized away from `f_i`.
  simpa using
    (isLocalizedModule_id (Submonoid.powers (f i)) (X.glue.localModule i)
      (Localization.Away (f i)))

/-- Helper for Lemma 15.90.11: reindexing an away-localization along an equality preserves the
denominator-`1` generator. -/
private theorem formalGlueingCan_awayEqLinearEquiv_apply_mk_one
    (M : Type w) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    awayEqLinearEquiv M h (LocalizedModule.mk m 1 : LocalizedModule.Away a M) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away b M) := by
  -- The equality only changes the indexing element of the localization, so on generators the map
  -- is definitionally the identity.
  cases h
  rfl

/-- Helper for Lemma 15.90.11: the iterated away-localization equivalence sends a denominator-`1`
generator to the corresponding denominator-`1` generator in the direct localization. -/
private theorem formalGlueingCan_iteratedLocalizedIso_apply_mk_one
    (a b : R) (M : Type w) [AddCommGroup M] [Module (Localization.Away a) M]
    [Module R M] [IsScalarTower R (Localization.Away a) M] (m : M) :
    iteratedLocalizedIso a b M (LocalizedModule.mk m 1 : LocalizedModule.Away b M) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M) := by
  -- First rewrite the numerator under the localization of the already-localized equivalence.
  change
    awayMulLinearEquiv a b M
      ((LocalizedModule.map (Submonoid.powers b) ((alreadyLocalizedLinearEquiv a M).symm.toLinearMap))
        (LocalizedModule.mk m 1 : LocalizedModule.Away b M)) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M)
  rw [LocalizedModule.map_mk]
  have hmk :
      (alreadyLocalizedLinearEquiv a M).symm m =
        (LocalizedModule.mk m 1 : LocalizedModule.Away a M) := by
    -- The inverse of the already-localized equivalence is characterized by the denominator-`1`
    -- generators sent back to `m`.
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

/-- Helper for Lemma 15.90.11: the inverse direct away-localization equivalence sends the
denominator-`1` direct generator to the corresponding iterated denominator-`1` generator. -/
private theorem formalGlueingCan_awayMulLinearEquiv_symm_apply_mk_one
    (a b : R) (M : Type w) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M).symm
        (LocalizedModule.mk m 1 : LocalizedModule.Away (a * b) M) =
      (LocalizedModule.mk (LocalizedModule.mk m 1) 1 :
        LocalizedModule.Away b (LocalizedModule.Away a M)) := by
  -- The forward direct-localization equivalence identifies the iterated denominator-`1`
  -- generator with the direct one, so its inverse sends the direct generator back to that input.
  apply (awayMulLinearEquiv a b M).injective
  simpa using
    (IsLocalizedModule.linearEquiv_apply
      (Submonoid.powers b ⊔ Submonoid.powers a)
      (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
      m).symm

/-- Helper for Lemma 15.90.11: the left transport from the iterated localization
`(M_{f_i})_{f_j}` to `M_{f_if_j}` sends the standard generator to the direct generator. -/
private theorem formalGlueingCan_leftToDirect_apply_mk_one
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((iteratedLocalizedIso (f i) (f j) (LocalizedModule.Away (f i) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f i) (f j) M)
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- Rewrite the right-hand side through the inverse direct-localization equivalence, then compute
  -- the iterated-localization transport on the standard generator.
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

/-- Helper for Lemma 15.90.11: the right transport from the iterated localization
`(M_{f_j})_{f_i}` to `M_{f_if_j}` sends the standard generator to the direct generator. -/
private theorem formalGlueingCan_rightToDirect_apply_mk_one
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    ((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
        (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
        awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
      awayEqLinearEquiv M (mul_comm (f j) (f i)))
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M))) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) := by
  -- Rewrite the overlap index to the swapped product, compute there, and then rewrite back.
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

/-- Helper for Lemma 15.90.11: localizing the identity equivalence introduces no extra transport
on away modules. -/
private theorem formalGlueingCan_awayLocalizeLinearEquiv_refl
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] :
    awayLocalizeLinearEquiv a (LinearEquiv.refl R M) = LinearEquiv.refl R (LocalizedModule.Away a M) := by
  -- The localized identity equivalence is determined by its values on localization generators.
  ext x
  induction x using LocalizedModule.induction_on with
  | _ y s =>
      simp [awayLocalizeLinearEquiv]

/-- Helper for Lemma 15.90.11: localizing the identity equivalence fixes the denominator-`1`
generator. -/
private theorem formalGlueingCan_awayLocalizeLinearEquiv_refl_apply_mk_one
    (a : R) (M : Type w) [AddCommGroup M] [Module R M] (m : M) :
    awayLocalizeLinearEquiv a (LinearEquiv.refl R M)
        (LocalizedModule.mk m 1 : LocalizedModule.Away a M) =
      (LocalizedModule.mk m 1 : LocalizedModule.Away a M) := by
  -- Specialize the identity-localization equivalence to the standard generator.
  simpa [formalGlueingCan_awayLocalizeLinearEquiv_refl]

/-- Helper for Lemma 15.90.11: the explicit three-factor overlap transport from Remark
`15.90.10` on the direct owner. -/
private noncomputable abbrev formalGlueingCan_explicit_overlapLinearEquiv
    (M : ModuleCat.{max u w} R) (i j : Fin t) :
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

/-- Helper for Lemma 15.90.11: the exact expanded inverse of the right direct-localization
transport sends the direct denominator-`1` generator back to the iterated generator. -/
private theorem formalGlueingCan_expanded_right_transport_symm_apply_mk_one
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i))).symm).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)))
      (LocalizedModule.mk m 1 : LocalizedModule.Away (f i * f j) M) =
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 : LocalizedModule.Away (f j) M) 1 :
          LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)) := by
  -- Apply the forward transport to both sides so the goal reduces to the already proved
  -- direct-localization generator formula.
  let e :
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[R]
        LocalizedModule.Away (f i * f j) M :=
    (((awayEqLinearEquiv (LocalizedModule.Away (f j) M) (mul_comm (f i) (f j))) ≪≫ₗ
          (iteratedLocalizedIso (f j) (f i) (LocalizedModule.Away (f j) M)).symm ≪≫ₗ
          awayMulLinearEquiv (f j) (f i) M) ≪≫ₗ
        awayEqLinearEquiv M (mul_comm (f j) (f i)))
  apply (LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j)) e).injective
  -- Both extended equivalences act by the underlying map on the canonical generators.
  rw [LinearEquiv.extendScalarsOfIsLocalization_apply, LinearEquiv.extendScalarsOfIsLocalization_apply]
  rw [LinearEquiv.apply_symm_apply]
  simpa [e] using
    (formalGlueingCan_rightToDirect_apply_mk_one (f := f) (M := M) (i := i) (j := j) (m := m)).symm

/-- Helper for Lemma 15.90.11: the explicit three-factor overlap transport sends the standard
generator on the `i`-side to the standard generator on the `j`-side. -/
private theorem formalGlueingCan_explicit_overlapLinearEquiv_mk_one
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    formalGlueingCan_explicit_overlapLinearEquiv (f := f) M i j
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 :
            LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f i) M)) =
      (LocalizedModule.mk
        (LocalizedModule.mk m 1 :
          LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M)) := by
  -- Strip the outer right wrapper by injectivity and then compute the three explicit factors in
  -- sequence on the denominator-`1` generator.
  let rightWrapper :
      LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) ≃ₗ[Localization.Away (f i * f j)]
        LocalizedModule.Away (f i * f j) (LocalizedModule.Away (f j) M) :=
    (awayLocalizeLinearEquiv (f i * f j)
      (LinearEquiv.refl R (LocalizedModule.Away (f j) M))).extendScalarsOfIsLocalization
        (Submonoid.powers (f i * f j)) (Localization.Away (f i * f j))
  apply rightWrapper.injective
  -- The left and right wrappers are localizations of the identity equivalence, so only the middle
  -- direct-localization transport contributes nontrivially.
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

/-- Helper for Lemma 15.90.11: after normalizing the public overlap wrapper at the
denominator-`1` generator, the canonical overlap map for `Can(M)` sends that generator to the
matching generator on the other side. -/
private theorem formalGlueingCan_overlapIso_owner_normalized
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((formalGlueingCan S f).obj M).glue.overlapIso i j).toLinearEquiv
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 :
            LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f i * f j)
            (((formalGlueingCan S f).obj M).glue.localModule i)) =
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 :
            LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j)
          (((formalGlueingCan S f).obj M).glue.localModule j)) := by
  -- TODO: unfold the public overlap wrapper on this generator and identify the resulting transport
  -- with the explicit three-factor equivalence proved above, then evaluate that explicit transport.
  sorry

/-- Helper for Lemma 15.90.11: on the canonical overlap square of `Can(M)`, the overlap
isomorphism should send the standard generator to the standard generator. -/
private theorem formalGlueingCan_overlapIso_mk_one
    (M : ModuleCat.{max u w} R) (i j : Fin t) (m : M) :
    (((formalGlueingCan S f).obj M).glue.overlapIso i j).toLinearEquiv
        (LocalizedModule.mk
          (LocalizedModule.mk m 1 :
            LocalizedModule.Away (f i) M) 1 :
          LocalizedModule.Away (f i * f j)
            (((formalGlueingCan S f).obj M).glue.localModule i)) =
        (LocalizedModule.mk
        (LocalizedModule.mk m 1 :
          LocalizedModule.Away (f j) M) 1 :
        LocalizedModule.Away (f i * f j)
          (((formalGlueingCan S f).obj M).glue.localModule j)) := by
  -- Route correction: avoid proving an equality of whole overlap equivalences. Instead, unfold the
  -- public overlap isomorphism only at this generator and compare directly with the explicit
  -- three-factor transport.
  exact @formalGlueingCan_overlapIso_owner_normalized R _ S _ _ t f M i j m

/-- Helper for Lemma 15.90.11: the constant family of localization generators coming from
`m : M` satisfies the glueing compatibility for the canonical object `Can(M)`. -/
private theorem formalGlueingCan_mk_mem_gluedModule
    (M : ModuleCat.{max u w} R) (m : M) :
    (fun i ↦ (LocalizedModule.mk m 1 : LocalizedModule.Away (f i) M)) ∈
      (((formalGlueingCan S f).obj M).glue.gluedModule : Submodule R _) := by
  -- TODO: unfold the kernel defining `gluedModule`, take the `(i,j)`-component of the
  -- compatibility map, and rewrite it to zero using `formalGlueingCan_overlapIso_mk_one`.
  sorry

/-- Helper for Lemma 15.90.11: transpose a morphism `Can(M) ⟶ X` to a compatible degree-zero
section of `X`. -/
private noncomputable def formalGlueingCan_hom_to_h0
    {M : ModuleCat.{max u w} R} {X : Glue S f} :
    (((formalGlueingCan S f).obj M) ⟶ X) → (M ⟶ (formalGlueingH0 S f).obj X) :=
  -- TODO: use `ModuleCat.extendRestrictScalarsAdj` for the base term, send `m` to the glued family
  -- `i ↦ φ.localMap i (LocalizedModule.mk m 1)`, and prove the `H⁰` kernel condition from
  -- `φ.comparison_comm` together with `formalGlueingCan_mk_mem_gluedModule`.
  sorry

/-- Helper for Lemma 15.90.11: reconstruct a morphism `Can(M) ⟶ X` from a degree-zero section of
`X`. -/
private noncomputable def formalGlueingH0_hom_to_can
    {M : ModuleCat.{max u w} R} {X : Glue S f} :
    (M ⟶ (formalGlueingH0 S f).obj X) → (((formalGlueingCan S f).obj M) ⟶ X) :=
  -- TODO: transpose the base projection back across `extendRestrictScalarsAdj`, localize each
  -- projected glued component with `IsLocalizedModule.map`, and recover the comparison and overlap
  -- compatibilities from the defining membership equation in `X.h0Module`.
  sorry

/-- Helper for Lemma 15.90.11: the universal Hom-set equivalence underlying the adjunction
`Can ⊣ H⁰`. -/
private noncomputable def formalGlueingCan_homEquiv
    (M : ModuleCat.{max u w} R) (X : Glue S f) :
    (((formalGlueingCan S f).obj M) ⟶ X) ≃ (M ⟶ (formalGlueingH0 S f).obj X) :=
  -- TODO: package `formalGlueingCan_hom_to_h0` and `formalGlueingH0_hom_to_can`, then prove the
  -- inverse laws by extensionality on the base component and on localization generators.
  sorry

/-- Helper for Lemma 15.90.11: the Hom-set equivalence for `Can ⊣ H⁰` is natural in the module
variable. -/
private theorem formalGlueingCan_homEquiv_naturality_left_symm
    {M₁ M₂ : ModuleCat.{max u w} R} {X : Glue S f}
    (a : M₁ ⟶ M₂) (g : M₂ ⟶ (formalGlueingH0 S f).obj X) :
    (formalGlueingCan_homEquiv (S := S) (f := f) M₁ X).symm (a ≫ g) =
      (formalGlueingCan S f).map a ≫
        (formalGlueingCan_homEquiv (S := S) (f := f) M₂ X).symm g := by
  -- TODO: compare the base transposes using `homEquiv_naturality_left_symm` for
  -- `ModuleCat.extendRestrictScalarsAdj`, and compare the local components on `LocalizedModule.mk`.
  sorry

/-- Helper for Lemma 15.90.11: the Hom-set equivalence for `Can ⊣ H⁰` is natural in the glueing
datum variable. -/
private theorem formalGlueingCan_homEquiv_naturality_right
    {M : ModuleCat.{max u w} R} {X Y : Glue S f}
    (g : ((formalGlueingCan S f).obj M) ⟶ X) (h : X ⟶ Y) :
    formalGlueingCan_homEquiv (S := S) (f := f) M Y (g ≫ h) =
      formalGlueingCan_homEquiv (S := S) (f := f) M X g ≫
        (formalGlueingH0 S f).map h := by
  -- TODO: both sides extract the same base section and the same localized family after composing
  -- with `h`; this should reduce to `AwayModuleGlueing.Hom.projection_gluedMap`.
  sorry

/- Domain-style sampling:
- primary domain: categorical formal glueing for module categories;
- sampled owner declarations:
  `CategoryTheory.Adjunction`,
  `FormalGlueingDatum`,
  `formalGlueingCan`,
  `formalGlueingH0`,
  `Functor.IsLeftAdjoint`;
- best owner abstraction: the source-facing adjunction
  `formalGlueingCan S f ⊣ formalGlueingH0 S f`;
- primitive data: the canonical functors `formalGlueingCan S f` and `formalGlueingH0 S f`;
- derived API: the left/right adjoint typeclass instances used by downstream generic categorical
  lemmas.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCanAdjunction`;
- `core/canonical`: `CategoryTheory.Adjunction`;
- `bridge/view`: the derived adjointness instances below for typeclass-driven reuse.
-/

-- Proof sketch: Remark `15.90.10` already defines the canonical source-facing right adjoint
-- `formalGlueingH0 S f`, so the lemma should expose the actual adjunction
-- `formalGlueingCan S f ⊣ formalGlueingH0 S f`. The proposition-level `IsLeftAdjoint` and
-- `IsRightAdjoint` owners are then derived consequences for downstream typeclass-driven reuse.
/-- Lemma 15.90.11: for the genuine formal glueing category `Glue(R → S, f₁, \ldots, fₜ)` from
Remark `15.90.10`, the canonical functor `Can` is left adjoint to the degree-zero functor
`H^0`. -/
@[stacks 0H77]
noncomputable def formalGlueingCanAdjunction :
    formalGlueingCan S f ⊣ formalGlueingH0 S f := by
  -- Route correction: expose the adjunction through the owner `Adjunction.mkOfHomEquiv`, so the
  -- remaining work is the source-faithful universal-property equivalence between morphisms out of
  -- `Can M` and compatible degree-zero sections of `X`.
  exact
    Adjunction.mkOfHomEquiv
      { homEquiv := formalGlueingCan_homEquiv (S := S) (f := f)
        homEquiv_naturality_left_symm :=
          formalGlueingCan_homEquiv_naturality_left_symm (S := S) (f := f)
        homEquiv_naturality_right :=
          formalGlueingCan_homEquiv_naturality_right (S := S) (f := f) }

noncomputable instance : (formalGlueingCan S f).IsLeftAdjoint :=
  (formalGlueingCanAdjunction f).isLeftAdjoint

noncomputable instance : (formalGlueingH0 S f).IsRightAdjoint :=
  (formalGlueingCanAdjunction f).isRightAdjoint

end
