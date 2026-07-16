import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_71_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_73_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_17
import StacksProject_2024.stacks_project.Chap15.Lemma_15_66_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']

/- Domain-style sampling for Lemma 15.66.4:
- primary domain: flat base change for `Hom` and `Ext` in `ModuleCat`;
- sampled owner declarations:
  `homTensorComparisonHom`,
  `extTensorComparisonHom`,
  `moduleCatExtFlatBaseChangeAdjointComparison`,
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv`;
- best owner abstraction: this file is a `bridge/view` layer. The public source-facing maps are the
  textbook base-change comparisons, while their factors should reuse the chapter owners from
  Lemmas `15.66.3` and `10.73.1` directly;
- primitive data: the ring map `R → R'`, the modules `M`, `N`, and the degree `i`;
- derived API: the tensor-symmetry bridge identifying `N ⊗_R R'` with the owner object
  `R' ⊗_R N`, and the resulting source-facing comparison maps below.
-/

/-- Helper for Lemma 15.66.4: a pseudo-coherent module is `m`-pseudo-coherent for every integer
bound. -/
private theorem moduleCat_isMPseudoCoherent_of_isPseudoCoherent
    (M : ModuleCat.{u} R) (m : ℤ) (hM : M.IsPseudoCoherent) :
    M.IsMPseudoCoherent m := by
  -- Proof comment: Lemma `15.65.6` identifies pseudo-coherence with uniform
  -- `m`-pseudo-coherence, so we only need to specialize the universal statement.
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hM
  exact hM m

/-- Helper for Lemma 15.66.4: over a Noetherian ring, a finite module is `(-d)`-pseudo-coherent
for every natural number `d`. -/
private theorem moduleCat_isNegPseudoCoherent_of_finite
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) :
    M.IsMPseudoCoherent (-(d : ℤ)) := by
  -- Proof comment: over a Noetherian ring, finite modules are pseudo-coherent by
  -- Lemma `15.65.17`, and Lemma `15.65.6` then supplies every fixed negative bound.
  have hM : M.IsPseudoCoherent := by
    simpa using
      (_root_.Module.isPseudoCoherent_iff_finite (R := R) (M := ↥M)).2
        (show Module.Finite R ↥M from inferInstance)
  exact moduleCat_isMPseudoCoherent_of_isPseudoCoherent M (-(d : ℤ)) hM

local notation "extScalars" => ModuleCat.extendScalars (algebraMap R R')

local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R R')

/-- The scalar-extension module `R'`, viewed as an `R`-module, agrees with `ModuleCat.of R R'`. -/
private def baseChangeRingLinearEquiv :
    ModuleCat.of R R' ≃ₗ[R] ↑((resScalars).obj (ModuleCat.of R' R')) := by
  refine
    { toFun := fun x ↦ by simpa using x
      invFun := fun x ↦ by simpa using x
      map_add' := by intro x y; rfl
      map_smul' := by
        intro r x
        have h1 : r • x = (algebraMap R R') r * x := by
          rw [Algebra.smul_def]
        have h2 :
            (RingHom.id R) r •
                (show ↑((resScalars).obj (ModuleCat.of R' R')) from x) =
              (algebraMap R R') r * x := by
          simpa using
            (ModuleCat.restrictScalars.smul_def' (algebraMap R R') r
              (show ModuleCat.of R' R' from x))
        exact h1.trans h2.symm
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }

/-- The canonical tensor-symmetry bridge from `N ⊗_R R'` to the restriction of scalars of the
owner object `R' ⊗_R N`. -/
private def tensorRightBaseChangeIso (N : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
      (resScalars).obj ((extScalars).obj N) := by
  refine LinearEquiv.toModuleIso ?_
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    ((TensorProduct.comm R N (ModuleCat.of R R')).trans
      (TensorProduct.congr baseChangeRingLinearEquiv (LinearEquiv.refl R N)))

/-- The source tensor factors `A ⊗_R R'` and `A ⊗_R ModuleCat.of R R'` are definitionally the same
`R`-module, but this equivalence gives a clean bijection for function-level composition. -/
private def tensorRightLinearEquiv (A : Type u) [AddCommMonoid A] [Module R A] :
    TensorProduct R A R' ≃ₗ[R] TensorProduct R A (ModuleCat.of R R') := by
  simpa using (LinearEquiv.refl R (TensorProduct R A R'))

/-- Postcomposition with the tensor-symmetry bridge is a bijection on `Hom`. -/
private theorem hom_postcompose_bijective_tensorRightBaseChangeIso
    (M N : ModuleCat.{u} R) :
    Function.Bijective
      (fun f : M ⟶ ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ↦
        f ≫ (tensorRightBaseChangeIso N).hom) := by
  refine ⟨?_, ?_⟩
  · intro f g h
    simpa using congrArg (fun k ↦ k ≫ (tensorRightBaseChangeIso N).inv) h
  · intro f
    exact ⟨f ≫ (tensorRightBaseChangeIso N).inv, by simp⟩

/-- Postcomposition with the tensor-symmetry bridge as an additive map on `Hom`. -/
private def homPostcomposeTensorRightBaseChangeAddHom
    (M N : ModuleCat.{u} R) :
    (M ⟶ ModuleCat.of R (TensorProduct R N (ModuleCat.of R R'))) →+
      (M ⟶ (resScalars).obj ((extScalars).obj N)) where
  toFun f := f ≫ (tensorRightBaseChangeIso N).hom
  map_zero' := by
    ext x
    simp
  map_add' _ _ := by
    ext x
    simp

/-- Postcomposition with the degree-zero `Ext` class of the tensor-symmetry bridge is a bijection
on `Ext^i`. -/
private theorem ext_postcomp_bijective_tensorRightBaseChangeIso
    (M N : ModuleCat.{u} R) (i : ℕ) :
    let e :
        ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
          (resScalars).obj ((extScalars).obj N) :=
      tensorRightBaseChangeIso N
    Function.Bijective ((Ext.mk₀ e.hom).postcomp M (add_zero i)) := by
  dsimp
  let e :
      ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
        (resScalars).obj ((extScalars).obj N) :=
    tensorRightBaseChangeIso N
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (((Ext.mk₀ e.inv).postcomp M (add_zero i))) hxy
    simpa [AddMonoidHom.comp_apply, Ext.comp_assoc_of_third_deg_zero, e] using h
  · intro x
    refine ⟨((Ext.mk₀ e.inv).postcomp M (add_zero i)) x, ?_⟩
    have h := congrArg (fun t ↦ x.comp (Ext.mk₀ t) (add_zero i)) e.inv_hom_id
    simp [e] at h ⊢

private noncomputable def homBaseChangeAdjointAddHom
    (M N : ModuleCat.{u} R) :
    (M ⟶ (resScalars).obj ((extScalars).obj N)) →+
      ((extScalars).obj M ⟶ (extScalars).obj N) where
  toFun f :=
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)).symm f
  map_zero' := by
    let e := (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)
    apply e.injective
    change e (e.symm 0) = e 0
    rw [e.apply_symm_apply]
    ext x
    rfl
  map_add' f g := by
    let e := (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)
    apply e.injective
    change e (e.symm (f + g)) = e (e.symm f + e.symm g)
    rw [e.apply_symm_apply]
    ext x
    have hf : (e.symm f) ((1 : R') ⊗ₜ[R] x) = f x := by
      exact congrArg (fun k ↦ k x) (e.apply_symm_apply f)
    have hg : (e.symm g) ((1 : R') ⊗ₜ[R] x) = g x := by
      exact congrArg (fun k ↦ k x) (e.apply_symm_apply g)
    change f x + g x =
      (e.symm f) ((1 : R') ⊗ₜ[R] x) + (e.symm g) ((1 : R') ⊗ₜ[R] x)
    rw [hf, hg]
    rfl

-- Proof sketch: take the canonical tensor comparison
-- `Hom_R(M, N) ⊗_R R' → Hom_R(M, N ⊗_R R')`, transport across the tensor-symmetry bridge to the
-- owner object `R' ⊗_R N`, and then apply the inverse of the tensor-Hom adjunction
-- `(ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv`.
/-- The textbook base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`,
expressed as the composite of the owner tensor comparison from Lemma `15.66.3`, the canonical
tensor-symmetry bridge, and the tensor-Hom adjunction from Lemma `10.14.3`, packaged as an
additive map. -/
private noncomputable def moduleCatHomTensorBaseChangeComparisonAddHom
    (M N : ModuleCat.{u} R) :
    TensorProduct R (M ⟶ N) R' →+
      ((extScalars).obj M ⟶ (extScalars).obj N) :=
  (homBaseChangeAdjointAddHom M N).comp <|
    (homPostcomposeTensorRightBaseChangeAddHom M N).comp <|
    (homTensorComparisonHom M N (ModuleCat.of R R')).hom.toAddMonoidHom.comp <|
    (tensorRightLinearEquiv (M ⟶ N)).toAddEquiv.toAddMonoidHom

/-- Helper for Lemma 15.66.4: on a pure tensor `f ⊗ s`, the Hom base-change comparison sends the
standard generator `1 ⊗ x` to `s ⊗ f x`. -/
private theorem moduleCatHomTensorBaseChangeComparisonAddHom_apply_one_tmul
    (M N : ModuleCat.{u} R) (f : M ⟶ N) (s : R') (x : M) :
    moduleCatHomTensorBaseChangeComparisonAddHom M N (f ⊗ₜ[R] s) ((1 : R') ⊗ₜ[R] x) =
      (show ↑((extScalars).obj N) from s ⊗ₜ[R] f x) := by
  -- Proof comment: evaluate the adjoint transpose on the standard tensor generator and then
  -- unfold the owner-level pure-tensor formulas once.
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (f := algebraMap R R')
    (M := M)
    (N := (extScalars).obj N)
    (φ := moduleCatHomTensorBaseChangeComparisonAddHom M N (f ⊗ₜ[R] s))
    x]
  have hinner :
      (homTensorComparisonHom M N (ModuleCat.of R R')).hom
          ((tensorRightLinearEquiv (M ⟶ N)) (f ⊗ₜ[R] s)) x =
        (show ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) from f x ⊗ₜ[R] s) := by
    change
      ((TensorProduct.rTensorHomToHomRTensor (RingHom.id R) (↑M) (↑N) R')
          (ModuleCat.Hom.hom f ⊗ₜ[R] s)) x =
        f x ⊗ₜ[R] s
    simp [TensorProduct.rTensorHomToHomRTensor_apply]
  simpa [moduleCatHomTensorBaseChangeComparisonAddHom, homBaseChangeAdjointAddHom,
    homPostcomposeTensorRightBaseChangeAddHom, tensorRightBaseChangeIso,
    baseChangeRingLinearEquiv, Algebra.TensorProduct.comm_tmul]
    using congrArg (fun z ↦ (tensorRightBaseChangeIso N).hom z) hinner

/-- Helper for Lemma 15.66.4: on a pure tensor `f ⊗ s`, the Hom base-change comparison sends
`t ⊗ x` to `(t * s) ⊗ f x`. -/
private theorem moduleCatHomTensorBaseChangeComparisonAddHom_apply_tmul
    (M N : ModuleCat.{u} R) (f : M ⟶ N) (s t : R') (x : M) :
    moduleCatHomTensorBaseChangeComparisonAddHom M N (f ⊗ₜ[R] s) (t ⊗ₜ[R] x) =
      (show ↑((extScalars).obj N) from (t * s) ⊗ₜ[R] f x) := by
  -- Proof comment: rewrite `t ⊗ x` as `t • (1 ⊗ x)` and use the generator calculation above.
  rw [show (t ⊗ₜ[R] x : (extScalars).obj M) = t • ((1 : R') ⊗ₜ[R] x) by
    simpa [TensorProduct.smul_tmul']]
  simp [moduleCatHomTensorBaseChangeComparisonAddHom_apply_one_tmul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.66.4: the Hom base-change comparison sends `𝟙_N ⊗ s` to scalar
multiplication by `s` on `N ⊗[R] R'`. -/
private theorem moduleCatHomTensorBaseChangeComparisonAddHom_id_tmul_eq_smul_id
    (N : ModuleCat.{u} R) (s : R') :
    moduleCatHomTensorBaseChangeComparisonAddHom N N (𝟙 N ⊗ₜ[R] s) =
      s • 𝟙 ((extScalars).obj N) := by
  -- Proof comment: both maps are `R'`-linear endomorphisms, so it is enough to compare them on
  -- the pure tensors `t ⊗ x`.
  ext y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro t x
    -- Proof comment: the previous pure-tensor computation identifies both endomorphisms with
    -- multiplication by `t * s` on `x`.
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      moduleCatHomTensorBaseChangeComparisonAddHom_apply_tmul N N (𝟙 N) s t x
  · intro y z hy hz
    simp [hy, hz]

private theorem moduleCatHomTensorBaseChangeComparison_map_smul
    (M N : ModuleCat.{u} R) (r : R')
    (x : TensorProduct R R' (M ⟶ N)) :
    moduleCatHomTensorBaseChangeComparisonAddHom M N
        (TensorProduct.comm R R' (M ⟶ N) (r • x)) =
      r • moduleCatHomTensorBaseChangeComparisonAddHom M N
        (TensorProduct.comm R R' (M ⟶ N) x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: the comparison is additive, so the zero tensor case is immediate.
    simp
  · intro s f
    -- Proof comment: after commuting the tensor factors, both sides are `R'`-linear maps out of
    -- `M ⊗[R] R'`; the extensionality principle reduces to the standard generators `1 ⊗ y`.
    ext y
    simp [moduleCatHomTensorBaseChangeComparisonAddHom_apply_one_tmul,
      TensorProduct.smul_tmul']
    exact
      congrArg (fun a : R' ↦ a ⊗ₜ[R] (ConcreteCategory.hom f) y)
        (by simpa [Algebra.smul_def] using (rfl : r * s = r * s))
  · intro x y hx hy
    -- Proof comment: additivity propagates the pure-tensor calculation to arbitrary tensors.
    simp [hx, hy]

/-- The canonical owner-object form
`R' ⊗_R Hom_R(M, N) → Hom_{R'}(R' ⊗_R M, R' ⊗_R N)` of the textbook base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`. -/
noncomputable def moduleCatHomTensorBaseChangeComparison
    (R' : Type u) [CommRing R'] [Algebra R R'] (M N : ModuleCat.{u} R) :
    ModuleCat.of R' (TensorProduct R R' (M ⟶ N)) ⟶
      ModuleCat.of R' (((ModuleCat.extendScalars (algebraMap R R')).obj M ⟶
        (ModuleCat.extendScalars (algebraMap R R')).obj N)) := by
  let hAdd :
      TensorProduct R (M ⟶ N) R' →+
        ((ModuleCat.extendScalars (algebraMap R R')).obj M ⟶
          (ModuleCat.extendScalars (algebraMap R R')).obj N) :=
    moduleCatHomTensorBaseChangeComparisonAddHom M N
  exact ModuleCat.ofHom
    { toFun := hAdd ∘ TensorProduct.comm R R' (M ⟶ N)
      map_add' := by
        intro x y
        simp [hAdd]
      map_smul' := by
        intro r x
        simpa [hAdd] using moduleCatHomTensorBaseChangeComparison_map_smul M N r x }

-- Proof sketch: the source-facing textbook map is the composite of the owner tensor comparison,
-- the tensor-symmetry bridge, and the inverse tensor-Hom adjunction. Under finite presentation,
-- the tensor comparison is bijective, while the other two factors are canonical equivalences.
/-- Lemma 15.66.4 (1): for a flat ring map `R → R'`, if `M` is finitely presented, then the
canonical base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective. -/
theorem moduleCat_homTensorBaseChange_bijective_of_finitePresentation
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hf : (algebraMap R R').Flat) :
    Function.Bijective (moduleCatHomTensorBaseChangeComparison R' M N) := by
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  have hTensor : Function.Bijective (homTensorComparisonHom M N (ModuleCat.of R R')).hom := by
    let f := homTensorComparisonHom M N (ModuleCat.of R R')
    letI : IsIso f := homTensorComparison_isIso_of_finitePresentation M N (ModuleCat.of R R')
    simpa using ConcreteCategory.bijective_of_isIso f
  have hAdd :
      Function.Bijective
        ((moduleCatHomTensorBaseChangeComparisonAddHom M N :
          TensorProduct R (M ⟶ N) R' → ((extScalars).obj M ⟶ (extScalars).obj N))) := by
    simpa [moduleCatHomTensorBaseChangeComparisonAddHom] using
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
          ((extScalars).obj N)).symm.bijective).comp
        ((hom_postcompose_bijective_tensorRightBaseChangeIso M N).comp
          (hTensor.comp (tensorRightLinearEquiv (M ⟶ N)).bijective))
  simpa [moduleCatHomTensorBaseChangeComparison, moduleCatHomTensorBaseChangeComparisonAddHom]
    using hAdd.comp (TensorProduct.comm R R' (M ⟶ N)).bijective

/-- Lemma 15.66.4 (1): for a flat ring map `R → R'`, if `M` is finitely presented, then the
canonical base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism in `ModuleCat R'`. -/
theorem moduleCat_homTensorBaseChange_isIso_of_finitePresentation
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hf : (algebraMap R R').Flat) :
    IsIso (moduleCatHomTensorBaseChangeComparison R' M N) := by
  let e :=
    LinearEquiv.ofBijective
      (moduleCatHomTensorBaseChangeComparison R' M N).hom
      (moduleCat_homTensorBaseChange_bijective_of_finitePresentation M N hf)
  have he :
      e.toModuleIso.hom = moduleCatHomTensorBaseChangeComparison R' M N := by
    ext x
    rfl
  rw [← he]
  infer_instance

-- Proof sketch: compose the tensor comparison
-- `Ext^i_R(M, N) ⊗_R R' → Ext^i_R(M, N ⊗_R R')` with the adjoint flat base-change comparison
-- `Ext^i_R(M, N ⊗_R R') → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`.
/-- The textbook base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`,
expressed as the composite of the owner maps from Lemmas `15.66.3` and `10.73.1`, packaged as
an additive map. -/
private noncomputable def moduleCatExtTensorBaseChangeComparisonAddHom
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) :
    TensorProduct R (Ext.{u} M N i) R' →+
      Ext.{u} ((extScalars).obj M) ((extScalars).obj N) i :=
  (moduleCatExtFlatBaseChangeAdjointComparison
      M
      ((extScalars).obj N)
      hf
      i).comp <|
    ((Ext.mk₀ (tensorRightBaseChangeIso N).hom).postcomp M (add_zero i)).comp <|
    (extTensorComparisonHom M N (ModuleCat.of R R') i).hom.toAddMonoidHom.comp <|
    (tensorRightLinearEquiv (Ext.{u} M N i)).toAddEquiv.toAddMonoidHom

/-- Helper for Lemma 15.66.4: on a pure tensor, the full `Ext` base-change comparison is the
owner composite with the tensor-symmetry bridge and flat-base-change adjoint map. -/
private theorem moduleCatExtTensorBaseChangeComparisonAddHom_apply_tmul
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ)
    (η : Ext.{u} M N i) (s : R') :
    moduleCatExtTensorBaseChangeComparisonAddHom M N hf i (η ⊗ₜ[R] s) =
      moduleCatExtFlatBaseChangeAdjointComparison
          M
          ((extScalars).obj N)
          hf
          i
        (((Ext.mk₀ (tensorRightBaseChangeIso N).hom).postcomp M (add_zero i))
          ((extTensorComparisonHom M N (ModuleCat.of R R') i).hom (η ⊗ₜ[R] s))) := by
  -- Proof comment: unfold the packaged comparison once and note that
  -- `tensorRightLinearEquiv` is definitionally the identity on the tensor product.
  simp [moduleCatExtTensorBaseChangeComparisonAddHom, tensorRightLinearEquiv]

/-- Helper for Lemma 15.66.4: in the final `Ext_{R'}` codomain, postcomposition by the scalar
endomorphism `a • 𝟙` is ordinary scalar multiplication. -/
private theorem ext_comp_smul_id_eq_smul
    (M N : ModuleCat.{u} R') (i : ℕ) (a : R') (e : Ext.{u} M N i) :
    e.comp (Ext.mk₀ (a • 𝟙 N)) (add_zero i) = a • e := by
  -- Proof comment: this is the target-side scalar action formula on `Ext`.
  simpa using (smul_eq_comp_mk₀ e a).symm

private theorem moduleCatExtTensorBaseChangeComparison_map_smul
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) (r : R')
    (x : TensorProduct R R' (Ext.{u} M N i)) :
    moduleCatExtTensorBaseChangeComparisonAddHom M N hf i
        (TensorProduct.comm R R' (Ext.{u} M N i) (r • x)) =
      r • moduleCatExtTensorBaseChangeComparisonAddHom M N hf i
        (TensorProduct.comm R R' (Ext.{u} M N i) x) :=
by
  /-- Helper for Lemma 15.66.4: after commuting the tensor factors, the full Ext base-change
  comparison sends `η ⊗ (r * s)` to `r` times the image of `η ⊗ s`. -/
  have moduleCatExtTensorBaseChangeComparison_apply_tmul_mul
      (η : Ext.{u} M N i) (s : R') :
      moduleCatExtTensorBaseChangeComparisonAddHom M N hf i (η ⊗ₜ[R] (r * s)) =
        r • moduleCatExtTensorBaseChangeComparisonAddHom M N hf i (η ⊗ₜ[R] s) := by
    -- Route correction: the ill-typed earlier route tried to put an ambient `R'`-module
    -- structure on the intermediate `Ext_R` group. We instead unfold the final composite once,
    -- rewrite the degree-zero factor to the scalar endomorphism of `N ⊗[R] R'`, and only then
    -- use `smul_eq_comp_mk₀` in the final `Ext_{R'}` codomain.
    let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R R')
    let e :
        ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
          (resScalars).obj ((extScalars).obj N) :=
      tensorRightBaseChangeIso N
    have hs_mul :
        moduleCatHomTensorBaseChangeComparisonAddHom N N (𝟙 N ⊗ₜ[R] (r * s)) =
          (r * s) • 𝟙 ((extScalars).obj N) := by
      simpa using
        moduleCatHomTensorBaseChangeComparisonAddHom_id_tmul_eq_smul_id (R := R) N (r * s)
    have hs :
        moduleCatHomTensorBaseChangeComparisonAddHom N N (𝟙 N ⊗ₜ[R] s) =
          s • 𝟙 ((extScalars).obj N) := by
      simpa using
        moduleCatHomTensorBaseChangeComparisonAddHom_id_tmul_eq_smul_id (R := R) N s
    -- TODO: identify the inner `Ext` comparison on pure tensors with postcomposition by the two
    -- scalar endomorphisms above, then use functoriality of `extScalars.mapExtAddHom`,
    -- associativity of `Ext` composition, and `ext_comp_smul_id_eq_smul` to pull out the outer
    -- scalar. The new helper `moduleCatExtTensorBaseChangeComparisonAddHom_apply_tmul` has
    -- already normalized both sides to this owner-level comparison shape.
    have hscalar :
        moduleCatExtTensorBaseChangeComparisonAddHom M N hf i (η ⊗ₜ[R] (r * s)) =
          r • moduleCatExtTensorBaseChangeComparisonAddHom M N hf i (η ⊗ₜ[R] s) := by
      -- Proof comment: first rewrite both sides to the normalized owner composite supplied by
      -- `moduleCatExtTensorBaseChangeComparisonAddHom_apply_tmul`; the remaining blocker is the
      -- naturality of `moduleCatExtFlatBaseChangeAdjointComparison` with respect to the scalar
      -- endomorphisms identified above.
      rw [moduleCatExtTensorBaseChangeComparisonAddHom_apply_tmul,
        moduleCatExtTensorBaseChangeComparisonAddHom_apply_tmul]
      sorry
    exact hscalar
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: additivity of the comparison makes the zero tensor case immediate.
    simp
  · intro s η
    -- Proof comment: commute the tensor factors and reduce the `R'`-linearity claim to the
    -- dedicated pure-tensor scalar formula.
    simpa [Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', mul_assoc, mul_left_comm,
      mul_comm] using moduleCatExtTensorBaseChangeComparison_apply_tmul_mul η s
  · intro x y hx hy
    -- Proof comment: the additive induction step now follows directly from the induction
    -- hypotheses.
    simp [hx, hy]

/-- The canonical owner-object form
`R' ⊗_R Ext^i_R(M, N) → Ext^i_{R'}(R' ⊗_R M, R' ⊗_R N)` of the textbook base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`. -/
noncomputable def moduleCatExtTensorBaseChangeComparison
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) :
    ModuleCat.of R' (TensorProduct R R' (Ext.{u} M N i)) ⟶
      ModuleCat.of R' (Ext.{u} ((extScalars).obj M) ((extScalars).obj N) i) :=
  ModuleCat.ofHom
    { toFun := moduleCatExtTensorBaseChangeComparisonAddHom M N hf i ∘
        TensorProduct.comm R R' (Ext.{u} M N i)
      map_add' := by
        intro x y
        let hAdd := moduleCatExtTensorBaseChangeComparisonAddHom M N hf i ∘
          TensorProduct.comm R R' (Ext.{u} M N i)
        simp
      map_smul' := by
        intro r x
        exact moduleCatExtTensorBaseChangeComparison_map_smul M N hf i r x }

-- Proof sketch: compose the tensor comparison
-- `Ext^i_R(M, N) ⊗_R R' → Ext^i_R(M, N ⊗_R R')` with the adjoint flat base-change comparison
-- `Ext^i_R(M, N ⊗_R R') → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`.
/-- Companion factorization result for Lemma 15.66.4 (2): each owner map appearing in the
construction of `moduleCatExtTensorBaseChangeComparison` is bijective. -/
private theorem moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    Function.Bijective (extTensorComparisonHom M N (ModuleCat.of R R') i).hom ∧
      Function.Bijective
        (moduleCatExtFlatBaseChangeAdjointComparison
          M
          ((extScalars).obj N)
          hf
          i) := by
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  constructor
  · let f := extTensorComparisonHom M N (ModuleCat.of R R') i
    letI : IsIso f := extTensorComparison_isIso_of_isMPseudoCoherent
      M N (ModuleCat.of R R') m i hM hi
    simpa using ConcreteCategory.bijective_of_isIso f
  · simpa using moduleCat_ext_flat_baseChange_adjoint_bijective
      M ((extScalars).obj N) hf i

-- Proof sketch: the source-facing textbook map is the composite of the two owner maps from the
-- previous theorem.
/-- Lemma 15.66.4 (2): for a flat ring map `R → R'`, if `M` is `(-m)`-pseudo-coherent, then the
canonical base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective for every `i < m`. -/
theorem moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    Function.Bijective (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  rcases
      moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
        M N m i hf hM hi with
    ⟨hTensor, hAdj⟩
  have hAdd :
      Function.Bijective (moduleCatExtTensorBaseChangeComparisonAddHom M N hf i) := by
    simpa [moduleCatExtTensorBaseChangeComparisonAddHom] using
      hAdj.comp
      ((ext_postcomp_bijective_tensorRightBaseChangeIso M N i).comp
        (hTensor.comp (tensorRightLinearEquiv (Ext.{u} M N i)).bijective))
  simpa [moduleCatExtTensorBaseChangeComparison, moduleCatExtTensorBaseChangeComparisonAddHom]
    using hAdd.comp (TensorProduct.comm R R' (Ext.{u} M N i)).bijective

/-- Lemma 15.66.4 (2): for a flat ring map `R → R'`, if `M` is `(-m)`-pseudo-coherent, then the
canonical base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism in `ModuleCat R'` for every `i < m`. -/
theorem moduleCat_extTensorBaseChange_isIso_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  let e :=
    LinearEquiv.ofBijective
      (moduleCatExtTensorBaseChangeComparison M N hf i).hom
      (moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent M N m i hf hM hi)
  have he :
      e.toModuleIso.hom = moduleCatExtTensorBaseChangeComparison M N hf i := by
    ext x
    rfl
  rw [← he]
  infer_instance

-- Proof sketch: over a Noetherian ring, a finite module is pseudo-coherent; then it is
-- `(-(i + 1))`-pseudo-coherent, and the previous theorem applies with `m = i + 1`.
/-- Companion factorization result for Lemma 15.66.4 (3): under the Noetherian finite hypotheses,
each owner map appearing in `moduleCatExtTensorBaseChangeComparison` is bijective in every
degree. -/
private theorem moduleCat_extTensorBaseChange_factorization_bijective_of_isNoetherianRing_of_finite
    [IsNoetherianRing R] (M N : ModuleCat.{u} R) [Module.Finite R M]
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (extTensorComparisonHom M N (ModuleCat.of R R') i).hom ∧
      Function.Bijective
        (moduleCatExtFlatBaseChangeAdjointComparison
          M
          ((extScalars).obj N)
          hf
          i) := by
  exact moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
    M N (i + 1) i hf
    (moduleCat_isNegPseudoCoherent_of_finite (R := R) M (i + 1))
    (Nat.lt_succ_self i)

-- Proof sketch: combine the previous Noetherian finite reduction with part `(2)`.
/-- Lemma 15.66.4 (3): if `R` is Noetherian and `M` is finite, then for every `i` the canonical
base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective. -/
theorem moduleCat_extTensorBaseChange_bijective_of_isNoetherianRing_of_finite
    [IsNoetherianRing R] (M N : ModuleCat.{u} R) [Module.Finite R M]
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  exact moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent
    M N (i + 1) i hf
    (moduleCat_isNegPseudoCoherent_of_finite (R := R) M (i + 1))
    (Nat.lt_succ_self i)

end

end CategoryTheory
