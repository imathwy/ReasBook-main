import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_15
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap10.Lemma_10_76_1
import stacks_proof.stacks_project.Chap10.Lemma_10_77_5

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Lemma 10.99.17: an `A`-module annihilated by `I` carries the induced
`A / I`-module structure. -/
abbrev quotient_module_of_annihilator_le
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) : Module Ā K :=
  Module.IsTorsionBySet.module
    ((Module.isTorsionBySet_iff_subset_annihilator A K).2 hK)

/-- Helper for Lemma 10.99.17: the induced `A / I`-module structure remains compatible with the
original `A`-action. -/
abbrev quotient_module_isScalarTower_of_annihilator_le
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    @IsScalarTower A Ā K _ (quotient_module_of_annihilator_le (A := A) (f := f) hK).toSMul _ :=
  Module.IsTorsionBySet.isScalarTower
    ((Module.isTorsionBySet_iff_subset_annihilator A K).2 hK)

/-- Helper for Lemma 10.99.17: the canonical free `A / I`-cover of an `I`-annihilated module is
surjective. This is the source proof's free presentation of modules killed by the whole ideal. -/
lemma quotient_canonical_free_cover_surjective
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    Function.Surjective (Finsupp.linearCombination Ā (id : K → K)) := by
  letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  -- The singleton basis vector at `x` maps back to `x`.
  simpa using Finsupp.linearCombination_surjective Ā Function.surjective_id

/-- Helper for Lemma 10.99.17: the kernel inclusion for the canonical free `A / I`-cover is exact
before the cover map. This is the exact prefix used in the public-owner Tor bootstrap. -/
lemma quotient_canonical_free_cover_exact
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
    Function.Exact
      (LinearMap.ker πBar).subtype πBar := by
  letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  -- The canonical free cover is exact by the standard kernel-inclusion exactness lemma.
  simpa [πBar] using LinearMap.exact_subtype_ker_map πBar

/-- Helper for Lemma 10.99.17: the kernel of the canonical free `A / I`-cover is still
annihilated by `I`. This keeps the whole-ideal induction inside the quotient-module world. -/
lemma span_le_annihilator_canonical_free_cover_ker
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let _ : IsScalarTower A Ā K :=
      quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
    let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
    I ≤ Module.annihilator A
      (LinearMap.ker πBar) := by
  letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  letI : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  -- The kernel is an `A / I`-module, so every scalar coming from `I` acts trivially on it.
  have hbot : I • (⊤ : Submodule A (LinearMap.ker πBar)) = ⊥ := by
    simpa using
      (ideal_smul_top_eq_bot_of_quotient_module (R := A)
        (N := LinearMap.ker πBar))
  simpa [Submodule.annihilator_top] using
    ((Submodule.le_annihilator_iff (R := A) (M := LinearMap.ker πBar)).2 hbot)

/-- Helper for Lemma 10.99.17: in every degree, the quotient-first public owner
`K ↦ Tor_n^A(K, M)` is naturally isomorphic to the fixed-left source owner
`K ↦ Tor'_n^A(M, K)`. -/
noncomputable def tor_left_owner_iso (n : ℕ) :
    (((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)) ≅
      ((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)) where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) n).hom.app X).app (ModuleCat.of A M))
      naturality := by
        intro X Y g
        -- Naturality of `tor_flip_iso` in the first Tor variable becomes naturality of the fixed
        -- right-variable owner after evaluation at `M`.
        simpa using congrArg (fun α => α.app (ModuleCat.of A M))
          ((tor_flip_iso (ModuleCat A) n).hom.naturality g) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) n).inv.app X).app (ModuleCat.of A M))
      naturality := by
        intro X Y g
        -- The inverse comparison is natural for the same reason.
        simpa using congrArg (fun α => α.app (ModuleCat.of A M))
          ((tor_flip_iso (ModuleCat A) n).inv.naturality g) }
  hom_inv_id := by
    ext X x
    -- The componentwise inverse law is inherited from `tor_flip_iso` after evaluation at `M`.
    have h := congrArg (fun α => α.app (ModuleCat.of A M))
      ((tor_flip_iso (ModuleCat A) n).hom_inv_id_app X)
    simpa using congrArg (fun g => g x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- The same componentwise argument proves the other inverse law.
    have h := congrArg (fun α => α.app (ModuleCat.of A M))
      ((tor_flip_iso (ModuleCat A) n).inv_hom_id_app X)
    simpa using congrArg (fun g => g x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Chap10 Lemma 10 99 17: quotient-first public-owner vanishing transports to the
fixed-left source owner through `tor_left_owner_iso`. -/
lemma isZero_sourceOwner_of_isZero_publicFlip
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K]
    (h :
      IsZero
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K)))) :
    IsZero
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K))) := by
  let e := (tor_left_owner_iso (A := A) (M := M) n).app (ModuleCat.of A K)
  -- Proof comment: the comparison isomorphism has public-flipped source and source-owner target,
  -- so its inverse transports the public vanishing to the source owner.
  exact IsZero.of_iso h e.symm

/-- Helper for Chap10 Lemma 10 99 17: fixed-left source-owner vanishing transports back to the
quotient-first public owner through `tor_left_owner_iso`. -/
lemma isZero_publicFlip_of_isZero_sourceOwner
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K]
    (h :
      IsZero
        ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K)))) :
    IsZero
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K))) := by
  let e := (tor_left_owner_iso (A := A) (M := M) n).app (ModuleCat.of A K)
  -- Proof comment: this is the forward direction of the same owner comparison, now returning to
  -- the public quotient-first owner used by the generator descent.
  exact IsZero.of_iso h e

/-- Helper for Lemma 10.99.17: degree `1` of `tor_left_owner_iso`. -/
noncomputable abbrev tor_one_left_owner_iso :
    (((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)) ≅
      ((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)) :=
  tor_left_owner_iso (A := A) (M := M) 1

/-- Helper for Lemma 10.99.17: in every degree, `tor_flip_iso` identifies the module-first public
owner `K ↦ Tor_n^A(M, K)` with the flipped source owner `K ↦ Tor'_n^A(K, M)`. This is the
degree-generic owner transport used to move the quotient hypotheses into the source-faithful
orientation. -/
noncomputable def tor_module_flip_owner_iso (n : ℕ) :
    ((Tor (ModuleCat A) n).obj (ModuleCat.of A M)) ≅
      ((Functor.flip (Tor' (ModuleCat A) n)).obj (ModuleCat.of A M)) := by
  -- Proof comment: this is exactly the degree-`n` component of `tor_flip_iso` evaluated at `M`.
  simpa using ((tor_flip_iso (ModuleCat A) n).app (ModuleCat.of A M))

/-- Helper for Lemma 10.99.17: degree `1` of `tor_module_flip_owner_iso`. -/
noncomputable abbrev tor_one_module_flip_owner_iso :
    ((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)) ≅
      ((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)) :=
  tor_module_flip_owner_iso (A := A) (M := M) 1

/-- Helper for Lemma 10.99.17: if `K` is annihilated by `I`, then the source tensor
`M ⊗[A] K` can be rewritten as the quotient tensor `(M / IM) ⊗[A / I] K`. This is the stable
transport needed to compare the public `A`-tensor tail with the flat `A / I`-tensor tail on the
canonical free cover. -/
noncomputable def tensor_compare_of_quotient_module
    {K : Type u} [AddCommGroup K] [Module Ā K] [Module A K] [IsScalarTower A Ā K] :
    M ⊗[A] K ≃ₗ[A] M̄ ⊗[Ā] K := by
  -- Proof comment: first commute the tensor, then cancel the base change `A → Ā`,
  -- replace `Ā ⊗[A] M` by `M / IM`, and finally commute back to restore the public owner order.
  let e₁ := TensorProduct.comm A M K
  let e₂ :=
    LinearEquiv.restrictScalars A <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ā Ā K M).symm
  let J : Ideal A := Ideal.span (Set.range f)
  let e₃base : (Ā ⊗[A] M) ≃ₗ[Ā] M̄ :=
    linearEquiv_over_quotient (R := A)
      (TensorProduct.quotTensorEquivQuotSMul M J)
  let e₃ :=
    LinearEquiv.restrictScalars A <|
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Ā K) e₃base
  let e₄ := LinearEquiv.restrictScalars A <| TensorProduct.comm Ā K M̄
  exact e₁.trans (e₂.trans (e₃.trans e₄))

/-- Helper for Lemma 10.99.17: if `K` is annihilated by `I`, then the source tensor
`M ⊗[A] K` can be rewritten as the quotient tensor `(M / IM) ⊗[A / I] K`. -/
noncomputable def tensor_compare_of_annihilated
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let _ : IsScalarTower A Ā K :=
      quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
    M ⊗[A] K ≃ₗ[A] M̄ ⊗[Ā] K :=
  let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let _ : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  tensor_compare_of_quotient_module (A := A) (M := M) (f := f)

/-- Helper for Lemma 10.99.17: on pure tensors, `tensor_compare_of_annihilated` is the expected
quotient-tensor comparison sending `m ⊗ x` to `\bar m ⊗ x`. -/
lemma tensor_compare_of_annihilated_tmul
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) (m : M) (x : K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let _ : IsScalarTower A Ā K :=
      quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
    tensor_compare_of_annihilated (A := A) (M := M) (f := f) hK (m ⊗ₜ[A] x) =
      ((Submodule.mkQ (I • (⊤ : Submodule A M))) m : M̄) ⊗ₜ[Ā] x := by
  let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let _ : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  -- Proof comment: every factor in the explicit composite defining `tensor_compare` has the
  -- expected action on pure tensors, so the composite collapses to the quotient class of `m`.
  simp [tensor_compare_of_annihilated, tensor_compare_of_quotient_module, linearEquiv_over_quotient,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

/-- Helper for Lemma 10.99.17: for the canonical free `A / I`-cover of an `I`-annihilated
module, the tensor comparison commutes with the kernel inclusion. -/
lemma tensor_compare_of_annihilated_canonical_cover_kernel_square
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let _ : IsScalarTower A Ā K :=
      quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
    let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
    (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
      (K := K →₀ Ā)).toLinearMap.comp
        (LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) =
      ((LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype).restrictScalars A).comp
        (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
          (K := LinearMap.ker πBar)).toLinearMap := by
  let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let _ : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  -- Proof comment: after evaluating on pure tensors, both sides are the same quotient pure tensor
  -- with the kernel element viewed in the ambient free module.
  ext m x
  simp [tensor_compare_of_quotient_module, linearEquiv_over_quotient,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

/-- Helper for Lemma 10.99.17: after transporting to the quotient tensor world, flatness of
`M / IM` over `A / I` makes the tensor tail of the canonical free cover injective. -/
lemma tensor_tail_injective_of_flat_canonical_cover
    {K : Type u} [AddCommGroup K] [Module A K]
    (hquot : Module.Flat Ā M̄)
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let _ : IsScalarTower A Ā K :=
      quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
    let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
    Function.Injective
      (LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) := by
  let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let _ : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  dsimp
  have hSquare :
      (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
        (K := K →₀ Ā)).toLinearMap.comp
          (LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) =
        ((LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype).restrictScalars A).comp
          (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
            (K := LinearMap.ker πBar)).toLinearMap :=
    tensor_compare_of_annihilated_canonical_cover_kernel_square
      (A := A) (M := M) (f := f) hK
  have hbar_injective :
      Function.Injective (LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype) := by
    let _ : Module.Flat Ā M̄ := hquot
    -- Proof comment: flatness over the quotient ring preserves injectivity of the kernel
    -- inclusion after tensoring on the left.
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M̄)
      (LinearMap.ker πBar).subtype Subtype.val_injective
  -- Proof comment: apply the quotient tensor comparison to an equality in the `A`-tensor world
  -- and then use injectivity of the transported `A / I`-tensor map.
  intro x y hxy
  have hxy' :
      (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
        (K := K →₀ Ā)).toLinearMap
          ((LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) x) =
        (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
          (K := K →₀ Ā)).toLinearMap
          ((LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) y) := by
    exact congrArg
      ((tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
        (K := K →₀ Ā)).toLinearMap) hxy
  have hbar_eq :
      (LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype)
          ((tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
            (K := LinearMap.ker πBar)) x) =
        (LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype)
          ((tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
            (K := LinearMap.ker πBar)) y) := by
    calc
      (LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype)
          ((tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
            (K := LinearMap.ker πBar)) x)
          =
        (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
          (K := K →₀ Ā))
            ((LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) x) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.congr_fun hSquare x).symm
      _ =
        (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
          (K := K →₀ Ā))
            ((LinearMap.lTensor M ((LinearMap.ker πBar).subtype.restrictScalars A)) y) := hxy'
      _ =
        (LinearMap.lTensor M̄ (LinearMap.ker πBar).subtype)
          ((tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
            (K := LinearMap.ker πBar)) y) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.congr_fun hSquare y)
  have hcompare_eq :
      (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
        (K := LinearMap.ker πBar)) x =
        (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
          (K := LinearMap.ker πBar)) y :=
    hbar_injective hbar_eq
  exact
    (tensor_compare_of_quotient_module (A := A) (M := M) (f := f)
      (K := LinearMap.ker πBar)).injective hcompare_eq

/-- Helper for Lemma 10.99.17: every module already defined over `A / I` is annihilated by `I`
after restricting scalars back to `A`. -/
lemma span_le_annihilator_of_quotient_module
    {K : Type u} [AddCommGroup K] [Module Ā K] [Module A K] [IsScalarTower A Ā K] :
    I ≤ Module.annihilator A K := by
  -- Proof comment: quotient scalars kill the whole ideal, so `I • ⊤ = ⊥`, which is equivalent
  -- to containment in the annihilator.
  have hbot : I • (⊤ : Submodule A K) = ⊥ := by
    simpa using ideal_smul_top_eq_bot_of_quotient_module (R := A) (N := K)
  simpa [Submodule.annihilator_top] using
    ((Submodule.le_annihilator_iff (R := A) (M := K)).2 hbot)

/-- Helper for Lemma 10.99.17: injectivity transfers across a commutative ladder of linear
equivalences. -/
lemma injective_of_ladder_linear_equiv
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    {u : X₁ →ₗ[A] X₂} {v : Y₁ →ₗ[A] Y₂} {e₁ : X₁ ≃ₗ[A] Y₁} {e₂ : X₂ ≃ₗ[A] Y₂}
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u)
    (hu : Function.Injective u) :
    Function.Injective v := by
  -- Proof comment: pull an equality in the target ladder back through both equivalences and then
  -- apply injectivity of the known horizontal map.
  intro x y hxy
  apply e₁.symm.injective
  apply hu
  apply e₂.injective
  calc
    e₂ (u (e₁.symm x)) = v x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = v y := hxy
    _ = e₂ (u (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

end
