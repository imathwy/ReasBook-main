import Mathlib
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_12_1 (from Chap10) -/
universe u v w z

variable {R : Type u} {M : Type v} {N : Type w} {P : Type z}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/- Definition 10.12.1: mathlib records bilinearity of an unbundled function by
`IsBilinearMap R f`, and the preferred bundled bilinear maps are linear maps
`M →ₗ[R] N →ₗ[R] P`, produced by `IsBilinearMap.toLinearMap`. -/
recall IsBilinearMap
recall IsBilinearMap.toLinearMap

/-- A two-variable function is bilinear exactly when each partial map is `R`-linear. -/
theorem isBilinearMap_iff_isLinearMap_left_right {f : M → N → P} :
    IsBilinearMap R f ↔
      (∀ x, IsLinearMap R (f x)) ∧ ∀ y, IsLinearMap R (fun x ↦ f x y) :=
by
  constructor
  · intro hf
    exact ⟨fun x ↦ (hf.toLinearMap x).isLinear, fun y ↦ (hf.toLinearMap.flip y).isLinear⟩
  · rintro ⟨hleft, hright⟩
    exact
      { add_left := fun x₁ x₂ y ↦ (hright y).map_add x₁ x₂
        smul_left := fun c x y ↦ (hright y).map_smul c x
        add_right := fun x y₁ y₂ ↦ (hleft x).map_add y₁ y₂
        smul_right := fun c x y ↦ (hleft x).map_smul c y }

/-- A function on the Cartesian product of two `R`-modules is bilinear exactly when each partial
map is `R`-linear. -/
theorem isBilinearMap_prod_iff_isLinearMap_left_right {f : M × N → P} :
    IsBilinearMap R (Function.curry f) ↔
      (∀ x, IsLinearMap R (fun y ↦ f (x, y))) ∧ ∀ y, IsLinearMap R (fun x ↦ f (x, y)) :=
by
  simpa using
    (show IsBilinearMap R (Function.curry f) ↔
        (∀ x, IsLinearMap R ((Function.curry f) x)) ∧
          ∀ y, IsLinearMap R (fun x ↦ (Function.curry f) x y) from
      isBilinearMap_iff_isLinearMap_left_right)

/-! ### Lemma_10_12_2 (from Chap10) -/
open scoped TensorProduct

universe u v w z z'

section

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/- Lemma 10.12.2: the canonical bilinear map `TensorProduct.mk R M N` exhibits `M ⊗[R] N` as the
tensor product of `M` and `N`, so every `R`-bilinear map out of `M × N` factors uniquely through
`M ⊗[R] N`. -/
recall TensorProduct.isTensorProduct

variable {T : Type z} {T' : Type z'}
  [AddCommMonoid T] [Module R T]
  [AddCommMonoid T'] [Module R T']

/-- Any two realizations of the tensor product of `M` and `N` are uniquely linearly equivalent over
their defining bilinear maps. -/
theorem isTensorProduct_existsUnique_linearEquiv
    {g : M →ₗ[R] N →ₗ[R] T} {g' : M →ₗ[R] N →ₗ[R] T'}
    (hg : IsTensorProduct g) (hg' : IsTensorProduct g') :
    ∃! j : T ≃ₗ[R] T', ∀ x y, j (g x y) = g' x y := by
  refine ⟨hg.equiv.symm ≪≫ₗ hg'.equiv, ?_, ?_⟩
  · intro x y
    simp
  · intro j hj
    ext z
    refine hg.inductionOn z ?_ (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · rw [hj x y]
      simp
    · simp [hx, hy]

end

/-! ### Lemma_10_12_3 (from Chap10) -/
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/- Lemma 10.12.3 (1): the bilinear map `(x, y) ↦ y ⊗ x` induces the canonical tensor-product
symmetry isomorphism `M ⊗[R] N ≃ₗ[R] N ⊗[R] M`, namely `TensorProduct.comm`. -/
recall TensorProduct.comm

variable {P : Type x} [AddCommMonoid P] [Module R P]

/- Lemma 10.12.3 (2): the bilinear map `((x, y), z) ↦ (x ⊗ z, y ⊗ z)` induces the canonical
distribution isomorphism from the binary direct sum tensor product to the product of tensor
products. In Lean, the binary direct sum of `R`-modules is canonically modeled by the product
module `M × N`, and the corresponding equivalence is the specialization of `prodLeft` to
`S = R`. -/
recall TensorProduct.prodLeft

end

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 10.12.3 (3): the bilinear map `(r, x) ↦ r • x` induces the canonical left-unit
isomorphism `R ⊗[R] M ≃ₗ[R] M`, namely `TensorProduct.lid`. -/
recall TensorProduct.lid

end

/-! ### Lemma_10_12_4 (from Chap10) -/
open scoped TensorProduct
open PiTensorProduct

universe u v w

variable {n : ℕ} {R : Type u} [CommSemiring R]
variable {M : Fin n → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/- Lemma 10.12.4 is a `bridge/view` item. The `core/canonical` owner abstraction is the
multilinear tensor-product equivalence `PiTensorProduct.lift`; the source-facing existence and
uniqueness statement is derived from this owner together with the primitive canonical multilinear
map `PiTensorProduct.tprod R`. -/
recall PiTensorProduct.lift

/-- Companion formulation of Lemma 10.12.4: every multilinear map out of `M` factors uniquely
through the canonical multilinear map `PiTensorProduct.tprod R`. -/
theorem piTensorProduct_existsUnique_lift
    {P : Type w} [AddCommMonoid P] [Module R P] (f : MultilinearMap R M P) :
    ∃! f' : (⨂[R] i, M i) →ₗ[R] P,
      f'.compMultilinearMap (tprod R) = f := by
  refine ⟨lift f, ?_, ?_⟩
  · simpa using (lift_symm (lift f)).symm
  · intro f' hf'
    exact lift.unique' hf'

/-! ### Lemma_10_12_5 (from Chap10) -/
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Domain triage: this item lies in the linear algebra of threefold tensor products.
The `core/canonical` owner abstraction is the associator `TensorProduct.assoc R M N P`.
The `PiTensorProduct` declarations `tmulEquivDep` and `subsingletonEquiv` from Lemma `10.12.4`
provide one realization of the same comparison, but in this file they belong only to the
`bridge/view` layer and should not appear as a parallel public owner API. -/
recall TensorProduct.assoc

/- Lemma 10.12.5 on pure tensors: the canonical associator sends
`((m ⊗[R] n) ⊗[R] p)` to `m ⊗[R] (n ⊗[R] p)`. -/
recall TensorProduct.assoc_tmul

end

/-! ### Definition_10_12_6 (from Chap10) -/
universe u v w

variable {A : Type u} {B : Type v} {N : Type w}
variable [Ring A] [Ring B] [AddCommGroup N]
variable [Module A N] [Module B N]

/- Definition 10.12.6: an `(A, B)`-bimodule is an abelian group `N` equipped with an `A`-module
structure and a `B`-module structure whose scalar actions commute. The canonical Lean expression
of this compatibility is `SMulCommClass A B N`. -/
recall SMulCommClass

/-! ### Lemma_10_12_7 (from Chap10) -/
open scoped TensorProduct
open TensorProduct

universe u v w x y

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N] [Module B N] [SMulCommClass A B N]
variable {P : Type y} [AddCommGroup P] [Module B P]

/- Lemma 10.12.7 is `source-facing`: it records the induced scalar actions on
`M ⊗[A] N` and `N ⊗[B] P`, together with the canonical reassociation
`((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P)`. The sampled owner abstractions in this domain are
`TensorProduct.leftModule`, `TensorProduct.smulCommClass_left`, `TensorProduct.assoc`, and
`TensorProduct.AlgebraTensorModule.assoc`. Mathlib does not currently expose this exact mixed-base
associator as a single owner declaration, so the file should export only the source-facing bridge
and keep the transported tensor-product instances internal. -/

private noncomputable instance : Module B (M ⊗[A] N) :=
  AddEquiv.module B (TensorProduct.comm A M N).toAddEquiv

@[simp] private theorem leftTensorRight_smul_tmul (b : B) (m : M) (n : N) :
    b • (m ⊗ₜ[A] n : M ⊗[A] N) = m ⊗ₜ[A] (b • n) := by
  apply (TensorProduct.comm A M N).injective
  rfl

private instance : SMulCommClass A B (M ⊗[A] N) where
  smul_comm a b x := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro m n
      rw [leftTensorRight_smul_tmul, smul_tmul']
      change (a • m) ⊗ₜ[A] (b • n) = b • ((a • m) ⊗ₜ[A] n)
      rw [leftTensorRight_smul_tmul]
    · intro x y hx hy
      simp [hx, hy, smul_add]

private instance : SMulCommClass B A (M ⊗[A] N) :=
  SMulCommClass.symm A B (M ⊗[A] N)

private instance : Module A (N ⊗[B] P) := by
  letI : SMulCommClass B A N := SMulCommClass.symm A B N
  infer_instance

@[simp] private theorem rightTensorLeft_smul_tmul (a : A) (n : N) (p : P) :
    a • (n ⊗ₜ[B] p : N ⊗[B] P) = (a • n) ⊗ₜ[B] p := by
  letI : SMulCommClass B A N := SMulCommClass.symm A B N
  simpa using (smul_tmul' a n p : a • (n ⊗ₜ[B] p : N ⊗[B] P) = (a • n) ⊗ₜ[B] p)

private noncomputable def assocCurry :
    M ⊗[A] N →+ P →+ M ⊗[A] (N ⊗[B] P) :=
  liftAddHom
    { toFun := fun m ↦
        { toFun := fun n ↦
            { toFun := fun p ↦ m ⊗ₜ[A] (n ⊗ₜ[B] p)
              map_zero' := by simp
              map_add' := by
                intro p q
                simp [tmul_add] }
          map_zero' := by
            ext p
            simp
          map_add' := by
            intro n n'
            ext p
            simp [add_tmul, tmul_add] }
      map_zero' := by
        ext n p
        simp
      map_add' := by
        intro m m'
        ext n p
        simp [add_tmul] }
    (fun a m n ↦ by
      ext p
      simp [smul_tmul, rightTensorLeft_smul_tmul])

@[simp]
private theorem assocCurry_tmul (m : M) (n : N) (p : P) :
    assocCurry (m ⊗ₜ[A] n) p = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

private noncomputable def assocHom :
    ((M ⊗[A] N) ⊗[B] P) →+ M ⊗[A] (N ⊗[B] P) :=
  liftAddHom assocCurry
    (fun b x p ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro m n
        change m ⊗ₜ[A] ((b • n) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] (b • p))
        congr 1
        exact smul_tmul b n p
      · intro x y hx hy
        simp [hx, hy])

@[simp]
private theorem assocHom_tmul (m : M) (n : N) (p : P) :
    assocHom ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

private theorem assocHom_map_smul (a : A) (x : ((M ⊗[A] N) ⊗[B] P)) :
    assocHom (a • x) = a • assocHom x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro y p
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro m n
      simp [assocHom_tmul]
    · intro y z hy hz
      have hy' : assocHom ((a • y) ⊗ₜ[B] p) = a • assocHom (y ⊗ₜ[B] p) := by
        simpa [smul_tmul'] using hy
      have hz' : assocHom ((a • z) ⊗ₜ[B] p) = a • assocHom (z ⊗ₜ[B] p) := by
        simpa [smul_tmul'] using hz
      rw [smul_tmul', smul_add, add_tmul, AddMonoidHom.map_add, hy', hz']
      rw [add_tmul, AddMonoidHom.map_add, smul_add]
  · intro x y hx hy
    rw [smul_add, AddMonoidHom.map_add, hx, hy, AddMonoidHom.map_add, smul_add]

private noncomputable def assocLinearMap :
    ((M ⊗[A] N) ⊗[B] P) →ₗ[A] M ⊗[A] (N ⊗[B] P) where
  toFun := assocHom
  map_add' := assocHom.map_add
  map_smul' := assocHom_map_smul

private noncomputable def assocInvCurry :
    M →+ (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
  { toFun := fun m ↦
      liftAddHom
        { toFun := fun n ↦
            { toFun := fun p ↦ (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p
              map_zero' := by simp
              map_add' := by
                intro p q
                simp [tmul_add] }
          map_zero' := by
            ext p
            simp
          map_add' := by
            intro n n'
            ext p
            simp [tmul_add, add_tmul] }
        (fun b n p ↦ by
          change ((m ⊗ₜ[A] (b • n) : M ⊗[A] N) ⊗ₜ[B] p) =
              ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] (b • p))
          rw [← leftTensorRight_smul_tmul, smul_tmul])
    map_zero' := by
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        simp
      · intro x y hx hy
        rw [AddMonoidHom.map_add, hx, hy]
        simp
    map_add' := by
      intro m m'
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        simp [add_tmul]
      · intro x y hx hy
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy] }

@[simp]
private theorem assocInvCurry_tmul (m : M) (n : N) (p : P) :
    assocInvCurry m (n ⊗ₜ[B] p) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) :=
  rfl

private noncomputable def assocInvHom :
    M ⊗[A] (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
  liftAddHom assocInvCurry
    (fun a m x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        rw [rightTensorLeft_smul_tmul, assocInvCurry_tmul, assocInvCurry_tmul]
        rw [smul_tmul]
      · intro x y hx hy
        simp [hx, hy])

@[simp]
private theorem assocInvHom_tmul (m : M) (n : N) (p : P) :
    assocInvHom (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) := by
  change assocInvCurry m (n ⊗ₜ[B] p) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p)
  rw [assocInvCurry_tmul]

private theorem assocInvHom_map_smul (a : A) (x : M ⊗[A] (N ⊗[B] P)) :
    assocInvHom (a • x) = a • assocInvHom x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro n p
      simp [assocInvHom_tmul]
    · intro y z hy hz
      rw [tmul_add, smul_add, AddMonoidHom.map_add, hy, hz, AddMonoidHom.map_add, smul_add]
  · intro x y hx hy
    rw [smul_add, AddMonoidHom.map_add, hx, hy, AddMonoidHom.map_add, smul_add]

private noncomputable def assocInvLinearMap :
    M ⊗[A] (N ⊗[B] P) →ₗ[A] ((M ⊗[A] N) ⊗[B] P) where
  toFun := assocInvHom
  map_add' := assocInvHom.map_add
  map_smul' := assocInvHom_map_smul

/-- Lemma 10.12.7: tensoring an `(A, B)`-bimodule on the left by an `A`-module and on the right by
a `B`-module is associative up to a canonical `A`-linear equivalence. -/
noncomputable def tensorBimoduleAssoc :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P) where
  toLinearMap := assocLinearMap
  invFun := assocInvLinearMap
  left_inv x := by
    change assocInvHom (assocHom x) = x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro y p
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro m n
        simp
      · intro y z hy hz
        rw [add_tmul, AddMonoidHom.map_add, AddMonoidHom.map_add, hy, hz]
    · intro x y hx hy
      rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy]
  right_inv x := by
    change assocHom (assocInvHom x) = x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro m y
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro n p
        simp
      · intro y z hy hz
        rw [tmul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, hy, hz]
    · intro x y hx hy
      rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy]

@[simp]
theorem tensorBimoduleAssoc_tmul (m : M) (n : N) (p : P) :
    tensorBimoduleAssoc ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

@[simp]
theorem tensorBimoduleAssoc_symm_tmul (m : M) (n : N) (p : P) :
    tensorBimoduleAssoc.symm (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) :=
  assocInvHom_tmul m n p

end

/-! ### Lemma_10_12_8 (from Chap10) -/
open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Lemma 10.12.8 is `source-facing` but recall-shaped: the owner abstraction is the canonical
linear equivalence `TensorProduct.lift.equiv`, and the textbook bijection
`Hom_R(M ⊗[R] N, P) ≃ Hom_R(M, Hom_R(N, P))` is its specialization along `RingHom.id R` followed by
inversion. -/
#check
  ((TensorProduct.lift.equiv (.id R) M N P).symm :
    (M ⊗[R] N →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] N →ₗ[R] P))

/- Companion check: the forward map of this inverse specialization is the canonical curried map
`TensorProduct.curry`, sending `f : M ⊗[R] N →ₗ[R] P` to `m ↦ fun n ↦ f (m ⊗ₜ n)`. -/
#check (TensorProduct.curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P)

/-! ### Lemma_10_12_9_Tensor_products_commute_with_colimits (from Chap10) -/
open CategoryTheory Limits MonoidalCategory

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I]
variable (N : ModuleCat.{u} R) (F : I ⥤ ModuleCat.{u} R) [HasColimit F]

/-- Lemma 10.12.9 (Tensor products commute with colimits): for a system of `R`-modules indexed by
a preordered set, the colimit of the tensor products `Mᵢ ⊗ N` is canonically isomorphic to the
tensor product of the colimit of the system with `N`. -/
noncomputable def colimit_tensor_right_iso : colimit (F ⋙ tensorRight N) ≅ (colimit F) ⊗ N :=
  (preservesColimitIso (tensorRight N) F).symm

/-- On each cocone leg, the comparison isomorphism from the colimit of `Mᵢ ⊗ N` to
`(colimit Mᵢ) ⊗ N` is induced by tensoring the colimit map `μᵢ` with the identity on `N`. -/
-- Proof sketch: specialize `ι_preservesColimitIso_inv` to the right-tensoring functor
-- `tensorRight N`; this is exactly the cocone-leg formula for the inverse of
-- `preservesColimitIso`, which is the `hom` of `colimit_tensor_right_iso`.
theorem colimit_tensor_right_iso_hom_ι (i : I) :
    colimit.ι (F ⋙ tensorRight N) i ≫ (colimit_tensor_right_iso N F).hom =
      colimit.ι F i ▷ N := by
  -- The comparison map is the inverse leg of `preservesColimitIso` for `tensorRight N`.
  -- The standard cocone-leg formula then gives exactly the induced map `μᵢ ⊗ 1`.
  simpa [colimit_tensor_right_iso] using
    (CategoryTheory.ι_preservesColimitIso_inv (G := tensorRight N) (F := F) i)

end

/-! ### Lemma_10_12_10 (from Chap10) -/
/- Lemma 10.12.10: tensoring a right exact sequence of `R`-modules with a fixed module `N`
preserves exactness. The canonical owner declarations are `rTensor_exact` for the exact pair and
`LinearMap.rTensor_surjective` for the terminal surjection. -/
recall rTensor_exact
recall LinearMap.rTensor_surjective

/-! ### Remark_10_12_11 (from Chap10) -/
/- Domain-style sampling:
- primary domain: exactness of linear maps under tensor product in commutative algebra;
- sampled owner declarations of the same kind:
  `LinearMap.exact_zero_iff_injective`,
  `Module.Flat.rTensor_exact`,
  `Module.Flat.iff_rTensor_exact`;
- layer:
  `source-facing`: the present counterexample is the explicit sequence `0 ⟶ ℤ ⟶ ℤ`;
  `core/canonical`: preservation of exact sequences under right tensoring is owned by
  `Module.Flat`;
  `bridge/view`: exactness of `0 ⟶ M ⟶ N` is canonically equivalent to injectivity of the second
  map via `LinearMap.exact_zero_iff_injective`;
- primitive data vs. derived API:
  primitive data: the explicit map `((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ)` and the tensor factor
  `ZMod 2`, provided by `Example_10_12_12`;
  derived API: exactness of the original sequence and failure of exactness after tensoring, both
  transported through the bridge theorem above. -/

/-- Remark 10.12.11: tensoring with an arbitrary module does not preserve exactness in general; the
exact sequence `0 ⟶ ℤ \xrightarrow{2} ℤ` becomes nonexact after tensoring with `ℤ/2ℤ`. -/
theorem tensorProduct_not_preserve_exact_sequence :
    Function.Exact (0 : Unit →ₗ[ℤ] ℤ) ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ∧
      ¬ Function.Exact ((0 : Unit →ₗ[ℤ] ℤ).rTensor (ZMod 2))
        (((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).rTensor (ZMod 2)) := by
  simpa [LinearMap.exact_zero_iff_injective] using
    tensoring_zmodTwo_does_not_preserve_injectivity

/-! ### Example_10_12_12 (from Chap10) -/
open scoped TensorProduct
open TensorProduct

private abbrev twoZLinearMap : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

private theorem intTensor_zmodTwo_one_ne_zero :
    (TensorProduct.lid ℤ (ZMod 2)).symm 1 ≠ 0 := by
  intro h
  exact (show (1 : ZMod 2) ≠ 0 by decide)
    (by simpa using congrArg (TensorProduct.lid ℤ (ZMod 2)) h)

private theorem two_zsmul_rTensor_zmodTwo_not_injective :
    ¬ Function.Injective (twoZLinearMap.rTensor (ZMod 2)) := by
  let f : ℤ ⊗[ℤ] ZMod 2 →ₗ[ℤ] ℤ ⊗[ℤ] ZMod 2 := twoZLinearMap.rTensor (ZMod 2)
  let z : ℤ ⊗[ℤ] ZMod 2 := (TensorProduct.lid ℤ (ZMod 2)).symm 1
  intro h
  apply intTensor_zmodTwo_one_ne_zero
  apply h
  calc
    f z = 0 := by
      apply (TensorProduct.lid ℤ (ZMod 2)).injective
      change (2 : ZMod 2) = 0
      decide
    _ = f 0 := by
      simp [f]

/-- Example 10.12.12: for the injective map `2 : ℤ → ℤ` of `ℤ`-modules, tensoring with `ZMod 2`
does not preserve injectivity. -/
theorem tensoring_zmodTwo_does_not_preserve_injectivity :
    Function.Injective ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
      ¬ Function.Injective (((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod 2)) := by
  refine ⟨?_, by simpa [twoZLinearMap] using two_zsmul_rTensor_zmodTwo_not_injective⟩
  simpa [twoZLinearMap] using smul_right_injective ℤ (show (2 : ℤ) ≠ 0 by decide)

/-- Bridge to the owner abstraction: `ZMod 2` is not flat as a `ℤ`-module because right tensoring
fails to preserve injectivity for multiplication by `2`. -/
theorem zmodTwo_not_flat : ¬ Module.Flat ℤ (ZMod 2) := by
  intro hflat
  letI := hflat
  exact two_zsmul_rTensor_zmodTwo_not_injective <|
    Module.Flat.rTensor_preserves_injective_linearMap twoZLinearMap <|
      by simpa [twoZLinearMap] using smul_right_injective ℤ (show (2 : ℤ) ≠ 0 by decide)

/-! ### Remark_10_12_13 (from Chap10) -/
section

variable {R : Type*} [CommRing R]
variable {N : Type*} [AddCommGroup N] [Module R N]

/- Remark 10.12.13: an `R`-module `N` for which tensoring on the right preserves exact
sequences is called a flat `R`-module; the canonical predicate for this notion is
`Module.Flat R N`. -/
recall Module.Flat

/- Companion recall: over a commutative ring, flatness is equivalent to exactness of tensoring on
the right by `N`; this is exactly the canonical theorem `Module.Flat.iff_rTensor_exact`. -/
recall Module.Flat.iff_rTensor_exact

end

/-! ### Lemma_10_12_14 (from Chap10) -/
universe u v w

open scoped TensorProduct
open TensorProduct

section

variable (R : Type u) (M : Type v) (N : Type w)
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/- The finite tensor-product part of this item is the canonical mathlib instance. -/
recall Module.Finite.tensorProduct

namespace Module.FinitePresentation

/-- Helper for Lemma 10.12.14: tensoring a finitely presented module with a finite free module
stays finitely presented. -/
private lemma tensorProduct_finite_free (n : ℕ) [Module.FinitePresentation R N] :
    Module.FinitePresentation R (N ⊗[R] (Fin n → R)) := by
  -- Identify the tensor product with the finite product `Fin n → N`.
  exact Module.FinitePresentation.of_equiv
    (TensorProduct.piScalarRight R R N (Fin n)).symm

/-- Lemma 10.12.14: if `M` and `N` are finitely presented `R`-modules, then the tensor
product `M ⊗[R] N` is finitely presented over `R`. -/
instance tensorProduct [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] : Module.FinitePresentation R (M ⊗[R] N) := by
  -- Follow the source proof through `N ⊗[R] M`, then commute the tensor factors at the end.
  have hNM : Module.FinitePresentation R (N ⊗[R] M) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    -- Tensor the finite free presentation source; this remains finitely presented.
    letI : Module.FinitePresentation R (N ⊗[R] (Fin n → R)) :=
      tensorProduct_finite_free (R := R) (N := N) n
    have hker_finite : Module.Finite R (LinearMap.ker f) := by
      -- The kernel of a presentation of a finitely presented module is finitely generated.
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
    have hker_fg : (LinearMap.ker (LinearMap.lTensor N f)).FG := by
      letI : Module.Finite R (LinearMap.ker f) := hker_finite
      -- Right exactness identifies the new kernel with the range of the tensored subtype map.
      have hExact : Function.Exact ((LinearMap.ker f).subtype) f :=
        LinearMap.exact_subtype_ker_map f
      have hTensorExact : Function.Exact
          (LinearMap.lTensor N (LinearMap.ker f).subtype)
          (LinearMap.lTensor N f) :=
        lTensor_exact N hExact hf
      rw [LinearMap.exact_iff] at hTensorExact
      exact hTensorExact.symm ▸ Submodule.fg_range (LinearMap.lTensor N (LinearMap.ker f).subtype)
    -- The tensor product is a quotient of the finitely presented source by a finitely generated
    -- kernel, so it is finitely presented.
    exact Module.finitePresentation_of_surjective (LinearMap.lTensor N f)
      (LinearMap.lTensor_surjective N hf) hker_fg
  -- Commute the tensor factors to recover the textbook order.
  exact Module.FinitePresentation.of_equiv (TensorProduct.comm R N M)

end Module.FinitePresentation

end

/-! ### Lemma_10_12_15 (from Chap10) -/
universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommSemiring R]
variable {S : Submonoid R}
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 10.12.15 is a `bridge/view` item in the localization/base-change domain. The primitive
owner abstraction is `IsLocalizedModule.isBaseChange`, and the canonical derived comparison is
`LocalizedModule.equivTensorProduct`. The Stacks statement uses its symmetric orientation. -/

/- Lemma 10.12.15: the localized module `S⁻¹M` is canonically isomorphic to
`S⁻¹R ⊗[R] M`. This is the symmetric orientation of the owner equivalence
`LocalizedModule.equivTensorProduct`. -/
#check (LocalizedModule.equivTensorProduct S M).symm

/- The symmetric form of the canonical isomorphism sends `(a / s) ⊗ m` to `a • (m / s)`. -/
recall LocalizedModule.equivTensorProduct_symm_apply_tmul

end

/-! ### Lemma_10_12_16 (from Chap10) -/
open scoped TensorProduct
open LocalizedModule

universe u v w

noncomputable section

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/- Lemma 10.12.16 is a `bridge/view` item. Its owner abstractions are
`IsLocalizedModule.linearEquiv`, applied to the canonical localization map on tensor products, and
`IsLocalization.moduleTensorEquiv`, which identifies tensoring over `Localization S` with tensoring
over `R` for localized modules. The source-facing equivalence below is their canonical composite. -/
/-- Lemma 10.12.16: localizing a tensor product is canonically equivalent to the tensor product of
the localized modules over `Localization S`. -/
def localizedTensorProductLinearEquiv :
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N ≃ₗ[Localization S]
      LocalizedModule S (M ⊗[R] N) :=
  let tensorMap := TensorProduct.map (mkLinearMap S M) (mkLinearMap S N)
  IsLocalization.moduleTensorEquiv S (Localization S) (LocalizedModule S M) (LocalizedModule S N) ≪≫ₗ
    (IsLocalizedModule.linearEquiv S tensorMap
      (mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization S (Localization S)

/-- The canonical localization-tensor equivalence sends a simple tensor of localized elements to
the localization of the corresponding tensor with multiplied denominator. -/
theorem localizedTensorProductLinearEquiv_apply_mk_tmul_mk
    (m : M) (n : N) (s t : S) :
    localizedTensorProductLinearEquiv S
      (mk m s ⊗ₜ[Localization S] mk n t) =
        mk (m ⊗ₜ[R] n) (s * t) := by
  let tensorMap := TensorProduct.map (mkLinearMap S M) (mkLinearMap S N)
  rw [show mk m s = Localization.mk (1 : R) s • mk m (1 : S) by
    simpa using (mk_smul_mk (1 : R) m s (1 : S)).symm]
  rw [show mk n t = Localization.mk (1 : R) t • mk n (1 : S) by
    simpa using (mk_smul_mk (1 : R) n t (1 : S)).symm]
  rw [TensorProduct.smul_tmul_smul, map_smul]
  change (Localization.mk (1 : R) s * Localization.mk (1 : R) t) •
      localizedTensorProductLinearEquiv S (mk m (1 : S) ⊗ₜ[Localization S] mk n (1 : S)) = _
  have hbase :
      localizedTensorProductLinearEquiv S (mk m (1 : S) ⊗ₜ[Localization S] mk n (1 : S)) =
        mk (m ⊗ₜ[R] n) (1 : S) := by
    change (IsLocalizedModule.linearEquiv S tensorMap (mkLinearMap S (M ⊗[R] N)))
        (mk m (1 : S) ⊗ₜ[R] mk n (1 : S)) = _
    simpa [localizedTensorProductLinearEquiv, tensorMap] using
      IsLocalizedModule.linearEquiv_apply S tensorMap
        (mkLinearMap S (M ⊗[R] N)) (m ⊗ₜ[R] n)
  rw [hbase]
  have hmul :
      Localization.mk (1 : R) s * Localization.mk (1 : R) t = Localization.mk (1 : R) (s * t) := by
    simp [Localization.mk_mul]
  rw [hmul]
  simpa using (mk_smul_mk (1 : R) (m ⊗ₜ[R] n) (s * t) (1 : S))

end
