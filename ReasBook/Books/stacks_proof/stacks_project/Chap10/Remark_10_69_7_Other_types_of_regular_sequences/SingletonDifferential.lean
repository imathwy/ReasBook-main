import stacks_proof.stacks_project.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.SingletonTensorTerms
import stacks_proof.stacks_project.Chap15.Lemma_15_30_2

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after postcomposing the
surviving `(1,0)` `D₁` contribution of the singleton tensor differential with the degree-zero
collapse map, only the mapped base Koszul differential remains. -/
-- TODO: re-express the repaired `d₁` summand using the current `HomologicalComplex.mapBifunctor`
-- API, then finish by the surviving `(n, 0)` collapse computation.
theorem singleton_tensor_degree_one_D1_postcompose_normalize {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    HomologicalComplex.mapBifunctor.d₁ K S (curriedTensor (ModuleCat A))
        (ComplexShape.down ℕ) 1 0 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)) := by
  dsimp
  -- Proof comment: expand the raw `d₁` summand in the total tensor differential.
  rw [HomologicalComplex.mapBifunctor.d₁_eq
    (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
    (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
    (i₁' := 0) (h := by simp) (i₂ := 0) (j := 0) (h' := by simp)]
  -- Proof comment: in chain complexes the surviving sign is `+1`, and the collapse map sends
  -- the `(0,0)` summand identically to the termwise tensor object.
  let f :
      ((curriedTensor (ModuleCat A)).obj
          ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X 1)).obj
        (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)).X 0) ⟶
      ((curriedTensor (ModuleCat A)).obj
          ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X 0)).obj
        (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)).X 0) :=
    (((curriedTensor (ModuleCat A)).map
      ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)).app
      (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)).X 0))
  change ((ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (1, 0) •
      (f ≫ HomologicalComplex.ιMapBifunctor
        (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
        (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 0 0 0 (by simp))) ≫
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
    (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
      ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0))
  dsimp [ComplexShape.ε₁]
  let ι :=
    HomologicalComplex.ιMapBifunctor
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
      (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 0 0 0 (by simp)
  have hsmul :
      ((1 : ℤˣ) • (f ≫ ι)) ≫
          (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
        (1 : ℤˣ) •
          ((f ≫ ι) ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom) := by
    simpa [ι] using
      (Linear.units_smul_comp (r := (1 : ℤˣ)) (f := f ≫ ι)
        (g := (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom))
  change ((1 : ℤˣ) • (f ≫ ι)) ≫
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
    (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
      ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0))
  rw [hsmul, one_smul]
  simpa [f, HomologicalComplex.tensorObj, HomologicalComplex.ιTensorObj,
    ChainComplex.single₀_obj_zero] using
    congrArg
      (fun f =>
        (((curriedTensor (ModuleCat A)).map
            ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)).app
            (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)).X 0)) ≫
          f)
      (koszul_singleton_tensor_X_iso_tensorRight_hom_comp_ι
        (A := A) (M := M) (r := r) 0)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after postcomposing the
surviving `(1,0)` `D₁` contribution of the singleton tensor differential with the degree-zero
collapse map, only the mapped base Koszul differential remains. -/
-- TODO: update the precomposition-with-`D₁` rewrite to the current `ι_D₁_assoc` shape, then
-- reduce to `singleton_tensor_degree_one_D1_postcompose_normalize`.
theorem singleton_tensor_degree_one_D1_component_eq_mapped_base_d {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₁ K S (curriedTensor (ModuleCat A))
          (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)) := by
  dsimp
  -- Proof comment: unfold `ιTensorObj` back to `ιMapBifunctor`, then apply the reassociated
  -- `ι_D₁` rewrite and finish with the raw normalization lemma.
  simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
    (show
      HomologicalComplex.ιMapBifunctor
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
          (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₁
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
          (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)) from by
        rw [HomologicalComplex.mapBifunctor.ι_D₁_assoc
          (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
          (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
          (j := 1) (j' := 0) (i₁ := 1) (i₂ := 0) (h := by simp)]
        simpa using
          singleton_tensor_degree_one_D1_postcompose_normalize
            (A := A) (M := M) (r := r))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after postcomposing the
singleton tensor differential with the degree-zero collapse map, the `(1,0)` `D₂` contribution
vanishes. -/
theorem singleton_tensor_degree_one_D2_component_eq_zero {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₂ K S (curriedTensor (ModuleCat A))
          (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
      0 := by
  dsimp
  -- Proof comment: first replace the precomposition with `D₂` by the corresponding `d₂` term.
  calc
    HomologicalComplex.ιTensorObj (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)) 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₂
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
          (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
      =
        HomologicalComplex.mapBifunctor.d₂
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
          (curriedTensor (ModuleCat A)) (ComplexShape.down ℕ) 1 0 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
            simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
              congrArg
                (fun f =>
                  f ≫
                    (koszul_singleton_tensor_X_iso_tensorRight
                      (A := A) (M := M) (r := r) 0).hom)
                (HomologicalComplex.mapBifunctor.ι_D₂
                  (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
                  (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
                  (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
                  (j := 1) (j' := 0) (i₁ := 1) (i₂ := 0) (h := by simp))
    _ = 0 := by
        by_cases hrel : (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0)
        · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero'
            (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
            (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
            (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
            (i₁ := 1) (h := hrel) (j := 0) (h' := by simp)]
          rw [zero_comp]
        · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero
            (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
            (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
            (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
            (i₁ := 1) (i₂ := 0) (j := 0) hrel]
          rw [zero_comp]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the degreewise tensor-collapse
isomorphisms for the singleton coefficient complex intertwine the degree-`1 → 0` differential with
the mapped base Koszul differential. -/
-- TODO: rewrite the transported degree-`1` differential using the current `d_comp_XIsoOfEq_hom`
-- statement, then combine the repaired `D₁` and `D₂` component formulas.
theorem singleton_tensor_degree_one_surviving_summand_transport {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    let T := HomologicalComplex.tensorObj K S
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        T.d 1 ((ComplexShape.down ℕ).next 1) ≫
        (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom =
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)) := by
  dsimp
  -- Proof comment: first transport the degree-`1 → next 1` differential to degree `0`, then
  -- split the tensor differential into its `D₁` and `D₂` pieces.
  calc
    HomologicalComplex.ιTensorObj
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)) 1 0 1 (by simp) ≫
        (HomologicalComplex.tensorObj
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).d 1
          ((ComplexShape.down ℕ).next 1) ≫
        ((HomologicalComplex.tensorObj
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).XIsoOfEq
          (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
      =
        HomologicalComplex.ιTensorObj
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)) 1 0 1 (by simp) ≫
        (HomologicalComplex.tensorObj
          (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).d 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f =>
                  HomologicalComplex.ιTensorObj
                      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
                      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)) 1 0 1
                      (by simp) ≫
                    f ≫
                      (koszul_singleton_tensor_X_iso_tensorRight
                        (A := A) (M := M) (r := r) 0).hom)
                (HomologicalComplex.d_comp_XIsoOfEq_hom
                  (HomologicalComplex.tensorObj
                    (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
                    ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)))
                  (by simp : (ComplexShape.down ℕ).next 1 = 0) 1)
    _ = ((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
          ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0) := by
            rw [singleton_tensor_degree_one_postcompose_split (A := A) (M := M) (r := r)]
            rw [singleton_tensor_degree_one_D1_component_eq_mapped_base_d
              (A := A) (M := M) (r := r)]
            rw [singleton_tensor_degree_one_D2_component_eq_zero
              (A := A) (M := M) (r := r)]
            simpa using add_zero
              ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
                ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the degreewise tensor-collapse
isomorphisms for the singleton coefficient complex intertwine the degree-`1 → 0` differential with
the mapped base Koszul differential. -/
theorem koszul_singleton_tensor_collapse_commutes_with_differential {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let T := HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
          ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0))
      =
        T.d 1 ((ComplexShape.down ℕ).next 1) ≫
          (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
          (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
  dsimp
  let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
  let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
  let T := HomologicalComplex.tensorObj K S
  -- Route correction: the old componentwise extensionality API has been replaced by
  -- `CategoryTheory.GradedObject.tensorObj_ext`, so we now check the two degree-`1` summands
  -- `(1, 0)` and `(0, 1)` separately.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hj : j = 1 := by omega
    subst hj
    -- Proof comment: the `(0, 1)` summand is killed by the collapse map on the left-hand side.
    have hleft_zero :
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)) = 0 := by
      simpa using
        congrArg
          (fun f =>
            f ≫ (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)))
          (koszul_singleton_tensor_X_iso_tensorRight_hom_comp_ι_zero_right
            (A := A) (M := M) (r := r))
    -- Proof comment: on the right-hand side, both `D₁` and `D₂` vanish on the `(0, 1)` summand.
    have hD1_zero :
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            HomologicalComplex.mapBifunctor.D₁ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom = 0 := by
      calc
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            HomologicalComplex.mapBifunctor.D₁ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
          =
            HomologicalComplex.mapBifunctor.d₁ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 0 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
              simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
                congrArg
                  (fun f =>
                    f ≫
                      (koszul_singleton_tensor_X_iso_tensorRight
                        (A := A) (M := M) (r := r) 0).hom)
                  (HomologicalComplex.mapBifunctor.ι_D₁
                    (K₁ := K) (K₂ := S) (F := curriedTensor (ModuleCat A))
                    (c := ComplexShape.down ℕ) (j := 1) (j' := 0)
                    (i₁ := 0) (i₂ := 1) (h := by simp))
        _ = 0 := by
            have hrel : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
              simp
            rw [HomologicalComplex.mapBifunctor.d₁_eq_zero
              (K₁ := K) (K₂ := S) (F := curriedTensor (ModuleCat A))
              (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (j := 0) hrel]
            exact zero_comp
    have hD2_zero :
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            HomologicalComplex.mapBifunctor.D₂ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom = 0 := by
      calc
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            HomologicalComplex.mapBifunctor.D₂ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
          =
            HomologicalComplex.mapBifunctor.d₂ K S (curriedTensor (ModuleCat A))
              (ComplexShape.down ℕ) 0 1 0 ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
              simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
                congrArg
                  (fun f =>
                    f ≫
                      (koszul_singleton_tensor_X_iso_tensorRight
                        (A := A) (M := M) (r := r) 0).hom)
                  (HomologicalComplex.mapBifunctor.ι_D₂
                    (K₁ := K) (K₂ := S) (F := curriedTensor (ModuleCat A))
                    (c := ComplexShape.down ℕ) (j := 1) (j' := 0)
                    (i₁ := 0) (i₂ := 1) (h := by simp))
        _ = 0 := by
            rw [HomologicalComplex.mapBifunctor.d₂_eq
              (K₁ := K) (K₂ := S) (F := curriedTensor (ModuleCat A))
              (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (i₂' := 0)
              (h := by simp) (j := 0) (h' := by simp)]
            have hsingle : S.d 1 0 = 0 := by
              simpa [S] using
                (HomologicalComplex.single_obj_d 0 (ModuleCat.of A M) 1 0)
            rw [hsingle, Functor.map_zero, zero_comp, smul_zero, zero_comp]
    have hright_zero :
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            T.d 1 ((ComplexShape.down ℕ).next 1) ≫
            (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom = 0 := by
      calc
        HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
            T.d 1 ((ComplexShape.down ℕ).next 1) ≫
            (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
          =
            HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
              T.d 1 0 ≫
              (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
                simp [Category.assoc]
        _ =
            HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
              HomologicalComplex.mapBifunctor.D₁ K S (curriedTensor (ModuleCat A))
                (ComplexShape.down ℕ) 1 0 ≫
              (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
            +
            HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
              HomologicalComplex.mapBifunctor.D₂ K S (curriedTensor (ModuleCat A))
                (ComplexShape.down ℕ) 1 0 ≫
              (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
                simpa [T, Category.assoc, Preadditive.comp_add] using
                  congrArg
                    (fun f =>
                      HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
                        f ≫
                        (koszul_singleton_tensor_X_iso_tensorRight
                          (A := A) (M := M) (r := r) 0).hom)
                    (HomologicalComplex.mapBifunctor.d_eq
                      (K₁ := K) (K₂ := S) (F := curriedTensor (ModuleCat A))
                      (c := ComplexShape.down ℕ) 1 0)
        _ = 0 := by
            rw [hD1_zero, hD2_zero]
            exact add_zero (0 : _)
    exact hleft_zero.trans hright_zero.symm
  · have hi1 : i = 1 := by omega
    subst hi1
    have hj0 : j = 0 := by omega
    subst hj0
    -- Proof comment: the `(1, 0)` summand is exactly the surviving source piece.
    have hleft_survive :
        HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)) =
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)) := by
      simpa using
        congrArg
          (fun f =>
            f ≫ (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)))
          (koszul_singleton_tensor_X_iso_tensorRight_hom_comp_ι
            (A := A) (M := M) (r := r) 1)
    exact hleft_survive.trans <|
      by
        simpa [K, S, T] using
          (singleton_tensor_degree_one_surviving_summand_transport
            (A := A) (M := M) (r := r)).symm

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after the degree-`1` and
degree-`0` identifications and the left unitor, the mapped singleton base differential becomes
the first map in `ModuleCat.smulShortComplex`. -/
theorem singleton_tensor_mapped_base_differential_eq_smul_shortComplex {A : Type u}
    [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let e₁ :
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj (K.X 1)) ≅
          ModuleCat.of A M :=
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
        ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
          fin_one_module_iso (A := A))) ≪≫
        (λ_ (ModuleCat.of A M))
    let e₀ :
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj (K.X 0)) ≅
          ModuleCat.of A M :=
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))) ≪≫
        (λ_ (ModuleCat.of A M))
    e₁.hom ≫ (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f =
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0)) ≫ e₀.hom := by
  dsimp
  have hbase :
      ((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (r • LinearMap.id) : ModuleCat.of A A ⟶ ModuleCat.of A A) =
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
              fin_one_module_iso (A := A))).inv ≫
          ((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
            ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0) ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom := by
    -- Proof comment: tensor the base-ring differential normalization and rewrite the mapped
    -- degree isomorphisms as the components of `mapIso`.
    simpa using
      congrArg (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map)
        (koszul_singleton_degree_one_differential_eq_smul_base (A := A) (r := r))
  -- Proof comment: the left unitor identifies tensoring the scalar map on `A` with scalar
  -- multiplication on `M`.
  have hunit :
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
            fin_one_module_iso (A := A))).hom ≫
          (λ_ (ModuleCat.of A M)).hom ≫
          (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
        =
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
                fin_one_module_iso (A := A))).hom ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
              (ModuleCat.ofHom (r • LinearMap.id) : ModuleCat.of A A ⟶ ModuleCat.of A A)) ≫
            (λ_ (ModuleCat.of A M)).hom := by
    simpa [ModuleCat.smulShortComplex, Category.assoc] using
      congrArg
        (fun f =>
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
              fin_one_module_iso (A := A))).hom ≫ f)
        (smul_tensor_left_unitor_naturality (A := A) (M := M) (r := r)).symm
  have hrewrite :
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
            fin_one_module_iso (A := A))).hom ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
            (ModuleCat.ofHom (r • LinearMap.id) : ModuleCat.of A A ⟶ ModuleCat.of A A)) ≫
          (λ_ (ModuleCat.of A M)).hom
        =
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map
              ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0)) ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
            (λ_ (ModuleCat.of A M)).hom := by
    rw [hbase]
    simp [Category.assoc]
  exact hunit.trans hrewrite

theorem singleton_tensor_sc1_right_square {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let T := HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    let e₁ :
        T.X 1 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
            fin_one_module_iso (A := A))) ≪≫
        (λ_ (ModuleCat.of A M))
    let e₀ :
        T.X 0 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))) ≪≫
        (λ_ (ModuleCat.of A M))
    let e₀' : (T.sc 1).X₃ ≅ ModuleCat.of A M :=
      (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)) ≪≫ e₀
    e₁.hom ≫ (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f =
      (T.sc 1).g ≫ e₀'.hom := by
  dsimp
  let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
  let T := HomologicalComplex.tensorObj K
    ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
  -- Proof comment: first normalize the mapped base differential to scalar multiplication on `M`.
  have hnormalize :
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
              fin_one_module_iso (A := A))).hom ≫
          (λ_ (ModuleCat.of A M)).hom ≫
          (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
        =
          (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
            ((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0) ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
            (λ_ (ModuleCat.of A M)).hom := by
    simpa [Category.assoc, K] using
      congrArg
        (fun f =>
          (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫ f)
        (singleton_tensor_mapped_base_differential_eq_smul_shortComplex
          (A := A) (M := M) (r := r))
  -- Proof comment: then use the already-proved tensor-collapse comparison for `d 1 0`.
  have hcollapse :
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
          ((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map (K.d 1 0) ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
          (λ_ (ModuleCat.of A M)).hom
        =
          T.d 1 ((ComplexShape.down ℕ).next 1) ≫
            (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
            (λ_ (ModuleCat.of A M)).hom := by
    simpa [Category.assoc, K, T] using
      congrArg
        (fun f =>
          f ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
            (λ_ (ModuleCat.of A M)).hom)
        (koszul_singleton_tensor_collapse_commutes_with_differential
          (A := A) (M := M) (r := r))
  -- Proof comment: finally rewrite the target window map back to `T.sc 1`.
  have hwindow :
      T.d 1 ((ComplexShape.down ℕ).next 1) ≫
          (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
          (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
          (λ_ (ModuleCat.of A M)).hom
        =
          (T.sc 1).g ≫
            ((T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)).hom ≫
              (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom ≫
              (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
                (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
              (λ_ (ModuleCat.of A M)).hom) := by
    simp [T, Category.assoc]
  exact hnormalize.trans (hcollapse.trans hwindow)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the degree-`1` window of the
singleton coefficient Koszul complex is isomorphic to the normalized short complex
`0 → M --r→ M`. -/
theorem koszul_singleton_tensor_sc1_iso_smulShortComplex {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let T := HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    let e₁ :
        T.X 1 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
            fin_one_module_iso (A := A))) ≪≫
        (λ_ (ModuleCat.of A M))
    let e₀ :
        T.X 0 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))) ≪≫
        (λ_ (ModuleCat.of A M))
    ∃ e :
      (let T := HomologicalComplex.tensorObj
        (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
      T.sc 1 ≅
        ShortComplex.mk
          (0 : (T.sc 1).X₁ ⟶ ModuleCat.of A M)
          (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
          (zero_comp_smulShortComplex_f ((T.sc 1).X₁) M (r := r))),
      e.hom.τ₂ = e₁.hom ∧ (T.sc 1).g ≫ e.hom.τ₃ = T.d 1 0 ≫ e₀.hom := by
  classical
  dsimp
  let T := HomologicalComplex.tensorObj
    (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
    ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
  let e₁ :
      T.X 1 ≅ ModuleCat.of A M :=
    (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1) ≪≫
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
        ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
          fin_one_module_iso (A := A))) ≪≫
      (λ_ (ModuleCat.of A M))
  let e₀ :
      T.X 0 ≅ ModuleCat.of A M :=
    (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0) ≪≫
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))) ≪≫
      (λ_ (ModuleCat.of A M))
  let e₀' : (T.sc 1).X₃ ≅ ModuleCat.of A M :=
    (T.XIsoOfEq (by simp : (ComplexShape.down ℕ).next 1 = 0)) ≪≫ e₀
  have hX2 : IsZero (T.X 2) := by
    have hK2 : IsZero
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X 2) := by
      -- Proof comment: the singleton source Koszul complex already vanishes in degree `2`.
      simpa using
        koszulComplexOn_singleton_X_isZero_of_two_le (A := A) (r := r) (n := 2) le_rfl
    -- Proof comment: the degreewise tensor comparison transports this vanishing to the
    -- coefficient complex.
    exact (Iso.isZero_iff
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 2)).mpr
      ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map_isZero hK2))
  have hprev : (ComplexShape.down ℕ).prev 1 = 2 := by
    -- Proof comment: degree `1` in a chain complex receives its incoming differential from
    -- degree `2`.
    simp
  have hscX1 : IsZero ((T.sc 1).X₁) := by
    -- Proof comment: the left object of the degree-`1` window is just the degree-`2` term.
    simpa using (Iso.isZero_iff (T.XIsoOfEq hprev)).mpr hX2
  have hleft : (T.sc 1).f ≫ e₁.hom = 0 := by
    -- Proof comment: the left object of the singleton degree-`1` window is zero, so its
    -- outgoing map vanishes after any postcomposition.
    exact hscX1.eq_of_src _ _
  let e :
      T.sc 1 ≅
        ShortComplex.mk
          (0 : (T.sc 1).X₁ ⟶ ModuleCat.of A M)
          (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
          (zero_comp_smulShortComplex_f ((T.sc 1).X₁) M (r := r)) :=
    ShortComplex.isoMk (Iso.refl _) e₁ e₀'
      (by simpa using hleft.symm)
      (singleton_tensor_sc1_right_square (A := A) (M := M) (r := r))
  refine ⟨e, rfl, ?_⟩
  -- Proof comment: the right component was chosen to include the degree-`0` transport, so the
  -- `sc 1` square is exactly the original `d 1 0` compatibility.
  change (T.sc 1).g ≫ e₀'.hom = T.d 1 0 ≫ e₀.hom
  simpa [e₀'] using
    (HomologicalComplex.d_comp_XIsoOfEq_hom T (by simp : (ComplexShape.down ℕ).next 1 = 0) 1)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after transporting the degree-`1`
term of the singleton coefficient Koszul complex back to `M`, the differential `d 1 0` becomes
scalar multiplication by `r`. -/
theorem koszul_singleton_tensor_degree_one_differential_eq_smul {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let T := HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    let e₁ :
        T.X 1 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
            fin_one_module_iso (A := A))) ≪≫
        (λ_ (ModuleCat.of A M))
    let e₀ :
        T.X 0 ≅ ModuleCat.of A M :=
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0) ≪≫
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))) ≪≫
        (λ_ (ModuleCat.of A M))
    e₁.hom ≫ (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f =
      T.d 1 0 ≫ e₀.hom := by
  classical
  let T := HomologicalComplex.tensorObj
    (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
    ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
  rcases koszul_singleton_tensor_sc1_iso_smulShortComplex (A := A) (M := M) (r := r) with
    ⟨e, hτ₂, hτ₃⟩
  -- Proof comment: the second commutative square of the window isomorphism is exactly the desired
  -- differential identity.
  dsimp [T]
  have hcomm :
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom ≫
          (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
            ((ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫
              fin_one_module_iso (A := A))).hom ≫
          (λ_ (ModuleCat.of A M)).hom ≫
          (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
          = (T.sc 1).g ≫ e.hom.τ₃ := by
        simpa [hτ₂] using e.hom.comm₂₃
  have hright :
      (T.sc 1).g ≫ e.hom.τ₃ =
        T.d 1 0 ≫
          ((koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom ≫
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
              (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A)))).hom ≫
            (λ_ (ModuleCat.of A M)).hom) := by
        simpa using hτ₃
  exact hcomm.trans hright

/-- Helper for Remark 10.69.7 (Other types of regular sequences): once the singleton coefficient
complex is reduced to its degreewise tensor description, the only nontrivial remaining homology
check is the degree-`1` differential normalization. -/
theorem koszul_singleton_tensor_homology_isZero_of_isSMulRegular {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} (hr : IsSMulRegular M r) :
    ∀ i : ℕ, 1 ≤ i →
      IsZero (((HomologicalComplex.tensorObj
        (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).homology i)) := by
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with rfl | hi'
  · -- TODO: identify the mapped singleton degree-`1 → 0` differential with
    -- `ModuleCat.smulShortComplex (ModuleCat.of A M) r` and use injectivity from `hr`.
    let T := HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
    have hX2 : IsZero (T.X 2) := by
      have hK2 : IsZero
          ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X 2) := by
        -- Proof comment: the singleton source Koszul complex already vanishes in degree `2`.
        simpa using
          koszulComplexOn_singleton_X_isZero_of_two_le (A := A) (r := r) (n := 2) le_rfl
      -- Proof comment: transport the source vanishing through the degreewise tensor comparison.
      exact (Iso.isZero_iff
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 2)).mpr
        ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map_isZero hK2))
    have hprev : (ComplexShape.down ℕ).prev 1 = 2 := by
      -- Proof comment: degree `1` in a chain complex receives its incoming differential from
      -- degree `2`.
      simp
    have hX1 : IsZero ((T.sc 1).X₁) := by
      -- Proof comment: identify the left term of `T.sc 1` with `T.X 2`.
      exact (Iso.isZero_iff (T.XIsoOfEq hprev)).mpr hX2
    let S : ShortComplex (ModuleCat A) :=
      ShortComplex.mk
        (0 : (T.sc 1).X₁ ⟶ ModuleCat.of A M)
        (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f
        (zero_comp_smulShortComplex_f ((T.sc 1).X₁) M (r := r))
    rcases koszul_singleton_tensor_sc1_iso_smulShortComplex (A := A) (M := M) (r := r) with
      ⟨e, _, _⟩
    have hmono : Mono S.g := by
      -- Proof comment: the normalized right map is multiplication by `r`, hence monic by `hr`.
      simpa [S, ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using hr
    have hExact : S.Exact := by
      -- Proof comment: for a short complex `0 → M --r→ M`, exactness is equivalent to
      -- injectivity of the right map.
      exact (S.exact_iff_mono rfl).2 hmono
    letI : S.HasHomology := hExact.hasHomology
    have hHomology : IsZero S.homology := by
      -- Proof comment: exactness of the normalized singleton window kills its homology.
      simpa [ShortComplex.exact_iff_isZero_homology] using hExact
    -- Proof comment: transport the normalized vanishing back to the original singleton complex.
    simpa [T, HomologicalComplex.homology] using
      (Iso.isZero_iff (ShortComplex.homologyMapIso e)).mpr hHomology
  · have hi2 : 2 ≤ i := by omega
    -- Degrees `≥ 2` vanish because the singleton source complex has no terms there.
    simpa using
      koszul_singleton_tensor_homology_isZero_of_two_le (A := A) (M := M) (r := r) hi2

theorem isKoszulRegularOn_singleton_of_isSMulRegular {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {r : A} (hr : IsSMulRegular M r) :
    IsKoszulRegularOn M (Fin.cons r (Fin.elim0 : Fin 0 → A)) := by
  have hweak : IsWeaklyRegular M ([r] : List A) :=
    (isWeaklyRegular_singleton_iff M r).2 hr
  simpa [singleton_list_get_eq_fin_cons] using hweak.isKoszulRegularOn


end RingTheory.Sequence
