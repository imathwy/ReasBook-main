import StacksProject_2024.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.EmptyKoszulBasics

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in each degree, tensoring any
chain complex with `single₀ M` collapses to tensoring the corresponding term with `M` on the
right. -/
noncomputable def tensor_single₀_X_iso_tensorRight {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat A) ℕ) (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) :
    ((HomologicalComplex.tensorObj K
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n) ≅
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj (K.X n)) := by
  let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
  let X :
      CategoryTheory.GradedObject (ℕ × ℕ) (ModuleCat A) :=
    ((CategoryTheory.GradedObject.mapBifunctor (curriedTensor (ModuleCat A)) ℕ ℕ).obj K.X).obj S.X
  let c :
      CategoryTheory.GradedObject.CofanMapObjFun X (fun p : ℕ × ℕ => p.1 + p.2) n :=
    CategoryTheory.GradedObject.CofanMapObjFun.mk X (fun p : ℕ × ℕ => p.1 + p.2) n
      ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj (K.X n)))
      (fun p hp => by
        rcases p with ⟨i, j⟩
        -- Only the `(n, 0)` summand survives, since `single₀ M` is zero away from degree `0`.
        by_cases hj : j = 0
        · subst hj
          have hi' : i = n := by simpa using hp
          simpa [S] using
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso (K.XIsoOfEq hi')).hom
        · exact
            (IsInitial.isInitialObj ((curriedTensor (ModuleCat A)).obj (K.X i)) _
              ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
                (ModuleCat.of A M) j hj).isInitial)).to _)
  have hc : IsColimit c := by
    refine mkCofanColimit _ (fun s => ?_) (fun s a => ?_) ?_
    · -- The universal map is determined by the surviving `(n, 0)` summand.
      simpa [S] using s.inj ⟨⟨n, 0⟩, by simp⟩
    · rcases a with ⟨⟨i, j⟩, hij⟩
      by_cases hj : j = 0
      · subst hj
        have hi' : i = n := by simpa using hij
        subst hi'
        have hhij :
            hij = (by simp : (i, 0) ∈ (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' ({i} : Set ℕ)) := by
          apply Subsingleton.elim
        cases hhij
        dsimp [c, CategoryTheory.GradedObject.CofanMapObjFun.mk]
        rw [MonoidalCategory.id_whiskerRight]
        exact Category.id_comp _
      · apply IsInitial.hom_ext
        exact IsInitial.isInitialObj ((curriedTensor (ModuleCat A)).obj (K.X i)) _
          ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
            (ModuleCat.of A M) j hj).isInitial)
    · intro s m hm
      simpa [c, S] using hm ⟨⟨n, 0⟩, by simp⟩
  -- This is exactly the coproduct comparison between the tensor complex and termwise tensoring.
  simpa [HomologicalComplex.tensorObj, X, S] using
    (CategoryTheory.GradedObject.CofanMapObjFun.iso (j := n) hc).symm

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in each degree, tensoring the
singleton coefficient complex with `single₀ M` collapses to tensoring the corresponding Koszul
term with `M` on the right. -/
noncomputable def koszul_singleton_tensor_X_iso_tensorRight {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} (n : ℕ) :
    ((HomologicalComplex.tensorObj
        (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n) ≅
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
        ((koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).X n)) := by
  let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
  let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
  let X :
      CategoryTheory.GradedObject (ℕ × ℕ) (ModuleCat A) :=
    ((CategoryTheory.GradedObject.mapBifunctor (curriedTensor (ModuleCat A)) ℕ ℕ).obj K.X).obj S.X
  let c :
      CategoryTheory.GradedObject.CofanMapObjFun X (fun p : ℕ × ℕ => p.1 + p.2) n :=
    CategoryTheory.GradedObject.CofanMapObjFun.mk X (fun p : ℕ × ℕ => p.1 + p.2) n
      ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj (K.X n)))
      (fun p hp => by
        rcases p with ⟨i, j⟩
        -- Only the `(n, 0)` summand survives, since `single₀ M` is zero away from degree `0`.
        by_cases hj : j = 0
        · subst hj
          have hi' : i = n := by simpa using hp
          simpa [K, S] using
            (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso (K.XIsoOfEq hi')).hom
        · exact
            (IsInitial.isInitialObj ((curriedTensor (ModuleCat A)).obj (K.X i)) _
              ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
                (ModuleCat.of A M) j hj).isInitial)).to _)
  have hc : IsColimit c := by
    refine mkCofanColimit _ (fun s => ?_) (fun s a => ?_) ?_
    · -- The universal map is determined by the surviving `(n, 0)` summand.
      simpa [K, S] using s.inj ⟨⟨n, 0⟩, by simp⟩
    · rcases a with ⟨⟨i, j⟩, hij⟩
      by_cases hj : j = 0
      · subst hj
        have hi' : i = n := by simpa using hij
        subst hi'
        have hhij :
            hij = (by simp : (i, 0) ∈ (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' ({i} : Set ℕ)) := by
          apply Subsingleton.elim
        cases hhij
        dsimp [c, CategoryTheory.GradedObject.CofanMapObjFun.mk]
        rw [MonoidalCategory.id_whiskerRight]
        exact Category.id_comp _
      · apply IsInitial.hom_ext
        exact IsInitial.isInitialObj ((curriedTensor (ModuleCat A)).obj (K.X i)) _
          ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
            (ModuleCat.of A M) j hj).isInitial)
    · intro s m hm
      simpa [c, K, S] using hm ⟨⟨n, 0⟩, by simp⟩
  -- This is exactly the coproduct comparison between the tensor complex and termwise tensoring.
  simpa [HomologicalComplex.tensorObj, X, K, S] using
    (CategoryTheory.GradedObject.CofanMapObjFun.iso (j := n) hc).symm

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degrees at least `2`, the
singleton coefficient tensor complex has zero middle term, hence zero homology. -/
theorem koszul_singleton_tensor_homology_isZero_of_two_le {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} {i : ℕ} (hi : 2 ≤ i) :
    IsZero (((HomologicalComplex.tensorObj
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).homology i)) := by
  let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
  let T := HomologicalComplex.tensorObj K ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
  have hKi : IsZero (K.X i) := by
    -- The underlying singleton Koszul complex already vanishes in degree `i ≥ 2`.
    simpa using koszulComplexOn_singleton_X_isZero_of_two_le (A := A) (r := r) hi
  have hTi : IsZero (T.X i) := by
    -- The degreewise tensor comparison transports this vanishing to the coefficient complex.
    exact (Iso.isZero_iff
      (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) i)).mpr
      ((((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).map_isZero hKi))
  have hsc : IsZero ((T.sc i).X₂) := by
    simpa [T] using hTi
  -- Once the middle term is zero, the short-complex homology in degree `i` is zero.
  simpa [T, HomologicalComplex.homology] using
    (ShortComplex.isZero_homology_of_isZero_X₂ (T.sc i) hsc)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the unique-coordinate free module
`Fin 1 → A` identifies with `A` itself. -/
noncomputable def fin_one_module_iso {A : Type u} [CommRing A] :
    ModuleCat.of A (Fin 1 → A) ≅ ModuleCat.of A A :=
  (LinearEquiv.funUnique (Fin 1) A A).toModuleIso

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degree `1 → 0`, the Koszul
contraction becomes the defining linear form after identifying `⋀¹ E` with `E` and `⋀⁰ E`
with the base ring. -/
theorem koszul_degree_zero_contraction_eq_linearForm {A : Type u} [CommRing A]
    {E : Type u} [AddCommGroup E] [Module A E] (φ : E →ₗ[A] A) (x : E) :
    (exteriorPower.zeroEquiv A E)
      ((koszulDifferentialLinearMap φ 0) ((exteriorPower.oneEquiv A E).symm x)) = φ x := by
  -- Proof comment: rewrite the degree-`1` generator as the canonical wedge of `x`.
  have hcalc :
      (koszulDifferentialLinearMap φ 0) ((exteriorPower.oneEquiv A E).symm x) =
        (φ x) • (exteriorPower.ιMulti A 0 (Fin.elim0 : Fin 0 → E)) := by
    -- Proof comment: after coercing out of the degree-`0` exterior power, the contraction
    -- formula is exactly `contractLeft_ι`.
    apply Subtype.ext
    simp [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  rw [hcalc]
  -- Proof comment: `zeroEquiv` sends the canonical degree-`0` generator to `1`.
  simp [exteriorPower.zeroEquiv_ιMulti]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): before tensoring with a
coefficient module, the singleton Koszul differential `d 1 0` is multiplication by `r`
after the standard degree-`1` and degree-`0` identifications. -/
theorem koszul_singleton_degree_one_differential_eq_smul_base {A : Type u} [CommRing A] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let k₁ : K.X 1 ≅ ModuleCat.of A A :=
      (ModuleCat.exteriorPower.iso₁ (ModuleCat.of A (Fin 1 → A))) ≪≫ fin_one_module_iso (A := A)
    let k₀ : K.X 0 ≅ ModuleCat.of A A :=
      ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 1 → A))
    ModuleCat.ofHom (r • LinearMap.id) = k₁.inv ≫ K.d 1 0 ≫ k₀.hom := by
  dsimp
  let φ := koszulFamilyLinearMap (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
  have hd :
      (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))).d 1 0 =
        koszulDifferential φ 0 := by
    -- Proof comment: the singleton Koszul complex is a `ChainComplex.of`, so `d 1 0`
    -- is the degree-zero Koszul differential.
    rfl
  rw [hd]
  ext
  have hfunUnique :
      ((((LinearEquiv.funUnique (Fin 1) A A).symm) 1 : Fin 1 → A)) = Pi.basisFun A (Fin 1) 0 := by
    -- Proof comment: in the unique-coordinate free module, `1` is the unique basis vector.
    ext i
    fin_cases i
    simp [Pi.basisFun, LinearEquiv.funUnique_symm_apply]
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply, ModuleCat.hom_ofHom]
  change (r • LinearMap.id) 1 =
      (exteriorPower.zeroEquiv A (Fin 1 → A))
        ((koszulDifferentialLinearMap φ 0)
          ((exteriorPower.oneEquiv A (Fin 1 → A)).symm (((fin_one_module_iso (A := A)).inv) 1)))
  rw [koszul_degree_zero_contraction_eq_linearForm]
  -- Proof comment: the singleton family sends its unique basis vector to `r`.
  have hφ :
      φ (((fin_one_module_iso (A := A)).inv) 1) = r := by
    calc
      φ (((fin_one_module_iso (A := A)).inv) 1) = φ (Pi.basisFun A (Fin 1) 0) := by
        simpa [fin_one_module_iso] using congrArg φ hfunUnique
      _ = r := by
        simpa [φ] using (koszulFamilyLinearMap_basis (f := Fin.cons r (Fin.elim0 : Fin 0 → A)) 0)
  simpa using hφ.symm

/-- Helper for Remark 10.69.7 (Other types of regular sequences): composing the zero morphism with
the scalar-multiplication map still gives the zero morphism. -/
theorem zero_comp_smulShortComplex_f {A : Type u} [CommRing A]
    (X : ModuleCat A) (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    (0 : X ⟶ ModuleCat.of A M) ≫ (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f = 0 := by
  -- Proof comment: this is the defining zero-composition property in the normalized short
  -- complex `0 → M --r→ M`.
  simpa using
    (show (0 : X ⟶ ModuleCat.of A M) ≫ (ModuleCat.smulShortComplex (ModuleCat.of A M) r).f = 0
      from zero_comp)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): under the left unitor, scalar
multiplication on the tensor-unit factor is identified with scalar multiplication on the
coefficient module. -/
theorem smul_tensor_left_unitor_naturality {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    ((ModuleCat.ofHom (r • LinearMap.id) : ModuleCat.of A A ⟶ ModuleCat.of A A) ▷
        ModuleCat.of A M) ≫
        (λ_ (ModuleCat.of A M)).hom =
      (λ_ (ModuleCat.of A M)).hom ≫
        (ModuleCat.ofHom (r • LinearMap.id) : ModuleCat.of A M ⟶ ModuleCat.of A M) := by
  -- Proof comment: both composites send `a ⊗ m` to `(r * a) • m`, so extensionality on tensors
  -- reduces the statement to the defining formula for the left unitor.
  ext x
  simp [ModuleCat.hom_whiskerRight, ModuleCat.hom_hom_leftUnitor]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): on the surviving
`(n, 0)` summand, the singleton tensor-collapse map is the identity after the canonical
degree-zero coefficient identification. -/
theorem koszul_singleton_tensor_X_iso_tensorRight_hom_comp_ι {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} (n : ℕ) :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    HomologicalComplex.ιTensorObj K S n 0 n (by simp) ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) n).hom =
      𝟙 _ := by
  -- Proof comment: the collapse isomorphism is defined from the cofan whose surviving injection
  -- is exactly the `(n, 0)` inclusion, so this component computation is formal.
  dsimp [koszul_singleton_tensor_X_iso_tensorRight, HomologicalComplex.ιTensorObj]
  erw [CategoryTheory.GradedObject.CofanMapObjFun.ιMapObj_iso_inv]
  simp

/-- Helper for Remark 10.69.7 (Other types of regular sequences): on the `(0, 1)` summand of the
degree-`1` total object, the singleton tensor-collapse map is zero because the coefficient complex
already vanishes in degree `1`. -/
theorem koszul_singleton_tensor_X_iso_tensorRight_hom_comp_ι_zero_right {A : Type u}
    [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    HomologicalComplex.ιTensorObj K S 0 1 1 (by simp) ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 1).hom =
      0 := by
  -- Proof comment: in the defining cofan for the collapse map, the `(0, 1)` summand factors
  -- through the zero degree-`1` piece of `single₀ M`, so the induced component is the zero map.
  dsimp [koszul_singleton_tensor_X_iso_tensorRight, HomologicalComplex.ιTensorObj]
  erw [CategoryTheory.GradedObject.CofanMapObjFun.ιMapObj_iso_inv]
  let hinit :
      IsInitial
        (((curriedTensor (ModuleCat A)).obj ((ModuleCat.of A (Fin 1 → A)).exteriorPower 0)).obj
          (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)).X 1)) :=
    IsInitial.isInitialObj ((curriedTensor (ModuleCat A)).obj
      ((ModuleCat.of A (Fin 1 → A)).exteriorPower 0)) _
      ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (ModuleCat.of A M) 1 (by simp)).isInitial)
  exact hinit.hom_ext _ _

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the degreewise tensor-collapse
isomorphisms for the singleton coefficient complex intertwine the degree-`1 → 0` differential with
the mapped base Koszul differential. -/
theorem singleton_tensor_degree_one_postcompose_split {A : Type u} [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] {r : A} :
    let K := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A))
    let S := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)
    let T := HomologicalComplex.tensorObj K S
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        T.d 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
      =
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₁ K S (curriedTensor (ModuleCat A))
          (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom
      +
    HomologicalComplex.ιTensorObj K S 1 0 1 (by simp) ≫
        HomologicalComplex.mapBifunctor.D₂ K S (curriedTensor (ModuleCat A))
          (ComplexShape.down ℕ) 1 0 ≫
        (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom := by
  dsimp
  -- Proof comment: this is just the tensor differential decomposition `d = D₁ + D₂`,
  -- postcomposed with the degree-zero collapse map.
  simpa [Category.assoc, Preadditive.comp_add] using
    congrArg
      (fun f =>
        HomologicalComplex.ιTensorObj
            (koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
            ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M)) 1 0 1 (by simp) ≫
          f ≫
            (koszul_singleton_tensor_X_iso_tensorRight (A := A) (M := M) (r := r) 0).hom)
      (HomologicalComplex.mapBifunctor.d_eq
        (K₁ := koszulComplexOn (R := A) (Fin.cons r (Fin.elim0 : Fin 0 → A)))
        (K₂ := (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))
        (F := curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ) 1 0)


end RingTheory.Sequence
