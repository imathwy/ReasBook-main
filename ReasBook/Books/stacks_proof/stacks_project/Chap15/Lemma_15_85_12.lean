import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR
local notation "singleComplex₀" => CochainComplex.singleFunctor ModR (0 : ℤ)
local notation "KModR" => HomotopyCategory ModR (ComplexShape.up ℤ)

/-- The canonical two-term cochain complex attached to an endomorphism `f`. -/
private abbrev endomorphismTwoTermCone {M : Type w} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) : CochainComplex ModR ℤ :=
  CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom f))

/-- The canonical two-term cochain complex attached to a square matrix `A`. -/
private abbrev matrixTwoTermCone {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : CochainComplex ModR ℤ :=
  endomorphismTwoTermCone A.toLin'

/-- Helper for Lemma 15.85.12: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {C D : CochainComplex ModR ℤ}
    (f : C ⟶ D) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModR).app C)
      ((DerivedCategory.quotientCompQhIso ModR).app D))
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- Rewrite the conjugated morphism into the naturality square of `quotientCompQhIso`.
  change
    (DerivedCategory.quotientCompQhIso ModR).inv.app C ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModR).hom.app D =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModR).hom.app D =
        (DerivedCategory.quotientCompQhIso ModR).hom.app C ≫ DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso ModR).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso ModR).inv.app C ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModR).hom.app D =
      (DerivedCategory.quotientCompQhIso ModR).inv.app C ≫
        ((DerivedCategory.quotientCompQhIso ModR).hom.app C ≫ DerivedCategory.Q.map f) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (DerivedCategory.quotientCompQhIso ModR).inv.app C ≫ k) hnat
    _ = DerivedCategory.Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso ModR).app C)
              (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.85.12: a null-homotopic scalar multiple of the identity becomes zero in
the derived category. -/
private theorem q_obj_smul_id_eq_zero_of_homotopy_zero
    {C : CochainComplex ModR ℤ}
    (r : R) (h : Homotopy (r • 𝟙 C) 0) :
    r • 𝟙 (DerivedCategory.Q.obj C) = 0 := by
  -- First kill the morphism in the homotopy quotient.
  have hquot :
      (HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map (r • 𝟙 C) = 0 := by
    exact (HomotopyCategory.quotient_map_eq_zero_iff (r • 𝟙 C)).2 ⟨h⟩
  have hQh :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)).map (r • 𝟙 C)) = 0 := by
    simp [hquot]
  -- Then transport that vanishing back across `quotientCompQhIso`.
  have hQ :
      DerivedCategory.Q.map (r • 𝟙 C) = 0 := by
    have htransport := quotientCompQhIso_homCongr_map (R := R) (f := r • 𝟙 C)
    rw [hQh] at htransport
    calc
      DerivedCategory.Q.map (r • 𝟙 C) =
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModR).app C)
          ((DerivedCategory.quotientCompQhIso ModR).app C)) 0 := htransport.symm
      _ = 0 := by
        change (DerivedCategory.quotientCompQhIso ModR).inv.app C ≫ 0 ≫
            (DerivedCategory.quotientCompQhIso ModR).hom.app C = 0
        rw [zero_comp, comp_zero]
  simpa using hQ

/-- Helper for Lemma 15.85.12: scalar vanishing transports across an isomorphism in the derived
category. -/
private theorem smul_id_eq_zero_of_isIsomorphic
    {X Y : DModR}
    (r : R) (hXY : IsIsomorphic X Y) (hX : r • 𝟙 X = 0) :
    r • 𝟙 Y = 0 := by
  rcases hXY with ⟨e⟩
  -- Conjugate the zero equality along the chosen isomorphism.
  have htransport : e.inv ≫ (r • 𝟙 X) ≫ e.hom = 0 := by
    simpa using congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) hX
  calc
    r • 𝟙 Y = e.inv ≫ (r • 𝟙 X) ≫ e.hom := by
      simp
    _ = 0 := htransport

/-- Helper for Lemma 15.85.12: the degree-`i` term of the canonical two-term cone is zero away
from `i = -1` and `i = 0`. -/
private theorem matrix_two_term_cone_isZero_X
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) {i : ℤ} (hi0 : i ≠ 0) (hiNegOne : i ≠ -1) :
    Limits.IsZero ((matrixTwoTermCone A).X i) := by
  let M : ModR := ModuleCat.of R (ι → R)
  let φ : (singleComplex₀).obj M ⟶ (singleComplex₀).obj M :=
    (singleComplex₀).map (ModuleCat.ofHom A.toLin')
  have hleft :
      Limits.IsZero (((singleComplex₀).obj M).X (i + 1)) := by
    -- The source single complex only has a nonzero term in degree `0`.
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M (i + 1))
    intro hi
    apply hiNegOne
    linarith
  have hright :
      Limits.IsZero (((singleComplex₀).obj M).X i) := by
    -- The target single complex only has a nonzero term in degree `0`.
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i)
    exact hi0
  exact (CochainComplex.mappingCone.isZero_X_iff (φ := φ) i).2 ⟨hleft, hright⟩

/-- Helper for Lemma 15.85.12: the degree-zero component of the single-complex map induced by
any morphism is the morphism itself. -/
private theorem single_zero_map_f_zero_eq_ofHom
    {M N : ModR} (u : M ⟶ N) :
    ((singleComplex₀).map u).f 0 = u := by
  -- Normalize the single-complex map to its unique nonzero degree.
  simpa [CochainComplex.singleFunctor, CochainComplex.singleFunctors] using
    (HomologicalComplex.single_map_f_self (V := ModR) (c := ComplexShape.up ℤ)
      (j := (0 : ℤ)) (f := u))

/-- Helper for Lemma 15.85.12: the degree `-1` term of a degree-zero single complex is zero. -/
private theorem single_zero_obj_isZero_negOne
    (M : ModR) :
    Limits.IsZero (((singleComplex₀).obj M).X (-1)) := by
  -- The single complex is supported only at degree `0`.
  apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M (-1))
  norm_num

/-- Helper for Lemma 15.85.12: the degree `1` term of a degree-zero single complex is zero. -/
private theorem single_zero_obj_isZero_one
    (M : ModR) :
    Limits.IsZero (((singleComplex₀).obj M).X 1) := by
  -- The single complex is supported only at degree `0`.
  apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M 1)
  norm_num

/-- Helper for Lemma 15.85.12: the degree-zero component of the single-complex map induced by
`A` composed with the adjugate map is multiplication by `det A`. -/
private theorem single_map_comp_adjugate_eq_det_smul_id
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    ((singleComplex₀).map (ModuleCat.ofHom A.toLin')).f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' =
      (Matrix.det A) • 𝟙 (((singleComplex₀).obj (ModuleCat.of R (ι → R))).X 0) := by
  -- Rewrite the degree-zero component to the raw module map.
  rw [single_zero_map_f_zero_eq_ofHom (R := R) (u := ModuleCat.ofHom A.toLin')]
  -- The source proof uses the adjugate identity on the left action at degree `-1`.
  calc
    ModuleCat.ofHom A.toLin' ≫ ModuleCat.ofHom A.adjugate.toLin' =
        ModuleCat.ofHom ((A.adjugate * A).toLin') := by
          simp [Matrix.toLin'_mul]
    _ = ModuleCat.ofHom ((Matrix.det A • (1 : Matrix ι ι R)).toLin') := by
          rw [Matrix.adjugate_mul]
    _ = (Matrix.det A) • 𝟙 (((singleComplex₀).obj (ModuleCat.of R (ι → R))).X 0) := by
          rw [show ((Matrix.det A • (1 : Matrix ι ι R)).toLin') =
              (Matrix.det A) • (LinearMap.id : (ι → R) →ₗ[R] ι → R) by
                simp [Matrix.toLin'_one]]
          ext x i
          rfl

/-- Helper for Lemma 15.85.12: the adjugate map composed with the degree-zero component induced by
`A` is multiplication by `det A`. -/
private theorem adjugate_comp_single_map_eq_det_smul_id
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    ModuleCat.ofHom A.adjugate.toLin' ≫ ((singleComplex₀).map (ModuleCat.ofHom A.toLin')).f 0 =
      (Matrix.det A) • 𝟙 (((singleComplex₀).obj (ModuleCat.of R (ι → R))).X 0) := by
  -- Rewrite the degree-zero component to the raw module map.
  rw [single_zero_map_f_zero_eq_ofHom (R := R) (u := ModuleCat.ofHom A.toLin')]
  -- The source proof uses the adjugate identity on the right action at degree `0`.
  calc
    ModuleCat.ofHom A.adjugate.toLin' ≫ ModuleCat.ofHom A.toLin' =
        ModuleCat.ofHom ((A * A.adjugate).toLin') := by
          simp [Matrix.toLin'_mul]
    _ = ModuleCat.ofHom ((Matrix.det A • (1 : Matrix ι ι R)).toLin') := by
          rw [Matrix.mul_adjugate]
    _ = (Matrix.det A) • 𝟙 (((singleComplex₀).obj (ModuleCat.of R (ι → R))).X 0) := by
          rw [show ((Matrix.det A • (1 : Matrix ι ι R)).toLin') =
              (Matrix.det A) • (LinearMap.id : (ι → R) →ₗ[R] ι → R) by
                simp [Matrix.toLin'_one]]
          ext x i
          rfl

/-- Helper for Lemma 15.85.12: the adjugate homotopy datum on the two-term cone is supported only
in the unique source-faithful degree pair `0 → -1`. -/
private noncomputable abbrev adjugate_two_term_homotopy_hom
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    ∀ i j, (ComplexShape.up ℤ).Rel j i →
      ((matrixTwoTermCone A).X i ⟶ (matrixTwoTermCone A).X j)
  | 0, -1, _ =>
      (CochainComplex.mappingCone.snd ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 0
          (add_zero 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫
        (CochainComplex.mappingCone.inl ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0
          (-1) (by simp)
  | _, _, _ => 0

/-- Helper for Lemma 15.85.12: the `inl`/`fst` projection pair on the cone is the identity on the
source summand in degree `-1`. -/
private theorem mappingCone_inl_v_comp_fst_v_eq_id
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) :
    (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
      (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
        𝟙 (C.X 0) := by
  -- The cone term in degree `-1` is the biproduct `C.X 0 ⊞ D.X (-1)`, so this is the standard
  -- `biprod.inl_fst` identity.
  simpa using (biprod.inl_fst :
    (biprod.inl : C.X 0 ⟶ C.X 0 ⊞ D.X (-1)) ≫ biprod.fst = 𝟙 (C.X 0))

/-- Helper for Lemma 15.85.12: the `inr`/`snd` projection pair on the cone is the identity on the
target summand in degree `0`. -/
private theorem mappingCone_inr_f_comp_snd_v_eq_id
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) :
    (CochainComplex.mappingCone.inr φ).f 0 ≫
      (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) =
        𝟙 (D.X 0) := by
  -- The cone term in degree `0` is the biproduct `C.X 1 ⊞ D.X 0`, so this is the standard
  -- `biprod.inr_snd` identity.
  simp

/-- Helper for Lemma 15.85.12: the `inl` component of the cone inclusion is independent of the
relation witness. -/
private theorem mappingCone_inl_v_proof_irrel
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) {i j : ℤ}
    (h h' : i + -1 = j) :
    (CochainComplex.mappingCone.inl φ).v i j h =
      (CochainComplex.mappingCone.inl φ).v i j h' := by
  -- The relation witness lives in a proposition, so the corresponding component is proof-irrelevant.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.85.12: the `fst` component of the cone projection is independent of the
relation witness. -/
private theorem mappingCone_fst_v_proof_irrel
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) {i j : ℤ}
    (h h' : i + 1 = j) :
    (CochainComplex.mappingCone.fst φ).1.v i j h =
      (CochainComplex.mappingCone.fst φ).1.v i j h' := by
  -- The cocycle witness is also a proposition, so the component does not depend on its proof.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.85.12: the `snd` component of the cone projection is independent of the
degree-zero witness. -/
private theorem mappingCone_snd_v_proof_irrel
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) {i : ℤ}
    (h h' : i + 0 = i) :
    (CochainComplex.mappingCone.snd φ).v i i h =
      (CochainComplex.mappingCone.snd φ).v i i h' := by
  -- The degree-zero witness is a proposition, so the component is proof-irrelevant as well.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.85.12: the degree-`-1` cone projection commutes with scalar identities. -/
private theorem mappingCone_fst_postcompose_smul_id
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) (r : R) :
    (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ (r • 𝟙 (C.X 0)) =
      (r • 𝟙 ((CochainComplex.mappingCone φ).X (-1))) ≫
        (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl := by
  -- Both composites are the same scalar multiple of the cone projection onto the source summand.
  ext x
  simp [ModuleCat.hom_comp]

/-- Helper for Lemma 15.85.12: the degree-`0` cone projection commutes with scalar identities. -/
private theorem mappingCone_snd_postcompose_smul_id
    {C D : CochainComplex ModR ℤ} (φ : C ⟶ D) (r : R) :
    (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫ (r • 𝟙 (D.X 0)) =
      (r • 𝟙 ((CochainComplex.mappingCone φ).X 0)) ≫
        (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) := by
  -- Both composites are the same scalar multiple of the cone projection onto the target summand.
  ext x
  simp [ModuleCat.hom_comp]

/-- Helper for Lemma 15.85.12: the degree `-1 → 0` differential of the degree-zero single complex
vanishes because the source term is zero. -/
private theorem single_zero_d_negOne_zero_eq_zero
    (M : ModR) :
    ((singleComplex₀).obj M).d (-1) 0 = 0 := by
  -- The source of this differential is the zero degree `-1` term of the single complex.
  exact (single_zero_obj_isZero_negOne (R := R) M).eq_of_src _ 0

/-- Helper for Lemma 15.85.12: the degree `0 → 1` differential of the degree-zero single complex
vanishes because the target term is zero. -/
private theorem single_zero_d_zero_one_eq_zero
    (M : ModR) :
    ((singleComplex₀).obj M).d 0 1 = 0 := by
  -- The target of this differential is the zero degree `1` term of the single complex.
  exact (single_zero_obj_isZero_one (R := R) M).eq_of_tgt _ 0

/-- Helper for Lemma 15.85.12: the degree-`-1` cone boundary identity remains valid after
postcomposing with the adjugate branch and projecting to the source summand. -/
private theorem mappingCone_d_snd_postcompose_adjugate_inl_fst
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    let φ := (singleComplex₀).map (ModuleCat.ofHom A.toLin')
    (matrixTwoTermCone A).d (-1) 0 ≫
        (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
              (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
      (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
        φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' := by
  -- Route correction: normalize the cone witnesses first, then use `d_snd_v'` and kill the
  -- residual single-complex differential term before collapsing the `inl`/`fst` pair to `𝟙`.
  let M : ModR := ModuleCat.of R (ι → R)
  let φ : (singleComplex₀).obj M ⟶ (singleComplex₀).obj M :=
    (singleComplex₀).map (ModuleCat.ofHom A.toLin')
  change
    (CochainComplex.mappingCone φ).d (-1) 0 ≫
        (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
              (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
      (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
        φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin'
  -- First expose the cone boundary as the sum of the surviving `fst ≫ φ ≫ adj` branch and the
  -- dead single-complex differential branch.
  have hcore :=
    CochainComplex.mappingCone.d_snd_v'_assoc (φ := φ) 0
      (ModuleCat.ofHom A.adjugate.toLin' ≫
        (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
          (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl)
  -- Then the second summand vanishes because the source single complex has no degree `-1` term,
  -- while the remaining `inl ≫ fst` collapses to the identity on the source summand.
  have hnormalized :
      (CochainComplex.mappingCone φ).d (-1) 0 ≫
          (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
            ModuleCat.ofHom A.adjugate.toLin' ≫
              (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
                (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
        (((CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ φ.f 0) + 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
              (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl := by
    simpa [Category.assoc, single_zero_d_negOne_zero_eq_zero (R := R) M] using hcore
  calc
    (CochainComplex.mappingCone φ).d (-1) 0 ≫
        (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
              (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
      (((CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ φ.f 0) + 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫
          (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
            (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl := hnormalized
    _ = ((CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ φ.f 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
              (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl := by
          exact congrArg
            (fun k ↦ k ≫ ModuleCat.ofHom A.adjugate.toLin' ≫
              (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
                (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl)
            (add_zero ((CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ φ.f 0))
    _ = (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
          φ.f 0 ≫
            (ModuleCat.ofHom A.adjugate.toLin' ≫
              (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
                (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl) := by
          simp [Category.assoc]
    _ = (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
          φ.f 0 ≫ (ModuleCat.ofHom A.adjugate.toLin' ≫ 𝟙 (((singleComplex₀).obj M).X 0)) := by
          exact congrArg
            (fun k ↦ (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
              φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' ≫ k)
            (mappingCone_inl_v_comp_fst_v_eq_id (R := R) (φ := φ))
    _ = (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
          φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' := by
          exact Category.comp_id
            ((CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
              φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin')

/-- Helper for Lemma 15.85.12: the degree-`0` cone boundary identity remains valid after
precomposing with the adjugate branch and projecting to the target summand. -/
private theorem mappingCone_snd_adjugate_inl_d_postcompose_snd
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    let φ := (singleComplex₀).map (ModuleCat.ofHom A.toLin')
    (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫
          (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
            (matrixTwoTermCone A).d (-1) 0 ≫
              (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) =
      (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫ φ.f 0 := by
  -- Route correction: normalize the witnesses, apply `inl_v_d`, then kill the vanishing
  -- single-complex differential term before collapsing the `inr`/`snd` pair to `𝟙`.
  let M : ModR := ModuleCat.of R (ι → R)
  let φ : (singleComplex₀).obj M ⟶ (singleComplex₀).obj M :=
    (singleComplex₀).map (ModuleCat.ofHom A.toLin')
  change
    (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫
          (CochainComplex.mappingCone.inl φ).v 0 (-1) (by simp) ≫
            (CochainComplex.mappingCone φ).d (-1) 0 ≫
              (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) =
      (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
        ModuleCat.ofHom A.adjugate.toLin' ≫ φ.f 0
  have hcore :=
    CochainComplex.mappingCone.inl_v_d_assoc (φ := φ) 0 (-1) 1 (by simp) (by simp)
      ((CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0))
  -- Rewrite the cone boundary through the source summand, then precompose by the adjugate branch.
  have h := congrArg
    (fun k ↦ (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
      ModuleCat.ofHom A.adjugate.toLin' ≫ k) hcore
  -- The unwanted single-complex differential dies, and the `inr`/`snd` pair is the identity.
  simpa [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
    single_zero_d_zero_one_eq_zero (R := R) M,
    mappingCone_inr_f_comp_snd_v_eq_id (R := R) (φ := φ)] using h

/-- Helper for Lemma 15.85.12: in degree `-1`, the null-homotopic map attached to the adjugate
datum agrees with multiplication by `det A`. -/
private theorem adjugate_nullHomotopicMap_f_negOne_eq_det_smul_id
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    (Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A)).f (-1) =
      (Matrix.det A) • 𝟙 ((matrixTwoTermCone A).X (-1)) := by
  let M : ModR := ModuleCat.of R (ι → R)
  let φ : (singleComplex₀).obj M ⟶ (singleComplex₀).obj M :=
    (singleComplex₀).map (ModuleCat.ofHom A.toLin')
  change
    (Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A)).f (-1) =
      (Matrix.det A) • 𝟙 ((CochainComplex.mappingCone φ).X (-1))
  -- Compare the two endomorphisms through the cone projections in degree `-1`.
  rw [CochainComplex.mappingCone.ext_to_iff φ (-1) 0 rfl]
  constructor
  · -- The `fst` projection sees exactly the adjugate boundary computation.
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
    suffices hmain :
        (matrixTwoTermCone A).d (-1) 0 ≫
            (CochainComplex.mappingCone.snd
                ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 0
                  adjugate_two_term_homotopy_hom._proof_4 ≫
              ModuleCat.ofHom A.adjugate.toLin' ≫
                (CochainComplex.mappingCone.inl
                    ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 (-1)
                      adjugate_two_term_homotopy_hom._proof_5 ≫
                  (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
          (Matrix.det A • 𝟙 ((CochainComplex.mappingCone φ).X (-1))) ≫
            (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl by
      simpa [adjugate_two_term_homotopy_hom, Category.assoc] using hmain
    have hboundary :
        (matrixTwoTermCone A).d (-1) 0 ≫
            (CochainComplex.mappingCone.snd
                ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 0
                  adjugate_two_term_homotopy_hom._proof_4 ≫
              ModuleCat.ofHom A.adjugate.toLin' ≫
                (CochainComplex.mappingCone.inl
                    ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 (-1)
                      adjugate_two_term_homotopy_hom._proof_5 ≫
                  (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl =
          (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
            φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' := by
      simpa [matrixTwoTermCone, endomorphismTwoTermCone, M, φ, Category.assoc] using
        mappingCone_d_snd_postcompose_adjugate_inl_fst (R := R) (A := A)
    have hdet :
        φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' =
          (Matrix.det A) • 𝟙 (((singleComplex₀).obj M).X 0) := by
      simpa [M] using single_map_comp_adjugate_eq_det_smul_id (R := R) (A := A)
    have hcompose :
        (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
            φ.f 0 ≫ ModuleCat.ofHom A.adjugate.toLin' =
          (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫
            ((Matrix.det A) • 𝟙 (((singleComplex₀).obj M).X 0)) := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ (CochainComplex.mappingCone.fst φ).1.v (-1) 0 rfl ≫ k) hdet
    exact hboundary.trans <| hcompose.trans <|
      mappingCone_fst_postcompose_smul_id (R := R) (φ := φ) (Matrix.det A)
  · -- The `snd` projection lands in the zero degree `-1` term of the single complex.
    let hzero : Limits.IsZero (((singleComplex₀).obj M).X (-1)) :=
      single_zero_obj_isZero_negOne (R := R) M
    exact (hzero.eq_of_tgt _ 0).trans (hzero.eq_of_tgt _ 0).symm

/-- Helper for Lemma 15.85.12: in degree `0`, the null-homotopic map attached to the adjugate
datum agrees with multiplication by `det A`. -/
private theorem adjugate_nullHomotopicMap_f_zero_eq_det_smul_id
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    (Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A)).f 0 =
      (Matrix.det A) • 𝟙 ((matrixTwoTermCone A).X 0) := by
  let M : ModR := ModuleCat.of R (ι → R)
  let φ : (singleComplex₀).obj M ⟶ (singleComplex₀).obj M :=
    (singleComplex₀).map (ModuleCat.ofHom A.toLin')
  change
    (Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A)).f 0 =
      (Matrix.det A) • 𝟙 ((CochainComplex.mappingCone φ).X 0)
  -- Compare the two endomorphisms through the cone projections in degree `0`.
  rw [CochainComplex.mappingCone.ext_to_iff φ 0 1 rfl]
  constructor
  · -- The `fst` projection lands in the zero degree `1` term of the single complex.
    let hzero : Limits.IsZero (((singleComplex₀).obj M).X 1) :=
      single_zero_obj_isZero_one (R := R) M
    exact (hzero.eq_of_tgt _ 0).trans (hzero.eq_of_tgt _ 0).symm
  · -- The `snd` projection sees exactly the adjugate boundary computation.
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
      (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
    suffices hmain :
        (CochainComplex.mappingCone.snd
            ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 0
              adjugate_two_term_homotopy_hom._proof_4 ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl
                ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 (-1)
                  adjugate_two_term_homotopy_hom._proof_5 ≫
              (matrixTwoTermCone A).d (-1) 0 ≫
                (CochainComplex.mappingCone.snd φ).v 0 0 rfl =
          (Matrix.det A • 𝟙 ((CochainComplex.mappingCone φ).X 0)) ≫
            (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) by
      simpa [adjugate_two_term_homotopy_hom, Category.assoc] using hmain
    have hdet :
        ModuleCat.ofHom A.adjugate.toLin' ≫ φ.f 0 =
          (Matrix.det A) • 𝟙 (((singleComplex₀).obj M).X 0) := by
      simpa [M] using adjugate_comp_single_map_eq_det_smul_id (R := R) (A := A)
    calc
      (CochainComplex.mappingCone.snd
          ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 0
            adjugate_two_term_homotopy_hom._proof_4 ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫
            (CochainComplex.mappingCone.inl
                ((singleComplex₀).map (ModuleCat.ofHom A.toLin'))).v 0 (-1)
                  adjugate_two_term_homotopy_hom._proof_5 ≫
              (matrixTwoTermCone A).d (-1) 0 ≫
                (CochainComplex.mappingCone.snd φ).v 0 0 rfl =
        (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
          ModuleCat.ofHom A.adjugate.toLin' ≫ φ.f 0 := by
            simpa [matrixTwoTermCone, endomorphismTwoTermCone, M, φ, Category.assoc] using
              mappingCone_snd_adjugate_inl_d_postcompose_snd (R := R) (A := A)
      _ = (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫
          ((Matrix.det A) • 𝟙 (((singleComplex₀).obj M).X 0)) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) ≫ k) hdet
      _ = (Matrix.det A • 𝟙 ((CochainComplex.mappingCone φ).X 0)) ≫
          (CochainComplex.mappingCone.snd φ).v 0 0 (add_zero 0) := by
            exact mappingCone_snd_postcompose_smul_id (R := R) (φ := φ) (Matrix.det A)

/-- Helper for Lemma 15.85.12: the canonical null-homotopic map on the two-term cone is exactly
the scalar endomorphism `det(A) • 𝟙`. -/
private theorem adjugate_nullHomotopicMap_eq_det_smul_id_on_two_term_cone
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A) =
      (Matrix.det A) • 𝟙 (matrixTwoTermCone A) := by
  -- Compare the two endomorphisms degreewise on the only two nonzero terms of the cone.
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi0 : i = 0
  · subst hi0
    -- Degree `0` is one of the two active terms, handled by the explicit projection computation.
    simpa using adjugate_nullHomotopicMap_f_zero_eq_det_smul_id (R := R) (A := A)
  by_cases hiNegOne : i = -1
  · subst hiNegOne
    -- Degree `-1` is the other active term, also handled explicitly.
    simpa using adjugate_nullHomotopicMap_f_negOne_eq_det_smul_id (R := R) (A := A)
  -- Away from degrees `-1` and `0`, the cone term is zero, so any two endomorphisms agree.
  let hzero : Limits.IsZero ((matrixTwoTermCone A).X i) :=
    matrix_two_term_cone_isZero_X (R := R) (A := A) hi0 hiNegOne
  have hnull :
      (Homotopy.nullHomotopicMap' (adjugate_two_term_homotopy_hom (R := R) A)).f i = 0 :=
    hzero.eq_of_tgt _ 0
  have hscalar :
      ((Matrix.det A) • 𝟙 (matrixTwoTermCone A)).f i = 0 :=
    hzero.eq_of_tgt _ 0
  exact hnull.trans hscalar.symm

/-- Helper for Lemma 15.85.12: the adjugate matrix gives a null-homotopy of
`det(A) • 𝟙` on the canonical two-term cone. -/
private theorem det_smul_id_homotopy_zero_on_two_term_cone
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Nonempty (Homotopy ((Matrix.det A) • 𝟙 (matrixTwoTermCone A)) 0) := by
  -- Route correction: identify the scalar endomorphism with the canonical null-homotopic map
  -- coming from the single supported adjugate component, then reuse `nullHomotopy'`.
  refine ⟨(Homotopy.ofEq
    (adjugate_nullHomotopicMap_eq_det_smul_id_on_two_term_cone (R := R) A).symm).trans
      (Homotopy.nullHomotopy' (adjugate_two_term_homotopy_hom (R := R) A))⟩

/-- Helper for Lemma 15.85.12: the determinant annihilates the derived image of the canonical
two-term cone attached to a matrix indexed by any finite type. -/
private theorem indexed_matrix_two_term_derived_det_endomorphism_eq_zero
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (K : DModR) (A : Matrix ι ι R)
    (hK : IsIsomorphic (DerivedCategory.Q.obj (matrixTwoTermCone A)) K) :
    Matrix.det A • 𝟙 K = 0 := by
  -- First prove the scalar action is zero on the canonical cone model itself.
  have hcanonical :
      Matrix.det A • 𝟙 (DerivedCategory.Q.obj (matrixTwoTermCone A)) = 0 := by
    exact q_obj_smul_id_eq_zero_of_homotopy_zero (R := R) (Matrix.det A)
      (det_smul_id_homotopy_zero_on_two_term_cone (R := R) A).some
  -- Then transport that vanishing across the chosen derived-category isomorphism.
  exact smul_id_eq_zero_of_isIsomorphic (R := R) (Matrix.det A) hK hcanonical

/- Domain-style sampling for Lemma 15.85.12:
- primary domain: two-term cochain complexes in `ModuleCat R`, presented as mapping cones of
  matrices and, more canonically, of endomorphisms of finite free modules, and their derived
  images;
- sampled owner declarations of the same kind:
  `Matrix.toLin'`,
  `LinearMap.det_toLin'`,
  `CochainComplex.mappingCone`,
  `CochainComplex.singleFunctor`,
  `LinearMap.det`;
- best owner abstraction: the canonical owner for the two-term complex attached to an
  endomorphism `f` of a finite free module is
  `CochainComplex.mappingCone ((CochainComplex.singleFunctor ModR 0).map (ModuleCat.ofHom f))`,
  while the source-facing statement remains the matrix presentation `R^n \xrightarrow{A} R^n`;
- primitive data: for the source-facing lemma, a matrix `A : Matrix (Fin n) (Fin n) R` and a
  chosen representation isomorphism from the derived image of the corresponding two-term complex
  to `K`;
- derived API: the supporting finite-free endomorphism bridge theorem over the canonical
  mapping-cone owner.

Source/core/bridge triage:
- `source-facing`: the textbook matrix statement that an arbitrary `K` represented by
  `R^n \xrightarrow{A} R^n` is annihilated by `det A`;
- `core/canonical`: `CochainComplex.mappingCone` of the map induced by `f` on the degree-zero
  single complex;
- `bridge/view`: the finite-free endomorphism version together with the matrix comparison
  `A.toLin'` and `LinearMap.det_toLin'`.

Accordingly, this file keeps the matrix formulation as the main numbered source-facing theorem,
and exposes the finite-free endomorphism statement only as a supporting bridge over the canonical
mapping-cone owner. -/

/-- Lemma 15.85.12: if `K` is represented by the two-term complex `R^n \xrightarrow{A} R^n`,
then multiplication by `det A` acts by zero on `K` in `D(R)`. -/
@[stacks 0G9L]
theorem matrixTwoTermDerived_det_endomorphism_eq_zero {n : ℕ}
    (K : DModR) (A : Matrix (Fin n) (Fin n) R)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom A.toLin')))) K) :
    Matrix.det A • 𝟙 K = 0 := by
  -- The indexed helper theorem already proves the source-facing matrix case.
  simpa [matrixTwoTermCone, endomorphismTwoTermCone] using
    indexed_matrix_two_term_derived_det_endomorphism_eq_zero (R := R) K A hK

/-- Helper for Lemma 15.85.12: a chosen basis conjugates an endomorphism `f` to the matrix
linear map attached to `LinearMap.toMatrix b b f`. -/
private theorem basis_conjugates_endomorphism_to_matrix
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    ModuleCat.ofHom f ≫ b.equivFun.toModuleIso.hom =
      b.equivFun.toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.toMatrix b b f).toLin' := by
  -- Evaluate both composites on an element and read off coordinates in the chosen basis.
  ext x i
  simpa [Matrix.toLin'_apply] using
    (congrFun (LinearMap.toMatrix_mulVec_repr b b f x) i).symm

/-- Helper for Lemma 15.85.12: choosing a basis identifies the canonical two-term cone of `f`
with the matrix two-term cone of its coordinate matrix. -/
private theorem endomorphism_two_term_cone_basis_isomorphic
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    IsIsomorphic (endomorphismTwoTermCone f) (matrixTwoTermCone (LinearMap.toMatrix b b f)) := by
  let e : ModuleCat.of R M ≅ ModuleCat.of R (ι → R) := b.equivFun.toModuleIso
  let φf : (singleComplex₀).obj (ModuleCat.of R M) ⟶ (singleComplex₀).obj (ModuleCat.of R M) :=
    (singleComplex₀).map (ModuleCat.ofHom f)
  let φA :
      (singleComplex₀).obj (ModuleCat.of R (ι → R)) ⟶
        (singleComplex₀).obj (ModuleCat.of R (ι → R)) :=
    (singleComplex₀).map (ModuleCat.ofHom (LinearMap.toMatrix b b f).toLin')
  let α :
      (singleComplex₀).obj (ModuleCat.of R M) ⟶
        (singleComplex₀).obj (ModuleCat.of R (ι → R)) :=
    (singleComplex₀).map e.hom
  let αinv :
      (singleComplex₀).obj (ModuleCat.of R (ι → R)) ⟶
        (singleComplex₀).obj (ModuleCat.of R M) :=
    (singleComplex₀).map e.inv
  refine ⟨?_⟩
  change CochainComplex.mappingCone φf ≅ CochainComplex.mappingCone φA
  have hα : α ≫ αinv = 𝟙 ((singleComplex₀).obj (ModuleCat.of R M)) := by
    -- The single-complex functor preserves the inverse relation of the basis equivalence.
    simpa [α, αinv, e, Functor.map_comp] using
      congrArg (fun g ↦ (singleComplex₀).map g) e.hom_inv_id
  have hαinv : αinv ≫ α = 𝟙 ((singleComplex₀).obj (ModuleCat.of R (ι → R))) := by
    -- The same functorial transport gives the inverse relation in the other direction.
    simpa [α, αinv, e, Functor.map_comp] using
      congrArg (fun g ↦ (singleComplex₀).map g) e.inv_hom_id
  have hcomm : φf ≫ α = α ≫ φA := by
    -- Map the basis-conjugation square through the degree-zero single-complex functor.
    simpa [φf, φA, α, e, Functor.map_comp] using
      congrArg (fun g ↦ (singleComplex₀).map g)
        (basis_conjugates_endomorphism_to_matrix (R := R) b f)
  have hcomm_inv : φA ≫ αinv = αinv ≫ φf := by
    -- Conjugate `hcomm` by the inverse basis map instead of redoing the coordinate calculation.
    calc
      φA ≫ αinv = (αinv ≫ α) ≫ φA ≫ αinv := by rw [hαinv]; simp
      _ = αinv ≫ (α ≫ φA) ≫ αinv := by simp [Category.assoc]
      _ = αinv ≫ (φf ≫ α) ≫ αinv := by rw [hcomm]
      _ = αinv ≫ φf ≫ (α ≫ αinv) := by simp [Category.assoc]
      _ = αinv ≫ φf := by rw [hα]; simp
  -- The cone map induced by the basis square is an isomorphism, with inverse induced by `e.inv`.
  refine {
    hom := CochainComplex.mappingCone.map φf φA α α hcomm,
    inv := CochainComplex.mappingCone.map φA φf αinv αinv hcomm_inv,
    hom_inv_id := ?_,
    inv_hom_id := ?_ }
  · -- Functoriality of `mappingCone.map` reduces the composite to the identity square.
    calc
      CochainComplex.mappingCone.map φf φA α α hcomm ≫
          CochainComplex.mappingCone.map φA φf αinv αinv hcomm_inv =
        CochainComplex.mappingCone.map φf φf (α ≫ αinv) (α ≫ αinv)
          (by rw [reassoc_of% hcomm, hcomm_inv, Category.assoc]) := by
            simpa using
              (CochainComplex.mappingCone.map_comp
                (φ₁ := φf) (φ₂ := φA) (φ₃ := φf)
                (a := α) (b := α) (a' := αinv) (b' := αinv)
                (comm := hcomm) (comm' := hcomm_inv)).symm
      _ = 𝟙 (CochainComplex.mappingCone φf) := by
            simpa [hα] using (CochainComplex.mappingCone.map_id (φ := φf))
  · -- The reverse composite is the identity for the same reason.
    calc
      CochainComplex.mappingCone.map φA φf αinv αinv hcomm_inv ≫
          CochainComplex.mappingCone.map φf φA α α hcomm =
        CochainComplex.mappingCone.map φA φA (αinv ≫ α) (αinv ≫ α)
          (by rw [reassoc_of% hcomm_inv, hcomm, Category.assoc]) := by
            simpa using
              (CochainComplex.mappingCone.map_comp
                (φ₁ := φA) (φ₂ := φf) (φ₃ := φA)
                (a := αinv) (b := αinv) (a' := α) (b' := α)
                (comm := hcomm_inv) (comm' := hcomm)).symm
      _ = 𝟙 (CochainComplex.mappingCone φA) := by
            simpa [hαinv] using (CochainComplex.mappingCone.map_id (φ := φA))

-- Proof sketch: choose a basis of the finite free module `M`, represent `f` by a matrix `A`, and
-- apply the source-facing matrix lemma above to that presentation. The determinant comparison
-- `LinearMap.det_toLin'` identifies the resulting scalar action with multiplication by
-- `LinearMap.det f`.
/-- Supporting bridge: if `K` is represented by the two-term complex `M \xrightarrow{f} M` in
degrees `-1` and `0`, where `M` is finite free over `R`, then multiplication by `det(f)` acts by
zero on `K` in `D(R)`. -/
theorem endomorphismTwoTermDerived_det_endomorphism_eq_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (K : DModR) (f : M →ₗ[R] M)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom f)))) K) :
    LinearMap.det f • 𝟙 K = 0 := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex R M) R M := Module.Free.chooseBasis R M
  letI : Fintype (Module.Free.ChooseBasisIndex R M) := inferInstance
  letI : DecidableEq (Module.Free.ChooseBasisIndex R M) := Classical.decEq _
  let A : Matrix (Module.Free.ChooseBasisIndex R M) (Module.Free.ChooseBasisIndex R M) R :=
    LinearMap.toMatrix b b f
  have hMatrix :
      Matrix.det A • 𝟙 K = 0 := by
    -- Transport the given derived-category presentation along the basis-induced cone isomorphism.
    rcases hK with ⟨eK⟩
    rcases endomorphism_two_term_cone_basis_isomorphic (R := R) b f with ⟨eCone⟩
    refine indexed_matrix_two_term_derived_det_endomorphism_eq_zero (R := R) (K := K) (A := A) ?_
    exact ⟨(DerivedCategory.Q.mapIso eCone).symm ≪≫ eK⟩
  -- The determinant of the coordinate matrix is the determinant of `f`.
  simpa [A] using hMatrix

end

end CategoryTheory
