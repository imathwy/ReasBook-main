import StacksProject_2024.Chap10.Lemma_10_110_3.MinimalResolution

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: tensoring over `R` with a subsingleton right factor gives
a subsingleton reduced tensor product. -/
lemma tensor_subsingleton_of_right_subsingleton
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M] :
    Subsingleton (TensorProduct R (ResidueField R) M) := by
  -- Reduce equality of tensor elements to equality with zero, then prove that on pure tensors.
  constructor
  intro x y
  have hzero : ∀ z : TensorProduct R (ResidueField R) M, z = 0 := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · rfl
    · intro r m
      simpa [Subsingleton.elim m (0 : M)] using
        (TensorProduct.tmul_zero (R := R) (M := ResidueField R) (N := M) r)
    · intro z₁ z₂ hz₁ hz₂
      simp [hz₁, hz₂]
  exact (hzero x).trans (hzero y).symm

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: above the length bound of a finite free complex, the
residue-field base change of the term is subsingleton. -/
lemma baseChangeTerm_subsingleton_of_bound_lt
    {e n : ℕ} (C : FiniteFreeComplex R e) (h : e < n) :
    Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X n)) := by
  -- The complex term itself is a zero object beyond the bound, hence a subsingleton module.
  let _ : Subsingleton (C.toChainComplex.X n) :=
    ModuleCat.subsingleton_of_isZero (C.isZero_toChainComplex_X n h)
  exact tensor_subsingleton_of_right_subsingleton (R := R)

/-- Helper for Chap10 Lemma 10 110 3: a displayed finite free resolution of length `e`
gives the corresponding strict projective-dimension bound for the residue field. -/
lemma residueField_hasProjectiveDimensionLT_of_finiteFreeComplex_resolution
    {e : ℕ} (C : FiniteFreeComplex R e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (e + 1) := by
  -- Package the displayed finite free complex as the source-facing bounded-resolution witness.
  have hres :
      HasFiniteFreeResolutionLengthLE R (ResidueField R) e :=
    ⟨C.toChainComplex, ρ, hρ, C.isZero_toChainComplex_X⟩
  have hpd_le :
      HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) e :=
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := R) (M := ResidueField R) e).2 hres
  -- The mathlib owner spells `≤ e` as strict projective dimension `< e + 1`.
  simpa [CategoryTheory.HasProjectiveDimensionLE] using hpd_le

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a bounded finite free resolution kills residue-field Tor
strictly above the bound. -/
lemma tor_residueField_isZero_of_finiteFreeResolutionLengthLE_lt
    {d n : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d)
    (hdn : d < n) :
    Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) := by
  rcases hres with ⟨F, π, hπ, hbound⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let T : ChainComplex (ModuleCat R) ℕ :=
    ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat R)).obj
      (ModuleCat.of R (ResidueField R))).mapHomologicalComplex (ComplexShape.down ℕ)).obj F)
  have hFzero : Limits.IsZero (F.X n) := hbound n hdn
  have hTzero : Limits.IsZero (T.X n) := by
    -- Tensoring the chosen zero term with the residue field keeps it zero.
    simpa [T, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat R)).obj
        (ModuleCat.of R (ResidueField R))).map_isZero hFzero)
  have hsc : Limits.IsZero ((T.sc n).X₂) := by
    simpa [T] using hTzero
  have hhomology : Limits.IsZero (T.homology n) := by
    -- A short complex with zero middle term has zero homology.
    simpa [T, HomologicalComplex.homology] using
      (ShortComplex.isZero_homology_of_isZero_X₂ (T.sc n) hsc)
  let e :
      ((((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) ≅ T.homology n :=
    ModuleCat.tor_iso_homology_tensorized_resolution (R := R)
      (M := ModuleCat.of R (ResidueField R)) (N := ModuleCat.of R (ResidueField R)) π n
  -- Transport the computed homology vanishing back to the public `Tor` object.
  exact (Iso.isZero_iff e).mpr hhomology

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a nontrivial self-Ext group in degree `n` obstructs
projective dimension strictly less than `n`. -/
lemma not_hasProjectiveDimensionLT_of_selfExt_nontrivial
    [CategoryTheory.HasExt (ModuleCat.{u} R)]
    {X : ModuleCat.{u} R} {n : ℕ}
    (h : Nontrivial (CategoryTheory.Abelian.Ext.{u + 1} X X n)) :
    ¬ HasProjectiveDimensionLT X n := by
  -- Projective dimension `< n` makes every Ext group in degrees at least `n` subsingleton.
  intro hpd
  have hsub : Subsingleton (CategoryTheory.Abelian.Ext.{u + 1} X X n) := by
    exact CategoryTheory.HasProjectiveDimensionLT.subsingleton X n n le_rfl X
  -- The given nontriviality is precisely the negation of that subsingleton conclusion.
  exact (not_subsingleton_iff_nontrivial.mpr h) hsub

omit [CommRing R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: over a field, tensoring an injective linear map with the
identity remains injective. -/
lemma tensorProduct_map_id_injective_of_field
    {k : Type*} [Field k]
    {A B C : Type*}
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f (LinearMap.id : C →ₗ[k] C)) := by
  -- Vector spaces are flat, so the standard tensor-product injectivity theorem applies.
  exact TensorProduct.map_injective_of_flat_flat f (LinearMap.id : C →ₗ[k] C) hf
    (fun _ _ h ↦ h)

section LocalKoszul

variable {E : Type u} [AddCommGroup E] [Module R E]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: contraction by a linear form lowers the fixed exterior
degree on pure exterior monomials. -/
private theorem contractLeft_ιMulti_mem_exteriorPower_forKoszul (φ : E →ₗ[R] R) :
    ∀ n (v : Fin (n + 1) → E),
      CliffordAlgebra.contractLeft φ (ExteriorAlgebra.ιMulti R (n + 1) v) ∈ ⋀[R]^n E
  | 0, v => by
      -- In degree one the contraction lands in the scalar part of the exterior algebra.
      simp [ExteriorAlgebra.ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one,
        ExteriorAlgebra.exteriorPower]
  | n + 1, v => by
      -- Split off the first generator and use the graded Leibniz rule for contraction.
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ <|
          ExteriorAlgebra.ιMulti_range R (n + 1) ⟨Matrix.vecTail v, rfl⟩
      · have htail :
            CliffordAlgebra.contractLeft φ
                (ExteriorAlgebra.ιMulti R (n + 1) (Matrix.vecTail v)) ∈ ⋀[R]^n E := by
          simpa using contractLeft_ιMulti_mem_exteriorPower_forKoszul φ n (Matrix.vecTail v)
        have hι : ExteriorAlgebra.ι R (v 0) ∈ ⋀[R]^1 E := by
          simp [ExteriorAlgebra.exteriorPower]
        simpa [ExteriorAlgebra.exteriorPower, add_comm] using SetLike.mul_mem_graded hι htail

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: contraction vanishes on a pure exterior monomial when
the linear form vanishes on every factor. -/
theorem contractLeft_ιMulti_eq_zero_of_apply_eq_zero (φ : E →ₗ[R] R) :
    ∀ {n : ℕ} (v : Fin n → E), (∀ k, φ (v k) = 0) →
      CliffordAlgebra.contractLeft φ (ExteriorAlgebra.ιMulti R n v) = 0
  | 0, v, hv => by
      -- In degree zero the exterior monomial is `1`, and contraction kills scalars.
      simp [ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one]
  | n + 1, v, hv => by
      -- Split off the head; both the head coefficient and the recursive tail contraction vanish.
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
      have htail :
          CliffordAlgebra.contractLeft φ
              (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) = 0 := by
        exact contractLeft_ιMulti_eq_zero_of_apply_eq_zero φ
          (Matrix.vecTail v) (fun k ↦ hv k.succ)
      rw [hv 0, htail]
      simp

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: contraction by a linear form lowers the fixed exterior
degree. -/
theorem contractLeft_mem_exteriorPower_forKoszul
    (φ : E →ₗ[R] R) (n : ℕ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ⋀[R]^(n + 1) E) :
    CliffordAlgebra.contractLeft φ x ∈ ⋀[R]^n E := by
  -- Reduce from an arbitrary element of the fixed-degree submodule to pure exterior monomials.
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n + 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨v, rfl⟩
      exact contractLeft_ιMulti_mem_exteriorPower_forKoszul φ n v
  | zero =>
      simp
  | add a b _ _ ha hb =>
      simpa [map_add] using Submodule.add_mem (⋀[R]^n E) ha hb
  | smul a y _ hy =>
      simpa [map_smul] using Submodule.smul_mem (⋀[R]^n E) a hy

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the Koszul differential on fixed exterior powers induced
by a linear form. -/
noncomputable def localKoszulDifferentialLinearMap (φ : E →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^n E :=
  (CliffordAlgebra.contractLeft φ).restrict fun _ hx ↦
    contractLeft_mem_exteriorPower_forKoszul φ n hx

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the fixed-degree Koszul differential is contraction. -/
@[simp] theorem localKoszulDifferentialLinearMap_apply
    (φ : E →ₗ[R] R) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    (localKoszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) =
      CliffordAlgebra.contractLeft φ x :=
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the Koszul differential as a morphism in `ModuleCat`. -/
noncomputable def localKoszulDifferential (φ : E →ₗ[R] R) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower (n + 1) ⟶ (ModuleCat.of R E).exteriorPower n :=
  ModuleCat.ofHom (localKoszulDifferentialLinearMap φ n)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: consecutive local Koszul differentials compose to zero. -/
theorem localKoszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    localKoszulDifferential φ (n + 1) ≫ localKoszulDifferential φ n = 0 := by
  -- Push the chain-complex square down to the contraction identity in the exterior algebra.
  change ModuleCat.ofHom
      ((localKoszulDifferentialLinearMap φ n).comp
        (localKoszulDifferentialLinearMap φ (n + 1))) = 0
  ext x
  simp [localKoszulDifferentialLinearMap, CliffordAlgebra.contractLeft_contractLeft]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the local Koszul chain complex attached to a linear form. -/
noncomputable abbrev localKoszulComplex (φ : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of ((ModuleCat.of R E).exteriorPower)
    (localKoszulDifferential φ)
    (localKoszulDifferential_sq φ)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree `n` term of the local Koszul complex is the
`n`th exterior power. -/
theorem localKoszulComplex_X (φ : E →ₗ[R] R) (n : ℕ) :
    (localKoszulComplex φ).X n = (ModuleCat.of R E).exteriorPower n :=
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the linear form `(xᵢ)` on the finite free module `R^n`. -/
noncomputable abbrev localKoszulFamilyLinearMap {n : ℕ} (x : Fin n → R) :
    (Fin n → R) →ₗ[R] R :=
  Module.piEquiv (Fin n) R R x

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the finite-family Koszul linear form has the prescribed
coefficient on each standard basis vector. -/
theorem localKoszulFamilyLinearMap_basis {n : ℕ} (x : Fin n → R) (i : Fin n) :
    localKoszulFamilyLinearMap x (Pi.basisFun R (Fin n) i) = x i := by
  -- Expand `Module.piEquiv` as the finite linear combination over the standard coordinates.
  rw [localKoszulFamilyLinearMap, Module.piEquiv_apply_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.basisFun]
  · intro j _ hji
    simp [Pi.basisFun, hji]
  · intro hi
    simp at hi

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: if the finite family lies in the maximal ideal, then the
associated Koszul linear form also lands in the maximal ideal. -/
theorem localKoszulFamilyLinearMap_mem_maximalIdeal {n : ℕ}
    (x : Fin n → maximalIdeal R) (v : Fin n → R) :
    localKoszulFamilyLinearMap (fun i ↦ (x i : R)) v ∈ maximalIdeal R := by
  -- The linear form is the finite sum of coefficients times elements already in `maximalIdeal R`.
  rw [localKoszulFamilyLinearMap, Module.piEquiv_apply_apply]
  exact Submodule.sum_mem (maximalIdeal R) (fun i _ ↦
    Submodule.smul_mem _ (v i) (x i).property)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the Koszul linear form attached to maximal-ideal lifts
vanishes after passing to the residue field. -/
theorem residue_localKoszulFamilyLinearMap_eq_zero {n : ℕ}
    (x : Fin n → maximalIdeal R) (v : Fin n → R) :
    IsLocalRing.residue R (localKoszulFamilyLinearMap (fun i ↦ (x i : R)) v) = 0 := by
  -- The residue map kills exactly the maximal ideal.
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (localKoszulFamilyLinearMap_mem_maximalIdeal x v)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the local Koszul complex on a finite family `x : Fin n → R`. -/
noncomputable abbrev localKoszulComplexOn {n : ℕ} (x : Fin n → R) :
    ChainComplex (ModuleCat R) ℕ :=
  localKoszulComplex (localKoszulFamilyLinearMap x)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree `i` term of the finite-family local Koszul
complex is the corresponding exterior power of `R^n`. -/
theorem localKoszulComplexOn_X {n : ℕ} (x : Fin n → R) (i : ℕ) :
    (localKoszulComplexOn x).X i = (ModuleCat.of R (Fin n → R)).exteriorPower i :=
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: every term of the finite-family local Koszul complex is a
free `R`-module. -/
theorem localKoszulComplexOn_termwiseFree {n : ℕ} (x : Fin n → R) :
    ChainComplex.IsTermwiseFree (localKoszulComplexOn x) := by
  -- The standard basis of `R^n` gives a basis of each exterior power.
  intro i
  change Module.Free R (⋀[R]^i (Fin n → R))
  infer_instance

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: every term of the finite-family local Koszul complex is a
finite `R`-module. -/
theorem localKoszulComplexOn_termwiseFinite {n : ℕ} (x : Fin n → R) :
    ChainComplex.IsTermwiseFinite (localKoszulComplexOn x) := by
  -- Exterior powers of the finite free module `R^n` are finite.
  intro i
  change Module.Finite R (⋀[R]^i (Fin n → R))
  infer_instance

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in degree one, the Koszul contraction followed by
`⋀^0 ≃ R` is the original linear form. -/
theorem localKoszulDifferentialLinearMap_zero_oneEquiv (φ : E →ₗ[R] R) (v : E) :
    (exteriorPower.zeroEquiv R E)
      (localKoszulDifferentialLinearMap φ 0 ((exteriorPower.oneEquiv R E).symm v)) =
        φ v := by
  -- First identify the contracted one-fold generator with the scalar sitting in degree zero.
  have hterm :
      localKoszulDifferentialLinearMap φ 0 ((exteriorPower.oneEquiv R E).symm v) =
        (⟨algebraMap R (ExteriorAlgebra R E) (φ v), by
          simp [ExteriorAlgebra.exteriorPower]⟩ : ⋀[R]^0 E) := by
    ext
    simp [localKoszulDifferentialLinearMap, exteriorPower.oneEquiv_symm_apply,
      exteriorPower.ιMulti_apply_coe, CliffordAlgebra.contractLeft_ι]
  -- The degree-zero equivalence sends the scalar copy of `R` back to that scalar.
  have hscalar :
      (exteriorPower.zeroEquiv R E)
        (⟨algebraMap R (ExteriorAlgebra R E) (φ v), by
          simp [ExteriorAlgebra.exteriorPower]⟩ : ⋀[R]^0 E) = φ v := by
    have hsymm :
        (⟨algebraMap R (ExteriorAlgebra R E) (φ v), by
          simp [ExteriorAlgebra.exteriorPower]⟩ : ⋀[R]^0 E) =
            (exteriorPower.zeroEquiv R E).symm (φ v) := by
      rw [exteriorPower.zeroEquiv_symm_apply]
      ext
      simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
        Algebra.algebraMap_eq_smul_one]
    simpa using congrArg (exteriorPower.zeroEquiv R E) hsymm
  rw [hterm]
  exact hscalar

end LocalKoszul

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-one Koszul differential followed by the
residue-field degree-zero projection is zero for maximal-ideal coefficients. -/
lemma localKoszulAugmentation_d_comp_zero {n : ℕ} (x : Fin n → maximalIdeal R) :
    ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).d 1 0) ≫
      ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap) = 0 := by
  -- The degree-one Koszul differential is contraction by the family linear form, and the residue
  -- map kills all values because the coefficients lie in the maximal ideal.
  apply ModuleCat.hom_ext
  ext z
  let v : Fin n → R := (exteriorPower.oneEquiv R (Fin n → R)) z
  have hz : (exteriorPower.oneEquiv R (Fin n → R)).symm v = z := by
    simp [v]
  have hres :
      IsLocalRing.residue R (localKoszulFamilyLinearMap (fun i ↦ (x i : R)) v) = 0 :=
    residue_localKoszulFamilyLinearMap_eq_zero (R := R) x v
  change
    (ModuleCat.Hom.hom
        (((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).d 1 0) ≫
          ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
            (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap))) z = (0 : ResidueField R)
  calc
    (ModuleCat.Hom.hom
        (((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).d 1 0) ≫
          ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
            (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap))) z =
        IsLocalRing.residue R
          ((exteriorPower.zeroEquiv R (Fin n → R))
            (localKoszulDifferentialLinearMap
              (localKoszulFamilyLinearMap (fun i ↦ (x i : R))) 0 z)) := by
          rfl
    _ = IsLocalRing.residue R (localKoszulFamilyLinearMap (fun i ↦ (x i : R)) v) := by
          rw [← hz]
          rw [localKoszulDifferentialLinearMap_zero_oneEquiv]
    _ = 0 := hres

/-- Helper for Chap10 Lemma 10 110 3: the canonical augmentation from the local Koszul complex on
maximal-ideal lifts to the residue-field single complex. -/
noncomputable def localKoszulAugmentation {n : ℕ} (x : Fin n → maximalIdeal R) :
    localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ moduleSingle[R] (ResidueField R) :=
  (ChainComplex.toSingle₀Equiv
      (localKoszulComplexOn (R := R) (fun i ↦ (x i : R)))
      (ModuleCat.of R (ResidueField R))).symm
    ⟨ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap),
      localKoszulAugmentation_d_comp_zero (R := R) x⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-zero component of the local Koszul augmentation is
the residue map after the canonical `⋀^0 ≃ R` identification. -/
theorem localKoszulAugmentation_f_zero {n : ℕ} (x : Fin n → maximalIdeal R) :
    (localKoszulAugmentation (R := R) x).f 0 =
      ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap) := by
  -- Read the chosen degree-zero component back from `toSingle₀Equiv`.
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the local Koszul augmentation has zero positive-degree
components. -/
theorem localKoszulAugmentation_f_succ {n : ℕ} (x : Fin n → maximalIdeal R) (i : ℕ) :
    (localKoszulAugmentation (R := R) x).f (i + 1) = 0 := by
  -- The target single complex has zero object in every positive degree.
  exact moduleSingle_component_eq_zero_succ (R := R) (localKoszulAugmentation (R := R) x) i

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the residue field tensored with itself over the local ring
is nontrivial. -/
lemma residueField_tensor_self_nontrivial :
    Nontrivial (TensorProduct R (ResidueField R) (ResidueField R)) := by
  have hsmul : maximalIdeal R • (⊤ : Submodule R (ResidueField R)) = ⊥ := by
    -- The maximal ideal is exactly the annihilator of the residue field, so quotienting by its
    -- scalar multiples leaves the residue field unchanged.
    rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
    intro x hx
    exact Module.mem_annihilator.mpr fun y ↦ by
      have hx0 : algebraMap R (ResidueField R) x = 0 := by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (IsLocalRing.residue_eq_zero_iff (R := R) x).mpr hx
      rw [Algebra.smul_def, hx0, zero_mul]
  let e : (ResidueField R ⧸ maximalIdeal R • (⊤ : Submodule R (ResidueField R))) ≃ₗ[R]
      ResidueField R :=
    Submodule.quotEquivOfEqBot _ hsmul
  letI : Nontrivial
      (ResidueField R ⧸ maximalIdeal R • (⊤ : Submodule R (ResidueField R))) :=
    e.toEquiv.nontrivial
  -- The standard quotient-tensor equivalence transfers nontriviality back to `κ ⊗[R] κ`.
  exact (TensorProduct.quotTensorEquivQuotSMul (ResidueField R)
    (maximalIdeal R)).toEquiv.nontrivial

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the zeroth self-Tor of the residue field is nonzero. -/
lemma residueField_tor_zero_not_isZero :
    ¬ Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat R) 0).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) := by
  let e :
      ((((CategoryTheory.Tor (ModuleCat R) 0).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) ≅
        ModuleCat.of R (TensorProduct R (ResidueField R) (ResidueField R)) := by
    -- In degree zero, `Tor` is the ordinary tensor product.
    simpa [CategoryTheory.Tor] using
      (((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat R)).obj
        (ModuleCat.of R (ResidueField R))).leftDerivedZeroIsoSelf.app
          (ModuleCat.of R (ResidueField R)))
  intro hzero
  have htensorZero :
      Limits.IsZero (ModuleCat.of R (TensorProduct R (ResidueField R) (ResidueField R))) :=
    (Iso.isZero_iff e).mp hzero
  have hsub : Subsingleton (TensorProduct R (ResidueField R) (ResidueField R)) :=
    (ModuleCat.isZero_iff_subsingleton
      (M := ModuleCat.of R (TensorProduct R (ResidueField R) (ResidueField R)))).1 htensorZero
  -- This contradicts the nontriviality of the tensor square just proved.
  exact (not_subsingleton_iff_nontrivial.mpr
    (residueField_tensor_self_nontrivial (R := R))) hsub

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in a finite free complex of length `d + 1`, the
residue-field base change of degree `d + 2` is subsingleton. -/
lemma topBaseChangeTerm_subsingleton_of_shortComplex
    {d : ℕ} (C : FiniteFreeComplex R (d + 1)) :
    Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) := by
  -- Package the strict top-degree inequality used in the final contradiction.
  exact baseChangeTerm_subsingleton_of_bound_lt (R := R) C (Nat.lt_succ_self (d + 1))


end
