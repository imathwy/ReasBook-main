import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Pointwise TensorProduct

universe u v w

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section

attribute [local instance] Classical.decEq

/-- Helper for Exercise 15-15.2-6: a unimodular Gram matrix induces an integral pairing
equivalence with the coordinate functions on the chosen basis. This is the determinant-unit
version used by the dual-lattice route before positivity upgrades the sign. -/
theorem pairing_linear_equiv_basis_of_isUnit_det
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E)
    (hdet : IsUnit (Matrix.det (B.toMatrix b))) :
    ∃ e : E ≃ₗ[ℤ] (Fin n → ℤ), ∀ x i, e x i = B x (b i) := by
  let pairing : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro m x
        ext i
        simp }
  have hmatrix :
      LinearMap.toMatrix b (Pi.basisFun ℤ (Fin n)) pairing = Matrix.transpose (B.toMatrix b) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    simp [pairing]
  have hpairing_det :
      IsUnit (Matrix.det (LinearMap.toMatrix b (Pi.basisFun ℤ (Fin n)) pairing)) := by
    rw [hmatrix, Matrix.det_transpose]
    exact hdet
  refine ⟨LinearEquiv.ofIsUnitDet hpairing_det, ?_⟩
  intro x i
  rfl

/-- Helper for Exercise 15-15.2-6: a unimodular Gram matrix induces an integral pairing
equivalence with the coordinate functions on the chosen basis. -/
theorem pairing_linear_equiv_basis
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E)
    (hdet : Matrix.det (B.toMatrix b) = 1) :
    ∃ e : E ≃ₗ[ℤ] (Fin n → ℤ), ∀ x i, e x i = B x (b i) := by
  exact pairing_linear_equiv_basis_of_isUnit_det (b := b) (B := B) (by simpa [hdet])

/-- Helper for Exercise 15-15.2-6: a unimodular symmetric Gram matrix over `ℤ` realizes any
prescribed basis pairings modulo `2`. -/
theorem exists_vector_with_prescribed_pairings_mod_two_basis
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hdet : Matrix.det (B.toMatrix b) = 1) (d : Fin n → ZMod 2) :
    ∃ x : E, ∀ i, ((B x (b i) : ℤ) : ZMod 2) = d i := by
  rcases pairing_linear_equiv_basis (b := b) (B := B) hdet with ⟨e, he⟩
  let _ := hB_symm
  choose c hc using fun i : Fin n ↦ ZMod.intCast_surjective (d i)
  refine ⟨e.symm c, ?_⟩
  intro i
  rw [← he (e.symm c) i]
  have hcoord : e (e.symm c) i = c i := by
    simpa using congrArg (fun f : Fin n → ℤ ↦ f i) (e.apply_symm_apply c)
  rw [hcoord]
  exact hc i

/-- Helper for Exercise 15-15.2-6: if every basis coordinate is even, then the vector already
lies in `2E`. -/
theorem mem_two_mul_of_even_repr_basis
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) {z : E}
    (hz : ∀ i, Even (b.repr z i)) :
    z ∈ (2 •ℤ E) := by
  classical
  choose c hc using hz
  let y : E := b.equivFun.symm c
  have hz_eq : z = (2 : ℤ) • y := by
    apply b.equivFun.injective
    ext i
    calc
      b.equivFun z i = c i + c i := by
        simpa [Module.Basis.equivFun_apply] using hc i
      _ = (2 : ℤ) * c i := by
        ring
      _ = (2 : ℤ) * b.equivFun y i := by
        congr 1
        simpa [y] using
          (congrArg (fun f : Fin n → ℤ ↦ f i) (b.equivFun.apply_symm_apply c)).symm
      _ = b.equivFun ((2 : ℤ) • y) i := by
        simp
  rw [show (2 •ℤ E) = Representation.primeIdeal 2 • (⊤ : Submodule ℤ E) by rfl,
    Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
  refine ⟨y, by simp, ?_⟩
  calc
    ((LinearMap.lsmul ℤ E) (2 : ℤ)) y = (2 : ℤ) • y := by
      rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (2 : ℤ)) (b := y)]
      simp [LinearMap.lsmul_apply]
    _ = z := hz_eq.symm

/-- Helper for Exercise 15-15.2-6: in a unimodular symmetric basis, a vector whose pairings with
the basis are all even lies in `2E`. -/
theorem mem_two_mul_of_pairings_even_basis_of_isUnit_det
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hdet : IsUnit (Matrix.det (B.toMatrix b))) {z : E}
    (hz : ∀ i, B z (b i) ≡ 0 [ZMOD 2]) :
    z ∈ (2 •ℤ E) := by
  rcases pairing_linear_equiv_basis_of_isUnit_det (b := b) (B := B) hdet with ⟨e, he⟩
  have hz_even : ∀ i, Even (e z i) := by
    intro i
    rw [he z i]
    exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp (hz i))
  choose c hc using hz_even
  let y : E := e.symm c
  have hz_eq : z = (2 : ℤ) • y := by
    apply e.injective
    ext i
    calc
      e z i = c i + c i := by
        simpa [Module.Basis.equivFun_apply] using hc i
      _ = (2 : ℤ) * c i := by
        ring
      _ = (2 : ℤ) * e y i := by
        congr 1
        simpa [y] using (congrArg (fun f : Fin n → ℤ ↦ f i) (e.apply_symm_apply c)).symm
      _ = e ((2 : ℤ) • y) i := by
        simp
  rw [show (2 •ℤ E) = Representation.primeIdeal 2 • (⊤ : Submodule ℤ E) by rfl,
    Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
  refine ⟨y, by simp, ?_⟩
  calc
    ((LinearMap.lsmul ℤ E) (2 : ℤ)) y = (2 : ℤ) • y := by
      rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (2 : ℤ)) (b := y)]
      simp [LinearMap.lsmul_apply]
    _ = z := hz_eq.symm

/-- Helper for Exercise 15-15.2-6: in a unimodular symmetric basis, a vector whose pairings with
the basis are all even lies in `2E`. -/
theorem mem_two_mul_of_pairings_even_basis
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hdet : Matrix.det (B.toMatrix b) = 1) {z : E}
    (hz : ∀ i, B z (b i) ≡ 0 [ZMOD 2]) :
    z ∈ (2 •ℤ E) := by
  exact mem_two_mul_of_pairings_even_basis_of_isUnit_det
    (b := b) (B := B) hB_symm (by simpa [hdet]) hz

/-- Helper for Exercise 15-15.2-6: every element of `ZMod 2` is idempotent under squaring. -/
theorem zmod_two_square_eq_self (a : ZMod 2) : a ^ 2 = a := by
  simpa using (ZMod.pow_card a)

/-- Helper for Exercise 15-15.2-6: the polar form of a symmetric integral bilinear form vanishes
after reduction modulo `2`. -/
theorem polar_toQuadraticMap_eq_zero_mod_two_of_isSymm
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (u v : E) :
    ((QuadraticMap.polar B.toQuadraticMap u v : ℤ) : ZMod 2) = 0 := by
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  have hsymm : B v u = B u v := hB_symm.eq v u
  rw [hsymm, ← two_mul, Int.cast_mul]
  have htwo : ((2 : ℤ) : ZMod 2) = 0 := by
    decide
  rw [htwo, zero_mul]

/-- Helper for Exercise 15-15.2-6: modulo `2`, the value `B(y,y)` is the sum of the basis
diagonal values weighted by the coordinates of `y`. -/
theorem basis_diagonal_values_mod_two
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (y : E) :
    ((B y y : ℤ) : ZMod 2) =
      ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B (b i) (b i) : ℤ) : ZMod 2) := by
  let q : E → ZMod 2 := fun z ↦ ((B z z : ℤ) : ZMod 2)
  have hq_add : ∀ u v, q (u + v) = q u + q v := by
    intro u v
    have hpolar : ((QuadraticMap.polar B.toQuadraticMap u v : ℤ) : ZMod 2) = 0 :=
      polar_toQuadraticMap_eq_zero_mod_two_of_isSymm (E := E) B hB_symm u v
    unfold QuadraticMap.polar at hpolar
    have hpolar' : q (u + v) - q u - q v = 0 := by
      simpa [q] using hpolar
    have h' := congrArg (fun t : ZMod 2 ↦ t + q u + q v) hpolar'
    abel_nf at h'
    exact h'
  have hq_zsmul : ∀ (m : ℤ) (z : E), q (m • z) = ((m : ZMod 2)) * q z := by
    intro m z
    dsimp [q]
    calc
      ((B (m • z) (m • z) : ℤ) : ZMod 2) =
          (((m * m : ℤ) : ZMod 2) * ((B z z : ℤ) : ZMod 2)) := by
            rw [show B (m • z) (m • z) = (m * m) * B z z by simp [mul_assoc], Int.cast_mul]
      _ = ((m : ZMod 2) * (m : ZMod 2)) * ((B z z : ℤ) : ZMod 2) := by
            rw [Int.cast_mul]
      _ = ((m : ZMod 2)) * ((B z z : ℤ) : ZMod 2) := by
            rw [show ((m : ZMod 2) * (m : ZMod 2)) = (m : ZMod 2) by
              simpa [pow_two] using zmod_two_square_eq_self (m : ZMod 2)]
  have hsum (c : Fin n → ℤ) (s : Finset (Fin n)) :
      q (Finset.sum s (fun i => c i • b i)) =
        Finset.sum s (fun i => ((c i : ℤ) : ZMod 2) * q (b i)) := by
    refine Finset.induction_on s ?_ ?_
    · simp [q]
    · intro i s hi hs
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hq_add, hs, hq_zsmul]
  have hy : Finset.sum Finset.univ (fun i => b.equivFun y i • b i) = y := by
    apply b.repr.injective
    simp
  calc
    q y = q (Finset.sum Finset.univ (fun i => b.equivFun y i • b i)) := by
      rw [hy]
    _ = Finset.sum Finset.univ (fun i => ((b.equivFun y i : ℤ) : ZMod 2) * q (b i)) :=
      hsum (b.equivFun y) Finset.univ
    _ = ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B (b i) (b i) : ℤ) : ZMod 2) := by
      simp [q]

/-- Helper for Exercise 15-15.2-6: for a symmetric integral form, it is enough to check the
characteristic congruence on a basis. -/
theorem isCharacteristicModTwo_of_basis_diagonal_congruence
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    {x : E} (hx : ∀ i, B (b i) (b i) ≡ B x (b i) [ZMOD 2]) :
    B.IsCharacteristicModTwo x := by
  intro y
  have hyy :=
    basis_diagonal_values_mod_two (E := E) b B hB_symm y
  have hxy :
      ((B x y : ℤ) : ZMod 2) =
        ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B x (b i) : ℤ) : ZMod 2) := by
    let f : E →ₗ[ℤ] ℤ := B x
    have hy : Finset.sum Finset.univ (fun i => b.equivFun y i • b i) = y := by
      apply b.repr.injective
      simp
    calc
      ((B x y : ℤ) : ZMod 2) = ((f y : ℤ) : ZMod 2) := by
        rfl
      _ = ((f (Finset.sum Finset.univ (fun i => b.equivFun y i • b i)) : ℤ) : ZMod 2) := by
            rw [hy]
      _ = ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B x (b i) : ℤ) : ZMod 2) := by
            simp [f, map_sum, Int.cast_mul, mul_comm]
  have hdiag : ∀ i, ((B (b i) (b i) : ℤ) : ZMod 2) = ((B x (b i) : ℤ) : ZMod 2) := by
    intro i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa [Int.modEq_iff_dvd] using hx i
  have hcast : ((B y y : ℤ) : ZMod 2) = ((B x y : ℤ) : ZMod 2) := by
    calc
      ((B y y : ℤ) : ZMod 2) =
          ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B (b i) (b i) : ℤ) : ZMod 2) := hyy
      _ = ∑ i, ((b.equivFun y i : ℤ) : ZMod 2) * ((B x (b i) : ℤ) : ZMod 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hdiag i]
      _ = ((B x y : ℤ) : ZMod 2) := hxy.symm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  rw [Int.modEq_iff_dvd]
  simpa [sub_eq_add_neg, add_comm] using hcast

end
