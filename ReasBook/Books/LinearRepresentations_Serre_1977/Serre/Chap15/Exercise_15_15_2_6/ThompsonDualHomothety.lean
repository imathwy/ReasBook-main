import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonPrimeSmith

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: if every value of an integral bilinear form is divisible by
`m`, then dividing every value by `m` again produces an integral bilinear form whose positive
rescaling recovers the original form. -/
theorem exists_dividedBilinForm_of_dvd
    (B : BilinForm ℤ E) (m : ℕ)
    (hdiv : ∀ x y : E, (m : ℤ) ∣ B x y) :
    ∃ B' : BilinForm ℤ E, B = (m : ℤ) • B' := by
  let B' : BilinForm ℤ E :=
    LinearMap.mk₂ ℤ (fun x y ↦ B x y / (m : ℤ))
      (by
        intro x₁ x₂ y
        -- Divisibility in the first variable makes division compatible with addition.
        simpa [map_add] using
          Int.add_ediv_of_dvd_left (hdiv x₁ y) (b := B x₂ y) (c := (m : ℤ)))
      (by
        intro a x y
        -- Dividing after scaling is the same as scaling after dividing because `m` still divides
        -- the underlying pairing value.
        simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
          Int.mul_ediv_assoc a (hdiv x y))
      (by
        intro x y₁ y₂
        -- The same divisibility argument gives additivity in the second variable.
        simpa [map_add] using
          Int.add_ediv_of_dvd_left (hdiv x y₁) (b := B x y₂) (c := (m : ℤ)))
      (by
        intro a x y
        -- Right-linearity is proved by the same division-through-scaling identity.
        simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
          Int.mul_ediv_assoc a (hdiv x y))
  refine ⟨B', ?_⟩
  ext x y
  -- Multiplying the divided form back by `m` restores the original pairing value.
  simpa [B', zsmul_eq_mul, mul_comm] using
    (Int.ediv_mul_cancel (hdiv x y)).symm

/-- Helper for Exercise 15-15.2-6: a symmetric integral matrix whose quadratic form is positive on
all nonzero integral vectors has positive determinant. The proof is the algebraic determinant-sign
bridge used in Serre's part `(b)`: extend the matrix to `ℚ`, clear denominators to transfer
positivity to rational vectors, diagonalize the rational symmetric form, and compare determinants
with the diagonal Gram matrix. -/
theorem intMatrix_det_pos_of_isSymm_of_pos_on_integer_vectors
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM_symm : M.IsSymm)
    (hM_pos : ∀ z : Fin n → ℤ, z ≠ 0 → 0 < dotProduct z (M.mulVec z)) :
    0 < Matrix.det M := by
  classical
  let MQ : Matrix (Fin n) (Fin n) ℚ := M.map (Int.castRingHom ℚ)
  let BQ : BilinForm ℚ (Fin n → ℚ) := Matrix.toBilin' MQ
  have hMQ_symm : MQ.IsSymm := by
    exact hM_symm.map (Int.castRingHom ℚ)
  have hBQ_symm : BQ.IsSymm := by
    refine ⟨?_⟩
    intro x y
    calc
      BQ x y = dotProduct x (MQ.mulVec y) := by simp [BQ, Matrix.toBilin'_apply']
      _ = dotProduct (Matrix.vecMul x MQ) y := by rw [Matrix.dotProduct_mulVec]
      _ = dotProduct (MQ.transpose.mulVec x) y := by rw [Matrix.mulVec_transpose]
      _ = dotProduct (MQ.mulVec x) y := by rw [hMQ_symm.eq]
      _ = dotProduct y (MQ.mulVec x) := dotProduct_comm _ _
      _ = BQ y x := by simp [BQ, Matrix.toBilin'_apply']
  have hBQ_pos : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < BQ x x := by
    intro x hx
    let A : Matrix (Fin n) Unit ℚ := fun i _ ↦ x i
    let z : Fin n → ℤ := fun i ↦ A.num i ()
    let d : ℕ := A.den
    have hdne_nat : d ≠ 0 := by simpa [d] using Matrix.den_ne_zero A
    have hdpos_nat : 0 < d := Nat.pos_of_ne_zero hdne_nat
    have hdx : (fun i ↦ ((d : ℚ) * x i)) = fun i ↦ (z i : ℚ) := by
      ext i
      have h := Matrix.num_div_den A i ()
      have hdne : (A.den : ℚ) ≠ 0 := by exact_mod_cast Matrix.den_ne_zero A
      dsimp [A] at hdne
      dsimp [A, z, d] at h ⊢
      rw [← h]
      field_simp [hdne]
    have hz_ne : z ≠ 0 := by
      intro hz
      apply hx
      ext i
      have hi : (d : ℚ) * x i = 0 := by
        simpa [hz] using congrFun hdx i
      exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast hdne_nat)
    have hy : (d : ℚ) • x = fun i ↦ (z i : ℚ) := by
      ext i
      exact congrFun hdx i
    have hscaled_cast :
        BQ ((d : ℚ) • x) ((d : ℚ) • x) =
          ((dotProduct z (M.mulVec z) : ℤ) : ℚ) := by
      rw [hy]
      simp [BQ, MQ, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Finset.mul_sum]
    have hscaled_pos : 0 < BQ ((d : ℚ) • x) ((d : ℚ) • x) := by
      rw [hscaled_cast]
      exact_mod_cast hM_pos z hz_ne
    have hscaled_form :
        BQ ((d : ℚ) • x) ((d : ℚ) • x) = (d : ℚ) * (d : ℚ) * BQ x x := by
      simp [mul_assoc]
    rw [hscaled_form] at hscaled_pos
    have hdq : 0 < (d : ℚ) := by exact_mod_cast hdpos_nat
    exact pos_of_mul_pos_right hscaled_pos (mul_pos hdq hdq).le
  have hBQ_symm_linear : LinearMap.IsSymm BQ := ⟨fun x y ↦ hBQ_symm.eq x y⟩
  obtain ⟨v0, hv0⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis
      (K := ℚ) (V := Fin n → ℚ) (B := BQ) hBQ_symm_linear
  have hfr : Module.finrank ℚ (Fin n → ℚ) = n := Module.finrank_fin_fun ℚ
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hfr
  let v : Module.Basis (Fin n) ℚ (Fin n → ℚ) := v0.reindex e
  have hv0' : ∀ i j, i ≠ j → BQ (v0 i) (v0 j) = 0 := by
    intro i j hij
    exact hv0 hij
  have hv : ∀ i j : Fin n, i ≠ j → BQ (v i) (v j) = 0 := by
    intro i j hij
    simpa [v] using
      hv0' (e.symm i) (e.symm j) (by intro h; exact hij (e.symm.injective h))
  let std : Module.Basis (Fin n) ℚ (Fin n → ℚ) := Pi.basisFun ℚ (Fin n)
  let C : Matrix (Fin n) (Fin n) ℚ := std.toMatrix v
  have hstd_matrix : BQ.toMatrix std = MQ := by
    ext i j
    simp [BQ, std, MQ]
  have hchange : C.transpose * MQ * C = BQ.toMatrix v := by
    dsimp [C]
    rw [← hstd_matrix]
    simp [std, LinearMap.BilinForm.toMatrix_mul_basis_toMatrix]
  have hdiag : BQ.toMatrix v = Matrix.diagonal (fun i ↦ BQ (v i) (v i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.BilinForm.toMatrix_apply]
    · have hvij : BQ (v i) (v j) = 0 := hv i j hij
      simp [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply_ne _ hij, hvij]
  have hdiag_det_pos : 0 < Matrix.det (BQ.toMatrix v) := by
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_pos (fun i _ ↦ hBQ_pos (v i) (Module.Basis.ne_zero v i))
  have hCdet_ne : Matrix.det C ≠ 0 := by
    have hunit : IsUnit (std.det v) := std.isUnit_det v
    rw [Module.Basis.det_apply] at hunit
    simpa [C] using hunit.ne_zero
  have hCdet_sq_pos : 0 < Matrix.det C * Matrix.det C := mul_self_pos.mpr hCdet_ne
  have hdet_relation :
      Matrix.det (BQ.toMatrix v) = (Matrix.det C * Matrix.det C) * Matrix.det MQ := by
    have h := congrArg Matrix.det hchange
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm
  have hdetMQ_pos : 0 < Matrix.det MQ := by
    rw [hdet_relation] at hdiag_det_pos
    exact pos_of_mul_pos_right hdiag_det_pos hCdet_sq_pos.le
  have hmapdet : Matrix.det MQ = ((Matrix.det M : ℤ) : ℚ) := by
    dsimp [MQ]
    simpa using (Int.cast_det (R := ℚ) M).symm
  have hdet_cast_pos : 0 < ((Matrix.det M : ℤ) : ℚ) := by
    simpa [← hmapdet] using hdetMQ_pos
  exact_mod_cast hdet_cast_pos

/-- Helper for Exercise 15-15.2-6: the last sign step in part `(b)` reduces to the claim that a
symmetric positive-definite integral Gram matrix has nonnegative determinant. -/
theorem pairingMatrix_det_nonneg_of_isSymm_of_posDef
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) :
    0 ≤ Matrix.det (B.toMatrix b) := by
  have hM_symm : (B.toMatrix b).IsSymm := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, hB_symm.eq]
  have hM_pos :
      ∀ z : Fin n → ℤ, z ≠ 0 → 0 < dotProduct z ((B.toMatrix b).mulVec z) := by
    intro z hz
    have hzE : b.equivFun.symm z ≠ 0 := by
      exact (LinearEquiv.map_ne_zero_iff b.equivFun.symm).mpr hz
    have hpos : 0 < B (b.equivFun.symm z) (b.equivFun.symm z) := by
      simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hB_pos (b.equivFun.symm z) hzE
    have hdot :
        dotProduct z ((B.toMatrix b).mulVec z) =
          B (b.equivFun.symm z) (b.equivFun.symm z) := by
      simpa using LinearMap.BilinForm.dotProduct_toMatrix_mulVec (b := b) B z z
    simpa [hdot] using hpos
  exact
    (intMatrix_det_pos_of_isSymm_of_pos_on_integer_vectors
      (M := B.toMatrix b) hM_symm hM_pos).le

/-- Helper for Exercise 15-15.2-6: once the pairing image is the literal diagonal lattice
`mℤ^n`, the form is an integral multiple of a determinant-one form. -/
theorem dualIntegralLatticeIsRationalHomothety_of_pairingImage_eq_diagonal
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (m : ℕ) (hm : 0 < m)
    (hrange :
      pairingMap.range =
        Submodule.pi Set.univ
          (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))) :
    B.DualIntegralLatticeIsRationalHomothety := by
  let M : Submodule ℤ (Fin n → ℤ) :=
    Submodule.pi Set.univ
      (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))
  have hpairing_dvd : ∀ x y : E, (m : ℤ) ∣ B x y := by
    -- The explicit range description gives the required divisibility on every pairing value.
    intro x y
    exact
      pairingValue_dvd_of_pairingImage_eq_diagonal
        (B := B) (b := b) pairingMap hpairing m (by simpa [M] using hrange) x y
  obtain ⟨B', hscale⟩ :=
    exists_dividedBilinForm_of_dvd (B := B) (m := m) hpairing_dvd
  have hB'_symm : B'.IsSymm := by
    -- Symmetry survives after dividing the form by the positive integer `m`.
    refine ⟨?_⟩
    intro x y
    have hm_ne : (m : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    apply mul_left_cancel₀ hm_ne
    calc
      (m : ℤ) * B' x y = B x y := by
            simpa [hscale, zsmul_eq_mul, mul_comm] using
              (congrArg (fun T : BilinForm ℤ E ↦ T x y) hscale).symm
      _ = B y x := hB_symm.eq x y
      _ = (m : ℤ) * B' y x := by
            simpa [hscale, zsmul_eq_mul, mul_comm] using
              (congrArg (fun T : BilinForm ℤ E ↦ T y x) hscale)
  have hB'_pos : B'.toQuadraticMap.PosDef := by
    intro x hx
    have hm_pos_int : 0 < (m : ℤ) := by
      exact_mod_cast hm
    have hscaled : 0 < (m : ℤ) * B' x x := by
      -- Rewrite the positive-definite hypothesis on `B` through the displayed scaling equality.
      calc
        0 < B x x := by
              simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hB_pos x hx
        _ = (m : ℤ) * B' x x := by
              simpa [hscale, zsmul_eq_mul, mul_comm] using
                (congrArg (fun T : BilinForm ℤ E ↦ T x x) hscale)
    -- A positive multiple with positive coefficient forces the rescaled diagonal value to be
    -- positive as well.
    simpa [LinearMap.BilinMap.toQuadraticMap_apply] using
      pos_of_mul_pos_right hscaled hm_pos_int.le
  let pairingMap' : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B' x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        simp }
  have hpairing' : ∀ x : E, ∀ i : Fin n, pairingMap' x i = B' x (b i) := by
    intro x i
    rfl
  have hpairing'_injective : Function.Injective pairingMap' := by
    -- The rescaled form is still positive definite, so its coordinate pairing map is injective.
    exact
      pairingCoordinateMap_injective
        (E := E) (B := B') hB'_symm hB'_pos b pairingMap' hpairing'
  have hpairing'_range_top : pairingMap'.range = ⊤ := by
    apply eq_top_iff.mpr
    intro z hz
    let w : Fin n → ℤ := fun i ↦ (m : ℤ) * z i
    have hw_mem : w ∈ M := by
      -- The scaled coordinate vector obviously lies in the diagonal lattice `mℤ^n`.
      rw [Submodule.mem_pi]
      intro i hi
      rw [Submodule.mem_span_singleton]
      refine ⟨z i, ?_⟩
      simp [w, mul_comm]
    have hw_range : w ∈ pairingMap.range := by
      simpa [M, hrange] using hw_mem
    rcases LinearMap.mem_range.mp hw_range with ⟨x, hx⟩
    refine LinearMap.mem_range.mpr ⟨x, ?_⟩
    ext i
    have hm_ne : (m : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    have hi : pairingMap x i = (m : ℤ) * z i := by
      simpa [w] using congrArg (fun f : Fin n → ℤ ↦ f i) hx
    apply mul_left_cancel₀ hm_ne
    calc
      (m : ℤ) * pairingMap' x i = (m : ℤ) * B' x (b i) := by
            rw [hpairing']
      _ = B x (b i) := by
            simpa [hscale, zsmul_eq_mul, mul_comm] using
              (congrArg (fun T : BilinForm ℤ E ↦ T x (b i)) hscale).symm
      _ = pairingMap x i := by rw [hpairing]
      _ = (m : ℤ) * z i := hi
  let eRange : (Fin n → ℤ) ≃ₗ[ℤ] pairingMap'.range :=
    b.equivFun.symm.trans (LinearEquiv.ofInjective pairingMap' hpairing'_injective)
  have hdetEquiv :
      Int.natAbs
          (LinearMap.det
            (pairingMap'.range.subtype ∘ₗ eRange.toLinearMap)) =
        Nat.card ((Fin n → ℤ) ⧸ pairingMap'.range) :=
    Submodule.natAbs_det_equiv pairingMap'.range eRange
  have hmap :
      pairingMap'.range.subtype ∘ₗ eRange.toLinearMap =
        pairingMap' ∘ₗ b.equivFun.symm.toLinearMap := by
    -- The chosen range equivalence is just the basis coordinates followed by the pairing map.
    ext x i
    rfl
  rw [hmap] at hdetEquiv
  have hquot :
      Nat.card ((Fin n → ℤ) ⧸ pairingMap'.range) = 1 := by
    -- Surjectivity says that the coordinate quotient of the rescaled pairing image is trivial.
    rw [hpairing'_range_top]
    simp
  have hdet_pairingMap' :
      Int.natAbs (LinearMap.det (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap)) = 1 := by
    calc
      Int.natAbs (LinearMap.det (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap)) =
          Nat.card ((Fin n → ℤ) ⧸ pairingMap'.range) := by
            simpa using hdetEquiv
      _ = 1 := hquot
  have hmatrix :
      LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
          (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap) =
        Matrix.transpose (B'.toMatrix b) := by
    ext i j
    -- The rescaled coordinate pairing map still records the transpose Gram matrix.
    simp [LinearMap.toMatrix_apply, hpairing', hB'_symm.eq]
  have hdetToMatrix :
      Int.natAbs (LinearMap.det (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap)) =
        Int.natAbs
          (Matrix.det
            (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
              (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap))) := by
    rw [LinearMap.det_toMatrix]
  have hnatAbs_det_B' : Int.natAbs (Matrix.det (B'.toMatrix b)) = 1 := by
    -- The rescaled pairing map is an integral automorphism, so its Gram determinant has
    -- absolute value `1`.
    calc
      Int.natAbs (Matrix.det (B'.toMatrix b)) =
          Int.natAbs (Matrix.det (Matrix.transpose (B'.toMatrix b))) := by
            rw [Matrix.det_transpose]
      _ =
          Int.natAbs
            (Matrix.det
              (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
                (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap))) := by
            rw [hmatrix]
      _ = Int.natAbs (LinearMap.det (pairingMap' ∘ₗ b.equivFun.symm.toLinearMap)) := by
            rw [hdetToMatrix]
      _ = 1 := hdet_pairingMap'
  have hdet_nonneg : 0 ≤ Matrix.det (B'.toMatrix b) := by
    -- The remaining sign bridge is isolated in a separate helper.
    exact
      pairingMatrix_det_nonneg_of_isSymm_of_posDef
        (B := B') hB'_symm hB'_pos (b := b)
  have hdet_eq_one : Matrix.det (B'.toMatrix b) = 1 := by
    -- Nonnegativity lets us remove `Int.natAbs` from the determinant computation.
    calc
      Matrix.det (B'.toMatrix b) = Int.natAbs (Matrix.det (B'.toMatrix b)) := by
            exact Int.eq_natAbs_of_nonneg hdet_nonneg
      _ = 1 := by
            exact_mod_cast hnatAbs_det_B'
  refine ⟨m, hm, B', hscale, ?_⟩
  -- The determinant-one criterion is exactly the current self-duality owner.
  exact isSelfDualIntegralLattice_of_det_eq_one_basis (B := B') b hdet_eq_one

/-- Helper for Exercise 15-15.2-6: once the pairing image is the literal diagonal lattice
`mℤ^n`, the form is an integral multiple of a determinant-one form. -/
theorem dualIntegralLatticeIsRationalHomothety_of_constantSmithCoeffs
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (m : ℕ) (hm : 0 < m)
    (hcoeff :
      ∀ i : Fin n,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
            (by
              simpa [Module.finrank_eq_card_basis b] using
                (LinearMap.finrank_range_of_inj
                  (R := ℤ) (f := pairingMap) hpairing_injective)) i) = m) :
    B.DualIntegralLatticeIsRationalHomothety := by
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    -- The coordinate pairing map has full-rank image once it is injective.
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  have hrange :
      pairingMap.range =
        Submodule.pi Set.univ
          (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ)) := by
    -- The constant Smith-coefficient hypothesis collapses the range to the literal diagonal
    -- lattice in the original coordinates.
    simpa using
      pairingImage_eq_diagonal_of_constantSmithCoeffs
        (N := pairingMap.range) hNrank m hcoeff
  -- Route correction: the constant-Smith-coefficient formulation is now only a thin adapter
  -- around the direct literal-range theorem used by the main proof skeleton.
  exact
    dualIntegralLatticeIsRationalHomothety_of_pairingImage_eq_diagonal
      (B := B) hB_symm hB_pos (b := b) pairingMap hpairing hpairing_injective m hm hrange

/-- Exercise 15-15.2-6 (2): for a symmetric positive definite `G`-invariant integral bilinear
form, the `B`-dual integral lattice in `ℚ ⊗[ℤ] E` is a rational homothety of the original
lattice. -/
-- The local owner `DualIntegralLatticeIsRationalHomothety` records exactly the rational
-- homothety needed here; the proof globalizes the prime-local rigidity supplied by Exercise
-- `15-15.2-5` through the pairing image.
theorem rational_dual_lattice_eq_rational_homothety
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions) (B : BilinForm ℤ E)
    (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ)
    (hB_pos : B.toQuadraticMap.PosDef) :
    B.DualIntegralLatticeIsRationalHomothety := by
  by_cases hE : Subsingleton E
  · letI : Subsingleton E := hE
    -- In the zero-rank branch the determinant owner is automatic, so no localization argument is
    -- needed.
    exact dualIntegralLatticeIsRationalHomothety_of_subsingleton (E := E) B
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  letI : Nontrivial (FractionRing ℤ ⊗[ℤ] E) := fractionRing_tensor_nontrivial (E := E)
  let n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  let pairingMap : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        simp }
  have hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i) := by
    intro x i
    rfl
  have hpairing_injective : Function.Injective pairingMap := by
    -- Positive definiteness makes the coordinate pairing map injective.
    exact
      pairingCoordinateMap_injective
        (E := E) (B := B) hB_symm hB_pos b pairingMap hpairing
  obtain ⟨m, hm, hrange⟩ :=
    pairingImage_eq_diagonal_of_primeLocalFlipDual
      (ρ := ρ) (hρ := hρ) (B := B) hB_symm hB_invariant hB_pos
      (b := b) pairingMap hpairing hpairing_injective
  -- Route correction: the main theorem now consumes the direct literal range equality instead of
  -- exposing the primewise Smith-valuation theorem as a public frontier.
  exact
    dualIntegralLatticeIsRationalHomothety_of_pairingImage_eq_diagonal
      (B := B) hB_symm hB_pos (b := b) pairingMap hpairing hpairing_injective m hm hrange

end IntegralLatticeAmbient

end ThompsonExercise
