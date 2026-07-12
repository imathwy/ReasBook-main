import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.MilnorLineUnits

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: every Milnor line is projective over the
equal-endpoint ring. -/
theorem equalEndpointLineSubmodule_projective (u : kˣ) :
    Module.Projective R (equalEndpointLineSubmodule k u) := by
  -- Mathlib's Picard submodule API turns invertible submodules into projective modules.
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  exact Submodule.projective_of_isUnit (equalEndpointLineSubmodule_isUnit k u)

/-- Helper for Chap10 Example 10 55 5: a finite product of the diagonal Milnor-line modules
is projective. -/
theorem equalEndpointVectorClutchingModule_diagonalLines_projective
    {n : Type u} [Finite n] (D : n → kˣ) :
    Module.Projective R ((i : n) → equalEndpointLineSubmodule k (D i)) := by
  -- Convert the finite product to a dependent finitely supported function module, where mathlib
  -- has the projective instance from the coordinatewise projective hypotheses.
  let _ : Fintype n := Fintype.ofFinite n
  let _ : ∀ i : n, Module.Projective R (equalEndpointLineSubmodule k (D i)) :=
    fun i => equalEndpointLineSubmodule_projective k (D i)
  exact Module.Projective.of_equiv'
    (DFinsupp.linearEquivFunOnFintype :
      (Π₀ i : n, equalEndpointLineSubmodule k (D i)) ≃ₗ[R]
        ((i : n) → equalEndpointLineSubmodule k (D i)))

/-- Helper for Chap10 Example 10 55 5: unit-diagonal vector clutching is projective over the
equal-endpoint ring. -/
theorem equalEndpointVectorClutchingModule_diagonal_projective
    {n : Type u} [Fintype n] [DecidableEq n] (D : n → kˣ) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k)
        (Matrix.diagonal fun i : n => (D i : k))) := by
  -- Each Milnor line is projective, finite products of projectives are projective, and the
  -- diagonal bridge transports that projectivity to the vector-clutching module.
  let _ : Module.Projective R ((i : n) → equalEndpointLineSubmodule k (D i)) :=
    equalEndpointVectorClutchingModule_diagonalLines_projective k D
  exact Module.Projective.of_equiv'
    (equalEndpointVectorClutchingModule_diagonal_linearEquiv k D)

/-- Helper for Chap10 Example 10 55 5: a finite product of Milnor-line modules is finitely
generated over the equal-endpoint ring. -/
theorem equalEndpointVectorClutchingModule_diagonalLines_finite
    {n : Type u} [Finite n] (D : n → kˣ) :
    Module.Finite R ((i : n) → equalEndpointLineSubmodule k (D i)) := by
  -- Each coordinate line is finite, so the finite dependent product is finite.
  let _ : Fintype n := Fintype.ofFinite n
  let _ : ∀ i : n, Module.Finite R (equalEndpointLineSubmodule k (D i)) :=
    fun i => equalEndpointLineSubmodule_finite k (D i)
  infer_instance

/-- Helper for Chap10 Example 10 55 5: package a finite product of Milnor lines as a finite
projective module. -/
abbrev equalEndpointLineProductProjectiveModule
    {n : Type u} [Finite n] (D : n → kˣ) : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R ((i : n) → equalEndpointLineSubmodule k (D i)),
    ⟨equalEndpointVectorClutchingModule_diagonalLines_finite k D,
      equalEndpointVectorClutchingModule_diagonalLines_projective k D⟩⟩

/-- Helper for Chap10 Example 10 55 5: package a unit-diagonal vector clutching module as a
finite projective module. -/
abbrev equalEndpointVectorClutchingDiagonalProjectiveModule
    {n : Type u} [Fintype n] [DecidableEq n] (D : n → kˣ) : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R
      (equalEndpointVectorClutchingModule (k := k)
        (Matrix.diagonal fun i : n => (D i : k))),
    ⟨equalEndpointVectorClutchingModule_finite k
        (Matrix.diagonal fun i : n => (D i : k)),
      equalEndpointVectorClutchingModule_diagonal_projective k D⟩⟩

/-- Helper for Chap10 Example 10 55 5: the K₀ class of a unit-diagonal vector clutching module
is the K₀ class of the corresponding product of Milnor lines. -/
theorem equalEndpointVectorClutchingClass_diagonal_product
    {n : Type u} [Fintype n] [DecidableEq n] (D : n → kˣ) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingDiagonalProjectiveModule k D) =
      projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) := by
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    -- The zero module is finite projective, giving the base object for isomorphism invariance.
    exact ⟨inferInstance, inferInstance⟩
  let e :
      equalEndpointLineProductProjectiveModule k D ≅
        equalEndpointVectorClutchingDiagonalProjectiveModule k D :=
    CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
      (equalEndpointVectorClutchingModule_diagonal_linearEquiv k D).toModuleIso
  have h :
      ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
          (equalEndpointLineProductProjectiveModule k D) =
        ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
          (equalEndpointVectorClutchingDiagonalProjectiveModule k D) := by
    -- Transport the projective K₀ class through the diagonal linear equivalence.
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
      (equalEndpointLineProductProjectiveModule k D)
      (equalEndpointVectorClutchingDiagonalProjectiveModule k D)
      e)
  -- The theorem is stated with the diagonal class first, so reverse the transported equality.
  simpa [projectiveGrothendieckGroupOf] using h.symm

/-- Helper for Chap10 Example 10 55 5: package an arbitrary Milnor line as a finite projective
module. -/
abbrev equalEndpointLineProjectiveModule (u : kˣ) : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R (equalEndpointLineSubmodule k u),
    ⟨equalEndpointLineSubmodule_finite k u,
      equalEndpointLineSubmodule_projective k u⟩⟩

/-- Helper for Chap10 Example 10 55 5: the empty product of Milnor-line projective modules has
zero projective `K₀` class. -/
theorem equalEndpointLineProductProjectiveModule_pempty_class
    (D : PEmpty → kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) = 0 := by
  -- The empty dependent product is a subsingleton module, hence its `K₀` class is the zero
  -- object class.
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    exact ⟨inferInstance, inferInstance⟩
  simpa [projectiveGrothendieckGroupOf] using
    (@ModulePropertyK0.of_subsingleton R _ (finiteProjectiveModuleProperty R) h0
      (equalEndpointLineProductProjectiveModule k D) inferInstance)

/-- Helper for Chap10 Example 10 55 5: adding one more Milnor-line factor adds its class to the
finite product formula. -/
theorem equalEndpointLineProductProjectiveModule_option_class
    {α : Type u} [Fintype α] (D : Option α → kˣ)
    (hα :
      projectiveGrothendieckGroupOf R
          (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i))) =
        ∑ i : α, projectiveGrothendieckGroupOf R
          (equalEndpointLineProjectiveModule k (D (some i)))) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) =
      ∑ o : Option α, projectiveGrothendieckGroupOf R
        (equalEndpointLineProjectiveModule k (D o)) := by
  -- Split the `Option`-indexed product into the new `none` factor and the old tail product.
  let eLinear :
      ((o : Option α) → equalEndpointLineSubmodule k (D o)) ≃ₗ[R]
        (equalEndpointLineProjectiveModule k (D none)).obj ×
          (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i))).obj :=
    LinearEquiv.piOptionEquivProd R
  let eIso :
      equalEndpointLineProductProjectiveModule k D ≅
        equalEndpointProjectiveProductModule k
          (equalEndpointLineProjectiveModule k (D none))
          (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i))) :=
    CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R) eLinear.toModuleIso
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    exact ⟨inferInstance, inferInstance⟩
  have hIsoClass :
      projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) =
        projectiveGrothendieckGroupOf R
          (equalEndpointProjectiveProductModule k
            (equalEndpointLineProjectiveModule k (D none))
            (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i)))) := by
    -- Transport the product class across the canonical `Option` product decomposition.
    simpa [projectiveGrothendieckGroupOf] using
      (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
        (equalEndpointLineProductProjectiveModule k D)
        (equalEndpointProjectiveProductModule k
          (equalEndpointLineProjectiveModule k (D none))
          (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i))))
        eIso)
  calc
    projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) =
        projectiveGrothendieckGroupOf R
          (equalEndpointProjectiveProductModule k
            (equalEndpointLineProjectiveModule k (D none))
            (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i)))) :=
          hIsoClass
    _ = projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (D none)) +
          projectiveGrothendieckGroupOf R
            (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i))) := by
          exact equalEndpointProjectiveClass_prod (k := k)
            (equalEndpointLineProjectiveModule k (D none))
            (equalEndpointLineProductProjectiveModule k (fun i : α => D (some i)))
    _ = projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (D none)) +
          ∑ i : α, projectiveGrothendieckGroupOf R
            (equalEndpointLineProjectiveModule k (D (some i))) := by
          rw [hα]
    _ = ∑ o : Option α, projectiveGrothendieckGroupOf R
          (equalEndpointLineProjectiveModule k (D o)) := by
          simpa using
            (Fintype.sum_option
              (fun o : Option α =>
                projectiveGrothendieckGroupOf R
                  (equalEndpointLineProjectiveModule k (D o)))).symm

/-- Helper for Chap10 Example 10 55 5: the projective `K₀` class of a finite product of
Milnor-line modules is the sum of the projective classes of the factors. -/
theorem equalEndpointLineProductProjectiveModule_class_eq_sum
    {α : Type u} [Fintype α] (D : α → kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) =
      ∑ i : α, projectiveGrothendieckGroupOf R
        (equalEndpointLineProjectiveModule k (D i)) := by
  let P : ∀ (β : Type u) [Fintype β], Prop := fun β _ =>
    ∀ E : β → kˣ,
      projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k E) =
        ∑ i : β, projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (E i))
  have hP : P α := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ α
    · intro β γ hγ e hβ E
      letI : Fintype β := Fintype.ofEquiv γ e.symm
      let eLinear :
          ((b : β) → equalEndpointLineSubmodule k (E (e b))) ≃ₗ[R]
            ((c : γ) → equalEndpointLineSubmodule k (E c)) :=
        LinearEquiv.piCongrLeft R (fun c : γ => equalEndpointLineSubmodule k (E c)) e
      let eIso :
          equalEndpointLineProductProjectiveModule k (fun b : β => E (e b)) ≅
            equalEndpointLineProductProjectiveModule k E :=
        CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R) eLinear.toModuleIso
      have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
        exact ⟨inferInstance, inferInstance⟩
      have hIsoClass :
          projectiveGrothendieckGroupOf R
              (equalEndpointLineProductProjectiveModule k (fun b : β => E (e b))) =
            projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k E) := by
        -- Reindexing a finite product by an equivalence preserves its projective `K₀` class.
        simpa [projectiveGrothendieckGroupOf] using
          (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
            (equalEndpointLineProductProjectiveModule k (fun b : β => E (e b)))
            (equalEndpointLineProductProjectiveModule k E)
            eIso)
      have hsum :
          (∑ b : β, projectiveGrothendieckGroupOf R
              (equalEndpointLineProjectiveModule k (E (e b)))) =
            ∑ c : γ, projectiveGrothendieckGroupOf R
              (equalEndpointLineProjectiveModule k (E c)) := by
        exact Equiv.sum_comp e
          (fun c : γ =>
            projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (E c)))
      calc
        projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k E) =
            projectiveGrothendieckGroupOf R
              (equalEndpointLineProductProjectiveModule k (fun b : β => E (e b))) :=
            hIsoClass.symm
        _ = ∑ b : β, projectiveGrothendieckGroupOf R
              (equalEndpointLineProjectiveModule k (E (e b))) := by
            exact hβ (fun b : β => E (e b))
        _ = ∑ c : γ, projectiveGrothendieckGroupOf R
              (equalEndpointLineProjectiveModule k (E c)) :=
            hsum
    · intro E
      -- The induction starts from the empty product, whose class is zero.
      simpa using equalEndpointLineProductProjectiveModule_pempty_class (k := k) E
    · intro β _ ih E
      -- The option step is exactly the binary product relation plus the induction hypothesis.
      exact equalEndpointLineProductProjectiveModule_option_class (k := k) E
          (ih (fun b : β => E (some b)))
  exact hP D

/-- Helper for Chap10 Example 10 55 5: a unit-diagonal vector clutching module has projective
`K₀` class equal to the sum of the corresponding Milnor-line classes. -/
theorem equalEndpointVectorClutchingClass_diagonal_units
    {α : Type u} [Fintype α] [DecidableEq α] (D : α → kˣ) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingDiagonalProjectiveModule k D) =
      ∑ i : α, projectiveGrothendieckGroupOf R
        (equalEndpointLineProjectiveModule k (D i)) := by
  -- First identify the diagonal vector clutching package with the product of Milnor lines, then
  -- apply the finite product formula for projective `K₀` classes.
  calc
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingDiagonalProjectiveModule k D) =
        projectiveGrothendieckGroupOf R (equalEndpointLineProductProjectiveModule k D) := by
          exact equalEndpointVectorClutchingClass_diagonal_product (k := k) D
    _ = ∑ i : α, projectiveGrothendieckGroupOf R
          (equalEndpointLineProjectiveModule k (D i)) := by
          exact equalEndpointLineProductProjectiveModule_class_eq_sum (k := k) D

/-- Helper for Chap10 Example 10 55 5: every Milnor line projective module has generic rank
one. -/
theorem equalEndpointLineProjectiveModule_rank (u : kˣ) :
    equalEndpointProjectiveRank k (equalEndpointLineProjectiveModule k u) = 1 := by
  let K := FractionRing R
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  letI : Module.Invertible R (equalEndpointLineSubmodule k u) := by
    -- The submodule-unit API gives an invertible module structure on the packaged Milnor line.
    change Module.Invertible R (equalEndpointLineSubmoduleUnit k u)
    infer_instance
  letI : Module.Invertible K (TensorProduct R K (equalEndpointLineSubmodule k u)) :=
    inferInstance
  letI : Module.Free K (TensorProduct R K (equalEndpointLineSubmodule k u)) :=
    Module.Free.of_divisionRing K (TensorProduct R K (equalEndpointLineSubmodule k u))
  -- After base change to the fraction field, an invertible module is one-dimensional.
  simpa [equalEndpointProjectiveRank, equalEndpointLineProjectiveModule, K] using
    (Module.Invertible.finrank_eq_one K
      (TensorProduct R K (equalEndpointLineSubmodule k u)))

/-- Helper for Chap10 Example 10 55 5: the stable product comparison type for Milnor line
modules. -/
abbrev equalEndpointLineStableProductLinearEquiv (u v : kˣ) :=
  ((equalEndpointLineProjectiveModule k (u * v)).obj ×
      (equalEndpointProjectiveFreeModule k).obj) ≃ₗ[R]
    ((equalEndpointLineProjectiveModule k u).obj ×
      (equalEndpointLineProjectiveModule k v).obj)

/-- Helper for Chap10 Example 10 55 5: the upper elementary `2 × 2` matrix with
off-diagonal entry `t`. -/
def equalEndpointElementaryUpper (t : Polynomial k) :
    Matrix (Fin 2) (Fin 2) (Polynomial k) :=
  !![1, t; 0, 1]

/-- Helper for Chap10 Example 10 55 5: the lower elementary `2 × 2` matrix with
off-diagonal entry `t`. -/
def equalEndpointElementaryLower (t : Polynomial k) :
    Matrix (Fin 2) (Fin 2) (Polynomial k) :=
  !![1, 0; t, 1]

/-- Helper for Chap10 Example 10 55 5: an upper elementary matrix has determinant one. -/
theorem equalEndpointElementaryUpper_det (t : Polynomial k) :
    (equalEndpointElementaryUpper (k := k) t).det = 1 := by
  -- The determinant computation reduces to the standard `2 × 2` formula.
  simp [equalEndpointElementaryUpper, Matrix.det_fin_two]

/-- Helper for Chap10 Example 10 55 5: a lower elementary matrix has determinant one. -/
theorem equalEndpointElementaryLower_det (t : Polynomial k) :
    (equalEndpointElementaryLower (k := k) t).det = 1 := by
  -- The determinant computation reduces to the standard `2 × 2` formula.
  simp [equalEndpointElementaryLower, Matrix.det_fin_two]

/-- Helper for Chap10 Example 10 55 5: the explicit elementary `SL₂` path from the identity
to the diagonal matrix with entries `a` and `a⁻¹`. -/
def equalEndpointSL2DiagonalPath (a : kˣ) :
    Matrix (Fin 2) (Fin 2) (Polynomial k) :=
  equalEndpointElementaryUpper (k := k) (Polynomial.X * Polynomial.C ((a : k) - 1)) *
    equalEndpointElementaryLower (k := k) Polynomial.X *
    equalEndpointElementaryUpper (k := k)
      (Polynomial.X * Polynomial.C (((a⁻¹ : kˣ) : k) - 1)) *
    equalEndpointElementaryLower (k := k) (Polynomial.X * Polynomial.C (-(a : k)))

/-- Helper for Chap10 Example 10 55 5: the explicit diagonal path starts at the identity. -/
theorem equalEndpointSL2DiagonalPath_eval_zero (a : kˣ) :
    (equalEndpointSL2DiagonalPath (k := k) a).map (Polynomial.evalRingHom 0) = 1 := by
  -- Each elementary factor specializes to the identity at `X = 0`.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]

/-- Helper for Chap10 Example 10 55 5: the explicit diagonal path ends at
`diag(a, a⁻¹)`. -/
theorem equalEndpointSL2DiagonalPath_eval_one (a : kˣ) :
    (equalEndpointSL2DiagonalPath (k := k) a).map (Polynomial.evalRingHom 1) =
      !![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)] := by
  have ha0 : (a : k) ≠ 0 := Units.ne_zero a
  -- The four elementary matrices multiply to the diagonal matrix at `X = 1`.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
      field_simp [ha0]
      ring
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
      field_simp [ha0]
      ring
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
    · simp [equalEndpointSL2DiagonalPath, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]

/-- Helper for Chap10 Example 10 55 5: every matrix on the explicit diagonal path has
determinant one. -/
theorem equalEndpointSL2DiagonalPath_det (a : kˣ) :
    (equalEndpointSL2DiagonalPath (k := k) a).det = 1 := by
  -- Determinants multiply, and every elementary factor has determinant one.
  simp [equalEndpointSL2DiagonalPath, Matrix.det_mul, equalEndpointElementaryUpper_det,
    equalEndpointElementaryLower_det]

/-- Helper for Chap10 Example 10 55 5: an upper elementary matrix is inverted by negating its
off-diagonal entry. -/
theorem equalEndpointElementaryUpper_mul_neg (t : Polynomial k) :
    equalEndpointElementaryUpper (k := k) t * equalEndpointElementaryUpper (k := k) (-t) = 1 := by
  -- Check the four entries; the off-diagonal terms cancel.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointElementaryUpper]
    · simp [equalEndpointElementaryUpper]
  · fin_cases j
    · simp [equalEndpointElementaryUpper]
    · simp [equalEndpointElementaryUpper]

/-- Helper for Chap10 Example 10 55 5: negating the upper off-diagonal entry also gives a left
inverse. -/
theorem equalEndpointElementaryUpper_neg_mul (t : Polynomial k) :
    equalEndpointElementaryUpper (k := k) (-t) * equalEndpointElementaryUpper (k := k) t = 1 := by
  -- Check the four entries; this is the other cancellation order for the same elementary matrix.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointElementaryUpper]
    · simp [equalEndpointElementaryUpper]
  · fin_cases j
    · simp [equalEndpointElementaryUpper]
    · simp [equalEndpointElementaryUpper]

/-- Helper for Chap10 Example 10 55 5: a lower elementary matrix is inverted by negating its
off-diagonal entry. -/
theorem equalEndpointElementaryLower_mul_neg (t : Polynomial k) :
    equalEndpointElementaryLower (k := k) t * equalEndpointElementaryLower (k := k) (-t) = 1 := by
  -- Check the four entries; the lower off-diagonal terms cancel.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointElementaryLower]
    · simp [equalEndpointElementaryLower]
  · fin_cases j
    · simp [equalEndpointElementaryLower]
    · simp [equalEndpointElementaryLower]

/-- Helper for Chap10 Example 10 55 5: negating the lower off-diagonal entry also gives a left
inverse. -/
theorem equalEndpointElementaryLower_neg_mul (t : Polynomial k) :
    equalEndpointElementaryLower (k := k) (-t) * equalEndpointElementaryLower (k := k) t = 1 := by
  -- Check the four entries; this is the other cancellation order for the lower elementary matrix.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointElementaryLower]
    · simp [equalEndpointElementaryLower]
  · fin_cases j
    · simp [equalEndpointElementaryLower]
    · simp [equalEndpointElementaryLower]

/-- Helper for Chap10 Example 10 55 5: the upper elementary matrix packaged as a unit. -/
def equalEndpointElementaryUpperUnit (t : Polynomial k) :
    (Matrix (Fin 2) (Fin 2) (Polynomial k))ˣ :=
  { val := equalEndpointElementaryUpper (k := k) t
    inv := equalEndpointElementaryUpper (k := k) (-t)
    val_inv := equalEndpointElementaryUpper_mul_neg (k := k) t
    inv_val := equalEndpointElementaryUpper_neg_mul (k := k) t }

/-- Helper for Chap10 Example 10 55 5: the lower elementary matrix packaged as a unit. -/
def equalEndpointElementaryLowerUnit (t : Polynomial k) :
    (Matrix (Fin 2) (Fin 2) (Polynomial k))ˣ :=
  { val := equalEndpointElementaryLower (k := k) t
    inv := equalEndpointElementaryLower (k := k) (-t)
    val_inv := equalEndpointElementaryLower_mul_neg (k := k) t
    inv_val := equalEndpointElementaryLower_neg_mul (k := k) t }

/-- Helper for Chap10 Example 10 55 5: the explicit diagonal path is a product of elementary
matrix units. -/
def equalEndpointSL2DiagonalPathUnit (a : kˣ) :
    (Matrix (Fin 2) (Fin 2) (Polynomial k))ˣ :=
  equalEndpointElementaryUpperUnit (k := k) (Polynomial.X * Polynomial.C ((a : k) - 1)) *
    equalEndpointElementaryLowerUnit (k := k) Polynomial.X *
    equalEndpointElementaryUpperUnit (k := k)
      (Polynomial.X * Polynomial.C (((a⁻¹ : kˣ) : k) - 1)) *
    equalEndpointElementaryLowerUnit (k := k) (Polynomial.X * Polynomial.C (-(a : k)))

/-- Helper for Chap10 Example 10 55 5: the unit-valued diagonal path has the expected underlying
matrix. -/
theorem equalEndpointSL2DiagonalPathUnit_coe (a : kˣ) :
    ((equalEndpointSL2DiagonalPathUnit (k := k) a :
        (Matrix (Fin 2) (Fin 2) (Polynomial k))ˣ) :
      Matrix (Fin 2) (Fin 2) (Polynomial k)) =
      equalEndpointSL2DiagonalPath (k := k) a := rfl


end
