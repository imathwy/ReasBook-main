import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.LineResidualPicard

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the unit-ratio Milnor line unit is principal. -/
theorem equalEndpointLineSubmoduleUnit_one_principal :
    equalEndpointLineSubmoduleUnit k 1 ∈
      (Units.map (Submodule.spanSingleton R).toMonoidHom).range := by
  -- The ratio-one Picard class is trivial, so the exactness bridge marks the unit as principal.
  exact (equalEndpointLineSubmoduleUnit_principal_iff_picClass_eq_one k 1).mpr
    (equalEndpointLinePicClass_one k)

/-- Helper for Chap10 Example 10 55 5: a Milnor line Picard class is trivial exactly for
endpoint ratio `1`. -/
theorem equalEndpointLinePicClass_eq_one_iff (unitRatio : kˣ) :
    equalEndpointLinePicClass k unitRatio = 1 ↔ unitRatio = 1 := by
  constructor
  · intro hpic
    have hprincipal : equalEndpointLineSubmoduleUnit k unitRatio ∈
        (Units.map (Submodule.spanSingleton R).toMonoidHom).range := by
      -- Convert trivial Picard class into principality using the exactness bridge.
      exact (equalEndpointLineSubmoduleUnit_principal_iff_picClass_eq_one k unitRatio).mpr
        hpic
    exact (equalEndpointLineUnit_principal_iff (k := k) unitRatio).mp hprincipal
  · intro hratio
    -- The ratio-one line has trivial Picard class.
    rw [hratio]
    exact equalEndpointLinePicClass_one k

/-- Helper for Chap10 Example 10 55 5: Picard classes of Milnor lines multiply by multiplying
endpoint-unit ratios. -/
theorem equalEndpointLinePicClass_mul (u v : kˣ) :
    equalEndpointLinePicClass k (u * v) =
      equalEndpointLinePicClass k u * equalEndpointLinePicClass k v := by
  -- The already proved product law for line submodules is consumed through the line-unit
  -- homomorphism, then through `unitsToPic`.
  rw [← equalEndpointLinePicHom_apply]
  rw [← equalEndpointLinePicHom_apply]
  rw [← equalEndpointLinePicHom_apply]
  exact map_mul (equalEndpointLinePicHom k) u v

/-- Helper for Chap10 Example 10 55 5: Picard classes of inverse-ratio Milnor lines are inverse
Picard classes. -/
theorem equalEndpointLinePicClass_inv (unitRatio : kˣ) :
    equalEndpointLinePicClass k unitRatio⁻¹ =
      (equalEndpointLinePicClass k unitRatio)⁻¹ := by
  -- This is the inverse law for the Picard homomorphism, rewritten to the named class function.
  rw [← equalEndpointLinePicHom_apply]
  rw [← equalEndpointLinePicHom_apply]
  exact map_inv (equalEndpointLinePicHom k) unitRatio

/-- Helper for Chap10 Example 10 55 5: the Picard coordinate of Milnor lines is injective on
endpoint-unit ratios. -/
theorem equalEndpointLinePicHom_injective :
    Function.Injective (equalEndpointLinePicHom k) := by
  intro u v huv
  have hquot_pic : equalEndpointLinePicClass k (u * v⁻¹) = 1 := by
    -- Equal Picard coordinates make the quotient class trivial.
    rw [← equalEndpointLinePicHom_apply]
    rw [map_mul, map_inv, huv]
    exact mul_inv_cancel (equalEndpointLinePicHom k v)
  have hratio : u * v⁻¹ = 1 :=
    (equalEndpointLinePicClass_eq_one_iff (k := k) (u * v⁻¹)).mp hquot_pic
  -- A unit quotient equal to one is the original equality.
  exact mul_inv_eq_one.mp hratio

/-- Helper for Chap10 Example 10 55 5: equality of Milnor-line Picard coordinates is equality
of endpoint-unit ratios. -/
theorem equalEndpointLinePicClass_eq_iff (u v : kˣ) :
    equalEndpointLinePicClass k u = equalEndpointLinePicClass k v ↔ u = v := by
  -- Convert the named Picard classes back to the Picard homomorphism and use injectivity.
  constructor
  · intro hpic
    apply equalEndpointLinePicHom_injective (k := k)
    simpa [equalEndpointLinePicHom_apply] using hpic
  · intro hratio
    rw [hratio]

/-- Helper for Chap10 Example 10 55 5: if equality of residual Milnor-line classes preserves
the Picard coordinate, then residual Milnor-line classes are injective on endpoint-unit ratios. -/
theorem equalEndpointLineResidualClass_injective_of_picClass
    (hpic : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v →
        equalEndpointLinePicClass k u = equalEndpointLinePicClass k v) :
    ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  -- Picard coordinates already distinguish endpoint-unit ratios, so the compatibility hypothesis
  -- turns residual equality into equality of units.
  intro u v hresidual
  exact (equalEndpointLinePicClass_eq_iff (k := k) u v).mp (hpic u v hresidual)

/-- Helper for Chap10 Example 10 55 5: stable K₀ sum identities, Picard-coordinate compatibility,
and residual-line surjectivity together supply the residual exactness package. -/
theorem equalEndpointLineResidualClasses_of_projective_sum_and_picClass
    (hstable : ∀ u v : kˣ,
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
          equalEndpointProjectiveFreeClass k =
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
          projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v))
    (hpic : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v →
        equalEndpointLinePicClass k u = equalEndpointLinePicClass k v)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ _hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v,
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- The product law comes from stable K0 sums, while Picard compatibility supplies the
  -- injectivity half required by the residual homomorphism bridge.
  exact equalEndpointLineResidualClasses_of_projective_sum (k := k) hstable
    (equalEndpointLineResidualClass_injective_of_picClass (k := k) hpic) hsurj

/-- Helper for Chap10 Example 10 55 5: under a residual product law, equality of two residual
Milnor-line classes makes the quotient endpoint ratio residual-zero. -/
theorem equalEndpointLineResidualClass_mul_inv_eq_zero_of_eq
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    {u v : kˣ}
    (hresidual : equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v) :
    equalEndpointLineResidualClass k (u * v⁻¹) = 0 := by
  -- Convert the quotient residual class into a sum and cancel equal opposite summands.
  rw [hmul, equalEndpointLineResidualClass_inv_of_mul (k := k) hmul v, hresidual,
    add_neg_cancel]

/-- Helper for Chap10 Example 10 55 5: residual-zero detection by the Picard coordinate makes
residual Milnor-line classes injective. -/
theorem equalEndpointLineResidualClass_injective_of_zero_picClass
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) :
    ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  intro u v hresidual
  -- Pass from equality to the quotient class, then use the Picard/principal-line criterion.
  have hquot_zero :
      equalEndpointLineResidualClass k (u * v⁻¹) = 0 :=
    equalEndpointLineResidualClass_mul_inv_eq_zero_of_eq (k := k) hmul hresidual
  have hquot_pic : equalEndpointLinePicClass k (u * v⁻¹) = 1 :=
    hzero_pic (u * v⁻¹) hquot_zero
  have hquot : u * v⁻¹ = 1 :=
    (equalEndpointLinePicClass_eq_one_iff (k := k) (u * v⁻¹)).mp hquot_pic
  exact mul_inv_eq_one.mp hquot

/-- Helper for Chap10 Example 10 55 5: injectivity of residual Milnor-line classes already
detects residual-zero classes as trivial Picard classes. -/
theorem equalEndpointLineResidualClass_zero_picClass_one_of_injective
    (hinj : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)
    (unitRatio : kˣ)
    (hzero : equalEndpointLineResidualClass k unitRatio = 0) :
    equalEndpointLinePicClass k unitRatio = 1 := by
  -- Compare the residual-zero class with the ratio-one residual class to identify the unit.
  have hunit : unitRatio = 1 := by
    apply hinj unitRatio 1
    simpa [equalEndpointLineResidualClass_one] using hzero
  -- Once the endpoint-unit ratio is one, the Picard class is the known trivial class.
  rw [hunit]
  exact equalEndpointLinePicClass_one k

/-- Helper for Chap10 Example 10 55 5: stable K₀ sums, Picard detection of residual-zero
quotients, and rank-kernel surjectivity together supply residual exactness. -/
theorem equalEndpointLineResidualClasses_of_projective_sum_and_zero_picClass
    (hstable : ∀ u v : kˣ,
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
          equalEndpointProjectiveFreeClass k =
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
          projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v))
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ _hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v,
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Stable K₀ sums give the product law; the residual-zero Picard criterion gives injectivity.
  let hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v :=
    fun u v => equalEndpointLineResidualClass_mul_of_projective_sum (k := k) u v (hstable u v)
  exact ⟨hmul,
    equalEndpointLineResidualClass_injective_of_zero_picClass (k := k) hmul hzero_pic,
    hsurj⟩

/-- Helper for Chap10 Example 10 55 5: residual-zero Picard detection and residual-line
surjectivity make the residual Milnor-line homomorphism bijective. -/
theorem equalEndpointLineResidualHom_bijective_of_zeroPicClass_surjective
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    Function.Bijective
      (equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k)) := by
  -- The SL₂ stable-product theorem supplies additivity; the two hypotheses are exactly the
  -- class-level injectivity and surjectivity inputs for the residual homomorphism bridge.
  apply (equalEndpointLineResidualHom_bijective_iff (k := k)
    (equalEndpointLineResidualClass_mul k)).mpr
  exact ⟨
    equalEndpointLineResidualClass_injective_of_zero_picClass (k := k)
      (equalEndpointLineResidualClass_mul k) hzero_pic,
    hsurj⟩

/-- Helper for Chap10 Example 10 55 5: a bijective residual Milnor-line homomorphism implies the
Picard/Cartan exactness package. -/
theorem equalEndpointLinePicardCartanExact_of_residualHom
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    (hbijective :
      Function.Bijective (equalEndpointLineResidualHom (k := k) (hmul := hmul))) :
    (∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) ∧
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Split residual-hom bijectivity into class-level injectivity and residual-line surjectivity.
  have hinj : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    (equalEndpointLineResidualHom_injective_iff (k := k) hmul).mp hbijective.1
  have hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z :=
    (equalEndpointLineResidualHom_surjective_iff (k := k) hmul).mp hbijective.2
  -- Injectivity detects the ratio-one residual class, hence gives the Picard-principal half.
  exact ⟨
    equalEndpointLineResidualClass_zero_picClass_one_of_injective (k := k) hinj,
    hsurj⟩

/-- Helper for Chap10 Example 10 55 5: subtracting a fixed additive-group element from every
term of a finite sum is undone by adding the cardinal multiple of that fixed element. -/
private theorem finsetSumSubConstAddCardZsmul
    {G : Type*} [AddCommGroup G] {ι : Type*} (s : Finset ι) (f : ι → G) (a : G) :
    s.sum (fun i => f i - a) + (s.card : ℤ) • a = s.sum f := by
  -- Induct over the finite support so the only algebra left at each step is cancellation in an
  -- additive commutative group.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      simp only [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
      calc
        (f i - a + s.sum (fun j => f j - a)) + ((s.card : ℤ) • a + a) =
            f i + (s.sum (fun j => f j - a) + (s.card : ℤ) • a) := by
              abel
        _ = f i + s.sum f := by
              rw [ih]

/-- Helper for Chap10 Example 10 55 5: finite products of endpoint-unit ratios correspond to
finite sums of their residual Milnor-line classes. -/
theorem equalEndpointLineResidualClass_finset_prod
    {ι : Type u} (s : Finset ι) (D : ι → kˣ) :
    equalEndpointLineResidualClass k (s.prod D) =
      s.sum (fun i => equalEndpointLineResidualClass k (D i)) := by
  -- The statement is the finite iteration of the already-proved binary residual product law.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [equalEndpointLineResidualClass_one]
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, equalEndpointLineResidualClass_mul, ih]

/-- Helper for Chap10 Example 10 55 5: the explicit class map from endpoint-unit and rank
coordinates to projective `K₀`. -/
noncomputable def equalEndpointLineRankClassMap :
    Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
  ((equalEndpointProjectiveRankMap.{u, u} k).ker.subtype.comp
      ((equalEndpointLineResidualHom (k := k)
        (hmul := equalEndpointLineResidualClass_mul k)).comp
          (AddMonoidHom.fst (Additive kˣ) ℤ))) +
    ((equalEndpointProjectiveRankSection k).comp
      (AddMonoidHom.snd (Additive kˣ) ℤ))

/-- Helper for Chap10 Example 10 55 5: evaluating the line-plus-rank class map separates the
residual Milnor-line part from the free rank section. -/
theorem equalEndpointLineRankClassMap_apply (x : Additive kˣ × ℤ) :
    equalEndpointLineRankClassMap k x =
      (equalEndpointLineResidualClass k x.1.toMul :
        projectiveGrothendieckGroup.{u, u} R) +
        equalEndpointProjectiveRankSection k x.2 := by
  -- Unfold only the homomorphism combinators; the residual homomorphism evaluation is named.
  simp [equalEndpointLineRankClassMap, AddMonoidHom.comp_apply,
    equalEndpointLineResidualHom_apply]

/-- Helper for Chap10 Example 10 55 5: the rank of the line-plus-rank class map is the integer
coordinate. -/
theorem equalEndpointLineRankClassMap_rank :
    (equalEndpointProjectiveRankMap.{u, u} k).comp (equalEndpointLineRankClassMap k) =
      AddMonoidHom.snd (Additive kˣ) ℤ := by
  -- The residual line lies in the rank kernel, while the free section has the prescribed rank.
  apply AddMonoidHom.ext
  intro x
  rw [AddMonoidHom.comp_apply, equalEndpointLineRankClassMap_apply, map_add]
  have hline :
      equalEndpointProjectiveRankMap.{u, u} k
          (equalEndpointLineResidualClass k x.1.toMul :
            projectiveGrothendieckGroup.{u, u} R) = 0 :=
    (equalEndpointLineResidualClass k x.1.toMul).2
  rw [hline, equalEndpointProjectiveRankSection_rank, zero_add]
  rfl

/-- Helper for Chap10 Example 10 55 5: on a pure endpoint-unit coordinate, the line-plus-rank
class map is the residual Milnor-line class. -/
theorem equalEndpointLineRankClassMap_line (unitRatio : kˣ) :
    equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, (0 : ℤ)) =
      (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) := by
  -- The rank coordinate is zero, so only the residual-line summand remains.
  rw [equalEndpointLineRankClassMap_apply]
  simp [equalEndpointProjectiveRankSection_apply]

/-- Helper for Chap10 Example 10 55 5: a unit-diagonal vector-clutching class is represented by
the product of diagonal unit ratios together with its cardinal rank. -/
theorem equalEndpointVectorClutchingClass_diagonal_lineRank
    {ι : Type u} [Fintype ι] [DecidableEq ι] (D : ι → kˣ) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingDiagonalProjectiveModule k D) =
      equalEndpointLineRankClassMap k
        (Additive.ofMul (∏ i, D i), (Fintype.card ι : ℤ)) := by
  -- Start from the diagonal product formula, then rewrite each Milnor line as its residual
  -- class plus one free rank-one class.
  let F : projectiveGrothendieckGroup.{u, u} R := equalEndpointProjectiveFreeClass k
  let L : ι → projectiveGrothendieckGroup.{u, u} R :=
    fun i => projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (D i))
  have hresidualProd :
      (equalEndpointLineResidualClass k (∏ i, D i) :
        projectiveGrothendieckGroup.{u, u} R) =
        ∑ i, (equalEndpointLineResidualClass k (D i) :
          projectiveGrothendieckGroup.{u, u} R) := by
    simpa using congrArg
      (fun z : (equalEndpointProjectiveRankMap.{u, u} k).ker =>
        (z : projectiveGrothendieckGroup.{u, u} R))
      (equalEndpointLineResidualClass_finset_prod (k := k) (s := Finset.univ) D)
  have hresidualSum :
      (∑ i, (equalEndpointLineResidualClass k (D i) :
        projectiveGrothendieckGroup.{u, u} R)) =
        ∑ i, (L i - F) := by
    -- Forgetting the rank-kernel subtype exposes each residual line as `[I_u] - [R]`.
    apply Finset.sum_congr rfl
    intro i _
    simp [L, F, equalEndpointLineResidualClass_val]
  have hlineSum :
      (∑ i, L i) =
        (∑ i, (equalEndpointLineResidualClass k (D i) :
          projectiveGrothendieckGroup.{u, u} R)) +
          (Fintype.card ι : ℤ) • F := by
    -- The group-algebra helper cancels the `Fintype.card ι` copied free classes.
    rw [hresidualSum]
    exact (finsetSumSubConstAddCardZsmul
      (s := Finset.univ) (f := L) (a := F)).symm
  calc
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingDiagonalProjectiveModule k D) =
        ∑ i, L i := by
          exact equalEndpointVectorClutchingClass_diagonal_units (k := k) D
    _ = (equalEndpointLineResidualClass k (∏ i, D i) :
          projectiveGrothendieckGroup.{u, u} R) +
          (Fintype.card ι : ℤ) • F := by
          rw [hlineSum, hresidualProd]
    _ = equalEndpointLineRankClassMap k
          (Additive.ofMul (∏ i, D i), (Fintype.card ι : ℤ)) := by
          simp [equalEndpointLineRankClassMap_apply, equalEndpointProjectiveRankSection_apply, F]

/-- Helper for Chap10 Example 10 55 5: an invertible vector-clutching matrix has projective
`K₀` class determined by its determinant and size. -/
theorem equalEndpointVectorClutchingClass_det_lineRank
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hdet : A.det ≠ 0)
    (hA : Module.Projective R (equalEndpointVectorClutchingModule (k := k) A)) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k A hA) =
      equalEndpointLineRankClassMap k
        (Additive.ofMul (Units.mk0 A.det hdet), (Fintype.card ι : ℤ)) := by
  -- Reduce the invertible matrix to transvection products times a diagonal matrix.
  rcases Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A with
    ⟨L, L', D, hAeq⟩
  have hdet_eq : A.det = (Matrix.diagonal D).det := by
    calc
      A.det = ((L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod).det := by
            rw [hAeq]
      _ = (Matrix.diagonal D).det := by
            simp [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_assoc]
  have hDdet : (Matrix.diagonal D).det ≠ 0 := by
    intro hzero
    exact hdet (hdet_eq.trans hzero)
  let Dunit : ι → kˣ :=
    fun i => Units.mk0 (D i) (equalEndpointVectorClutching_diagonalEntry_ne_zero (k := k) hDdet i)
  have hDmatrix : Matrix.diagonal (fun i : ι => (Dunit i : k)) = Matrix.diagonal D := by
    ext i j
    simp [Dunit]
  have hAeqUnit :
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod *
          Matrix.diagonal (fun i : ι => (Dunit i : k)) *
            (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
    simpa [hDmatrix, mul_assoc] using hAeq
  have hunitProd : (∏ i, Dunit i) = Units.mk0 A.det hdet := by
    ext
    simpa [Dunit, Matrix.det_diagonal] using hdet_eq.symm
  -- Build projectivity proofs along the two transvection products, keeping each transport named.
  have hdiagProj :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (Matrix.diagonal fun i : ι => (Dunit i : k))) :=
    equalEndpointVectorClutchingModule_diagonal_projective k Dunit
  have hleftProj :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          ((L.map Matrix.TransvectionStruct.toMatrix).prod *
            Matrix.diagonal (fun i : ι => (Dunit i : k)))) :=
    equalEndpointVectorClutchingModule_leftTransvectionList_prod_projective (k := k)
      (Matrix.diagonal fun i : ι => (Dunit i : k)) L hdiagProj
  have hrightProj :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (((L.map Matrix.TransvectionStruct.toMatrix).prod *
            Matrix.diagonal (fun i : ι => (Dunit i : k))) *
              (L'.map Matrix.TransvectionStruct.toMatrix).prod)) :=
    equalEndpointVectorClutchingModule_rightTransvectionList_prod_projective (k := k)
      ((L.map Matrix.TransvectionStruct.toMatrix).prod *
        Matrix.diagonal (fun i : ι => (Dunit i : k))) L' hleftProj
  -- Compare the original class with the normalized transvection product and then with the diagonal.
  have hAprodClass :
      projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k A hA) =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            (((L.map Matrix.TransvectionStruct.toMatrix).prod *
              Matrix.diagonal (fun i : ι => (Dunit i : k))) *
                (L'.map Matrix.TransvectionStruct.toMatrix).prod) hrightProj) :=
    equalEndpointVectorClutchingClass_eq_of_matrix_eq (k := k) hAeqUnit hA hrightProj
  have hdiagToLeft :
      projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            (Matrix.diagonal fun i : ι => (Dunit i : k)) hdiagProj) =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            ((L.map Matrix.TransvectionStruct.toMatrix).prod *
              Matrix.diagonal (fun i : ι => (Dunit i : k))) hleftProj) :=
    equalEndpointVectorClutchingClass_leftTransvectionList_prod (k := k)
      (Matrix.diagonal fun i : ι => (Dunit i : k)) L hdiagProj hleftProj
  have hleftToRight :
      projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            ((L.map Matrix.TransvectionStruct.toMatrix).prod *
              Matrix.diagonal (fun i : ι => (Dunit i : k))) hleftProj) =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            (((L.map Matrix.TransvectionStruct.toMatrix).prod *
              Matrix.diagonal (fun i : ι => (Dunit i : k))) *
                (L'.map Matrix.TransvectionStruct.toMatrix).prod) hrightProj) :=
    equalEndpointVectorClutchingClass_rightTransvectionList_prod (k := k)
      ((L.map Matrix.TransvectionStruct.toMatrix).prod *
        Matrix.diagonal (fun i : ι => (Dunit i : k))) L' hleftProj hrightProj
  calc
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k A hA) =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            (((L.map Matrix.TransvectionStruct.toMatrix).prod *
              Matrix.diagonal (fun i : ι => (Dunit i : k))) *
                (L'.map Matrix.TransvectionStruct.toMatrix).prod) hrightProj) := hAprodClass
    _ = projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k
            (Matrix.diagonal fun i : ι => (Dunit i : k)) hdiagProj) := by
          exact (hdiagToLeft.trans hleftToRight).symm
    _ = equalEndpointLineRankClassMap k
          (Additive.ofMul (∏ i, Dunit i), (Fintype.card ι : ℤ)) := by
          exact equalEndpointVectorClutchingClass_diagonal_lineRank (k := k) Dunit
    _ = equalEndpointLineRankClassMap k
          (Additive.ofMul (Units.mk0 A.det hdet), (Fintype.card ι : ℤ)) := by
          rw [hunitProd]

/-- Helper for Chap10 Example 10 55 5: an invertible vector-clutching module has generic
projective rank equal to its index cardinality. -/
theorem equalEndpointVectorClutchingProjectiveRank_eq_card
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hdet : A.det ≠ 0)
    (hA : Module.Projective R (equalEndpointVectorClutchingModule (k := k) A)) :
    equalEndpointProjectiveRank k
        (equalEndpointVectorClutchingProjectiveModule k A hA) =
      (Fintype.card ι : ℤ) := by
  -- Apply the generic-rank map to the determinant normal form for this clutching module.
  calc
    equalEndpointProjectiveRank k
        (equalEndpointVectorClutchingProjectiveModule k A hA) =
        equalEndpointProjectiveRankMap.{u, u} k
          (projectiveGrothendieckGroupOf R
            (equalEndpointVectorClutchingProjectiveModule k A hA)) := by
          exact (equalEndpointProjectiveRankMap_apply_of k
            (equalEndpointVectorClutchingProjectiveModule k A hA)).symm
    _ = equalEndpointProjectiveRankMap.{u, u} k
          (equalEndpointLineRankClassMap k
            (Additive.ofMul (Units.mk0 A.det hdet), (Fintype.card ι : ℤ))) := by
          rw [equalEndpointVectorClutchingClass_det_lineRank (k := k) A hdet hA]
    _ = (Fintype.card ι : ℤ) := by
          have hrank :=
            DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k)
              (Additive.ofMul (Units.mk0 A.det hdet), (Fintype.card ι : ℤ))
          simpa [AddMonoidHom.comp_apply] using hrank

/-- Helper for Chap10 Example 10 55 5: a generator-level line-rank normal form makes the
explicit line-plus-rank class map surjective. -/
theorem equalEndpointLineRankClassMap_surjective_of_generator_normalForm
    (hnormal : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) :
    Function.Surjective (equalEndpointLineRankClassMap k) := by
  -- It is enough to lift preimages through the free abelian presentation: generators are handled
  -- by `hnormal`, while the zero, negative, and sum cases use additivity of the class map.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | of M =>
      rcases hnormal M with ⟨unitRatio, hM⟩
      refine ⟨(Additive.ofMul unitRatio, equalEndpointProjectiveRank k M), ?_⟩
      simpa [projectiveGrothendieckGroupOf] using hM.symm
  | neg z hz =>
      rcases hz with ⟨p, hp⟩
      refine ⟨-p, ?_⟩
      simpa using congrArg Neg.neg hp
  | add z w hz hw =>
      rcases hz with ⟨p, hp⟩
      rcases hw with ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      simpa using congrArg₂ (fun a b : projectiveGrothendieckGroup.{u, u} R => a + b) hp hq

/-- Helper for Chap10 Example 10 55 5: residual-line injectivity makes the explicit line-plus-rank
class map injective. -/
theorem equalEndpointLineRankClassMap_injective_of_residual_injective
    (hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) :
    Function.Injective (equalEndpointLineRankClassMap k) := by
  intro x y hxy
  -- First compare generic ranks; the rank computation for the class map identifies the second
  -- product coordinate.
  have hsecond : x.2 = y.2 := by
    have hxrank := DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k) x
    have hyrank := DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k) y
    calc
      x.2 =
          equalEndpointProjectiveRankMap.{u, u} k (equalEndpointLineRankClassMap k x) := by
            simpa [AddMonoidHom.comp_apply] using hxrank.symm
      _ = equalEndpointProjectiveRankMap.{u, u} k (equalEndpointLineRankClassMap k y) := by
            rw [hxy]
      _ = y.2 := by
            simpa [AddMonoidHom.comp_apply] using hyrank
  -- After the rank coordinates agree, cancellation leaves equality of the residual-line classes.
  have hresidual_val :
      (equalEndpointLineResidualClass k x.1.toMul :
          projectiveGrothendieckGroup.{u, u} R) =
        (equalEndpointLineResidualClass k y.1.toMul :
          projectiveGrothendieckGroup.{u, u} R) := by
    have hxy' := hxy
    rw [equalEndpointLineRankClassMap_apply, equalEndpointLineRankClassMap_apply, hsecond] at hxy'
    exact add_right_cancel hxy'
  have hresidual :
      equalEndpointLineResidualClass k x.1.toMul =
        equalEndpointLineResidualClass k y.1.toMul :=
    Subtype.ext hresidual_val
  have hfirst_mul : x.1.toMul = y.1.toMul :=
    hresidual_injective x.1.toMul y.1.toMul hresidual
  have hfirst : x.1 = y.1 := by
    simpa using congrArg Additive.ofMul hfirst_mul
  exact Prod.ext hfirst hsecond

/-- Helper for Chap10 Example 10 55 5: residual-line surjectivity onto the projective rank
kernel makes the explicit line-plus-rank class map surjective. -/
theorem equalEndpointLineRankClassMap_surjective_of_residual_surjective
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    Function.Surjective (equalEndpointLineRankClassMap k) := by
  intro x
  -- Split off the free summand with the same generic rank; the remainder lies in the rank kernel.
  let n : ℤ := equalEndpointProjectiveRankMap.{u, u} k x
  let freeClass : projectiveGrothendieckGroup.{u, u} R :=
    equalEndpointProjectiveRankSection k n
  have hkernel :
      equalEndpointProjectiveRankMap.{u, u} k (x - freeClass) = 0 := by
    rw [map_sub, equalEndpointProjectiveRankSection_rank]
    simp [n]
  let z : (equalEndpointProjectiveRankMap.{u, u} k).ker := ⟨x - freeClass, hkernel⟩
  rcases hsurj z with ⟨unitRatio, hunitRatio⟩
  refine ⟨(Additive.ofMul unitRatio, n), ?_⟩
  have hunitRatio_val :
      (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = x - freeClass :=
    congrArg Subtype.val hunitRatio
  -- Reassemble the residual kernel class and the free rank section.
  calc
    equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, n) =
        (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) + freeClass := by
          simp [equalEndpointLineRankClassMap_apply, freeClass]
    _ = (x - freeClass) + freeClass := by
          rw [hunitRatio_val]
    _ = x := by
          abel

/-- Helper for Chap10 Example 10 55 5: surjectivity of the explicit line-plus-rank class map is
equivalent to residual-line surjectivity onto the projective-rank kernel. -/
theorem equalEndpointLineRankClassMap_surjective_iff_residual_surjective :
    Function.Surjective (equalEndpointLineRankClassMap k) ↔
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  constructor
  · intro hsurj z
    -- Pull a preimage of the underlying rank-zero class through the line-plus-rank map.
    rcases hsurj (z : projectiveGrothendieckGroup.{u, u} R) with ⟨x, hx⟩
    refine ⟨x.1.toMul, ?_⟩
    apply Subtype.ext
    have hxrank := DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k) x
    have hsecond : x.2 = 0 := by
      -- The rank computation forces the integer coordinate of this preimage to vanish.
      calc
        x.2 =
            equalEndpointProjectiveRankMap.{u, u} k (equalEndpointLineRankClassMap k x) := by
              simpa [AddMonoidHom.comp_apply] using hxrank.symm
        _ = equalEndpointProjectiveRankMap.{u, u} k z.1 := by
              rw [hx]
        _ = 0 := z.2
    -- With integer coordinate zero, the preimage equation is exactly the residual-line class.
    have hxval :
        (equalEndpointLineResidualClass k x.1.toMul :
          projectiveGrothendieckGroup.{u, u} R) = z.1 := by
      have hx' := hx
      rw [equalEndpointLineRankClassMap_apply, hsecond] at hx'
      simpa [equalEndpointProjectiveRankSection_apply] using hx'
    exact hxval
  · intro hsurj
    -- The reverse implication is the already isolated reassembly of a residual class plus rank.
    exact equalEndpointLineRankClassMap_surjective_of_residual_surjective (k := k) hsurj

/-- Helper for Chap10 Example 10 55 5: the Picard/Cartan residual exactness clauses make the
explicit line-plus-rank class map bijective. -/
theorem equalEndpointLineRankClassMap_bijective_of_residualExact
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    Function.Bijective (equalEndpointLineRankClassMap k) := by
  -- Picard zero-detection gives residual-line injectivity, and residual surjectivity supplies the
  -- rank-kernel coordinate needed to hit an arbitrary projective K0 class.
  have hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    equalEndpointLineResidualClass_injective_of_zero_picClass (k := k)
      (equalEndpointLineResidualClass_mul k) hzero_pic
  exact ⟨
    equalEndpointLineRankClassMap_injective_of_residual_injective (k := k)
      hresidual_injective,
    equalEndpointLineRankClassMap_surjective_of_residual_surjective (k := k) hsurj⟩

/-- Helper for Chap10 Example 10 55 5: surjectivity of the line-plus-rank class map is exactly
the generator-level line-rank normal form. -/
theorem equalEndpointLineRankClassMap_surjective_iff_generator_normalForm :
    Function.Surjective (equalEndpointLineRankClassMap k) ↔
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M) := by
  constructor
  · intro hsurj M
    -- A preimage of the generator already has the right rank coordinate, by the rank computation
    -- for the explicit class map.
    rcases hsurj (projectiveGrothendieckGroupOf R M) with ⟨x, hx⟩
    refine ⟨x.1.toMul, ?_⟩
    have hxrank := DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k) x
    have hsecond : x.2 = equalEndpointProjectiveRank k M := by
      calc
        x.2 =
            equalEndpointProjectiveRankMap.{u, u} k (equalEndpointLineRankClassMap k x) := by
              simpa [AddMonoidHom.comp_apply] using hxrank.symm
        _ = equalEndpointProjectiveRankMap.{u, u} k (projectiveGrothendieckGroupOf R M) := by
              rw [hx]
        _ = equalEndpointProjectiveRank k M := equalEndpointProjectiveRankMap_apply_of k M
    have hxpair :
        x = (Additive.ofMul x.1.toMul, equalEndpointProjectiveRank k M) := by
      ext
      · cases x.1
        rfl
      · exact hsecond
    calc
      projectiveGrothendieckGroupOf R M = equalEndpointLineRankClassMap k x := hx.symm
      _ = equalEndpointLineRankClassMap k
            (Additive.ofMul x.1.toMul, equalEndpointProjectiveRank k M) := by
              exact congrArg (equalEndpointLineRankClassMap k) hxpair
  · intro hnormal
    -- Conversely, the generator normal form lifts through the free abelian presentation.
    exact equalEndpointLineRankClassMap_surjective_of_generator_normalForm (k := k) hnormal

/-- Helper for Chap10 Example 10 55 5: injectivity of the line-plus-rank class map is exactly
injectivity of residual Milnor-line classes. -/
theorem equalEndpointLineRankClassMap_injective_iff_residual_injective :
    Function.Injective (equalEndpointLineRankClassMap k) ↔
      ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  constructor
  · intro hinj u v hresidual
    -- Pure line coordinates turn residual equality into equality under the class map, so
    -- injectivity recovers the endpoint-unit ratio.
    have hresidual_val :
        (equalEndpointLineResidualClass k u : projectiveGrothendieckGroup.{u, u} R) =
          (equalEndpointLineResidualClass k v : projectiveGrothendieckGroup.{u, u} R) :=
      congrArg Subtype.val hresidual
    have hmap :
        equalEndpointLineRankClassMap k (Additive.ofMul u, (0 : ℤ)) =
          equalEndpointLineRankClassMap k (Additive.ofMul v, (0 : ℤ)) := by
      calc
        equalEndpointLineRankClassMap k (Additive.ofMul u, (0 : ℤ)) =
            (equalEndpointLineResidualClass k u :
              projectiveGrothendieckGroup.{u, u} R) := by
              exact equalEndpointLineRankClassMap_line (k := k) u
        _ = (equalEndpointLineResidualClass k v :
              projectiveGrothendieckGroup.{u, u} R) := hresidual_val
        _ = equalEndpointLineRankClassMap k (Additive.ofMul v, (0 : ℤ)) := by
              exact (equalEndpointLineRankClassMap_line (k := k) v).symm
    have hpair := hinj hmap
    have hfirst : Additive.ofMul u = Additive.ofMul v := congrArg Prod.fst hpair
    simpa using congrArg Additive.toMul hfirst
  · intro hresidual
    -- The forward formal lemma shows residual injectivity is sufficient for map injectivity.
    exact equalEndpointLineRankClassMap_injective_of_residual_injective (k := k) hresidual

/-- Helper for Chap10 Example 10 55 5: bijectivity of the explicit line-plus-rank class map is
equivalent to the Picard/Cartan residual exactness clauses. -/
theorem equalEndpointLineRankClassMap_bijective_iff_residualExact :
    Function.Bijective (equalEndpointLineRankClassMap k) ↔
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  constructor
  · intro hbijective
    -- Injectivity gives residual-line injectivity, which detects the residual-zero Picard class.
    have hresidual_injective : ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
      (equalEndpointLineRankClassMap_injective_iff_residual_injective (k := k)).mp
        hbijective.1
    have hzero_pic : ∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1 :=
      equalEndpointLineResidualClass_zero_picClass_one_of_injective (k := k)
        hresidual_injective
    have hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z :=
      (equalEndpointLineRankClassMap_surjective_iff_residual_surjective (k := k)).mp
        hbijective.2
    exact ⟨hzero_pic, hsurj⟩
  · intro hexact
    -- The reverse direction is the existing Picard/Cartan-to-bijectivity bridge.
    exact equalEndpointLineRankClassMap_bijective_of_residualExact (k := k)
      hexact.1 hexact.2

/-- Helper for Chap10 Example 10 55 5: the source normal-form and residual-injectivity clauses
make the explicit line-plus-rank class map bijective. -/
theorem equalEndpointLineRankClassMap_bijective_of_sourceClauses
    (hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)) :
    Function.Bijective (equalEndpointLineRankClassMap k) := by
  -- The two source clauses are exactly the surjectivity and injectivity halves of the explicit
  -- coordinate map.
  exact ⟨
    equalEndpointLineRankClassMap_injective_of_residual_injective (k := k) hsource.2,
    equalEndpointLineRankClassMap_surjective_of_generator_normalForm (k := k) hsource.1⟩

/-- Helper for Chap10 Example 10 55 5: bijectivity of the line-plus-rank class map is equivalent
to the two source-level clauses it packages. -/
theorem equalEndpointLineRankClassMap_bijective_iff_sourceClauses :
    Function.Bijective (equalEndpointLineRankClassMap k) ↔
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  constructor
  · intro hbijective
    -- Split bijectivity into the generator normal form and residual injectivity via the two
    -- formal equivalences above.
    exact ⟨
      (equalEndpointLineRankClassMap_surjective_iff_generator_normalForm (k := k)).mp
        hbijective.2,
      (equalEndpointLineRankClassMap_injective_iff_residual_injective (k := k)).mp
        hbijective.1⟩
  · intro hsource
    -- Conversely, the existing adapter turns the two clauses into bijectivity.
    exact equalEndpointLineRankClassMap_bijective_of_sourceClauses (k := k) hsource

/-- Helper for Chap10 Example 10 55 5: bijectivity of the explicit line-plus-rank class map
produces a normalized product equivalence. -/
theorem equalEndpointProjectiveRankProduct_exists_of_lineRankClassMap_bijective
    (hbijective : Function.Bijective (equalEndpointLineRankClassMap k)) :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k ∧
      ∀ unitRatio : kˣ,
        e (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) =
            (Additive.ofMul unitRatio, 0) := by
  -- Invert the explicit class map; its rank and residual-line computation rules give the
  -- required normalization of the inverse equivalence.
  let classEquiv : Additive kˣ × ℤ ≃+ projectiveGrothendieckGroup.{u, u} R :=
    AddEquiv.ofBijective (equalEndpointLineRankClassMap k) hbijective
  refine ⟨classEquiv.symm, ?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    have hclass : equalEndpointLineRankClassMap k (classEquiv.symm x) = x := by
      exact classEquiv.apply_symm_apply x
    have hrank :=
      DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k) (classEquiv.symm x)
    calc
      ((AddMonoidHom.snd (Additive kˣ) ℤ).comp classEquiv.symm.toAddMonoidHom) x =
          (classEquiv.symm x).2 := rfl
      _ = equalEndpointProjectiveRankMap.{u, u} k
          (equalEndpointLineRankClassMap k (classEquiv.symm x)) := by
            simpa [AddMonoidHom.comp_apply] using hrank.symm
      _ = equalEndpointProjectiveRankMap.{u, u} k x := by
            rw [hclass]
  · intro unitRatio
    apply classEquiv.injective
    calc
      classEquiv
          (classEquiv.symm (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R)) =
          (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) := by
            exact classEquiv.apply_symm_apply
              (equalEndpointLineResidualClass k unitRatio :
                projectiveGrothendieckGroup.{u, u} R)
      _ = equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, 0) := by
            exact (equalEndpointLineRankClassMap_line (k := k) unitRatio).symm
      _ = classEquiv (Additive.ofMul unitRatio, 0) := rfl

end
