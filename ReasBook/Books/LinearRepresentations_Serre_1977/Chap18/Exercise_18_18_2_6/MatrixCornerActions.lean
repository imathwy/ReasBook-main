import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_2
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3
import Mathlib.RingTheory.Morita.Matrix

noncomputable section

open scoped Matrix.Module

namespace Representation

section EquivalenceCriterion

variable {k : Type} [Field k]

/-- Helper for Exercise 18-18.2-6: when a `Matrix n n D`-module is restricted along the diagonal
embedding `D → Matrix n n D`, the original `k`-scalar action and the descended `D`-action form a
scalar tower. -/
lemma isScalarTower_of_matrix_scalar_action
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Type*} [AddCommGroup M] [Module (Matrix n n D) M] [Module k M]
    [IsScalarTower k (Matrix n n D) M] :
    let _ : Module D M :=
      Module.compHom M (Matrix.scalarAlgHom n k : D →ₐ[k] Matrix n n D).toRingHom
    IsScalarTower k D M := by
  let _ : Module D M :=
    Module.compHom M (Matrix.scalarAlgHom n k : D →ₐ[k] Matrix n n D).toRingHom
  -- Compare the diagonal `D`-action with the pre-existing `k`-action coming from `Matrix n n D`.
  exact
    IsScalarTower.of_algebraMap_smul (R := k) (A := D) (M := M) fun r x ↦ by
      change ((algebraMap k (Matrix n n D)) r) • x = r • x
      rw [IsScalarTower.algebraMap_smul (R := k) (A := Matrix n n D)]

/-- Helper for Exercise 18-18.2-6: a `D`-linear equivalence of coefficient modules induces the
corresponding `Matrix n n D`-linear equivalence on the associated matrix modules. -/
noncomputable def matrix_module_linearEquiv_of_linearEquiv
    {D : Type*} [Ring D]
    {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Type*} [AddCommGroup X] [Module D X] [AddCommGroup Y] [Module D Y]
    (e : X ≃ₗ[D] Y) :
    (n → X) ≃ₗ[Matrix n n D] n → Y := by
  -- Apply the coefficientwise map and use the inverse coefficientwise map for bijectivity.
  refine LinearEquiv.ofBijective (LinearMap.mapMatrixModule n e.toLinearMap) ?_
  constructor
  · intro f g hfg
    ext i
    exact e.injective (congrFun hfg i)
  · intro y
    refine ⟨LinearMap.mapMatrixModule n e.symm.toLinearMap y, ?_⟩
    ext i
    simp

/-- Helper for Exercise 18-18.2-6: on a finite product, the trace of a block-diagonal
endomorphism with a single nonzero block is the trace of that block. -/
lemma trace_pi_single_eq_trace_coordinate_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, Module.Free k (M i)] [∀ i, Module.Finite k (M i)]
    (i : ι) (f : M i →ₗ[k] M i) :
    LinearMap.trace k (∀ j, M j) (LinearMap.piMap (Pi.single i f)) =
      LinearMap.trace k (M i) f := by
  -- The Chapter `6` block-diagonal trace formula reduces the product trace to the sum of the
  -- diagonal block traces, and every block away from `i` vanishes.
  rw [trace_piMap_eq_sum_trace (K := k) (f := Pi.single i f)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Helper for Exercise 18-18.2-6: the corner idempotent `E_{ii}` acts on the standard matrix
module by projecting to the `i`-th coordinate. -/
lemma matrix_corner_action_eq_pi_single_id
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Type*} [AddCommGroup X] [Module D X] [FiniteDimensional D X]
    [Module k X] [IsScalarTower k D X]
    (i : n) :
    (DistribSMul.toLinearMap k (n → X) (Matrix.single i i (1 : D))) =
      LinearMap.piMap (Pi.single i (LinearMap.id : X →ₗ[k] X)) := by
  let f : (j : n) → X →ₗ[k] X := Pi.single i (LinearMap.id : X →ₗ[k] X)
  -- Evaluate the matrix action coordinatewise: only the `i`-th row of `E_{ii}` contributes.
  apply LinearMap.ext
  intro v
  funext j
  change (Matrix.single i i (1 : D) • v) j = (f j) (v j)
  rw [Matrix.Module.single_smul]
  by_cases h : j = i
  · subst h
    simp [f]
  · simp [f, h]

/-- Helper for Exercise 18-18.2-6: the `k`-trace of the corner idempotent on the standard
`Matrix n n D`-module `n → X` is the `k`-dimension of `X`. -/
lemma trace_matrix_corner_idempotent_eq_finrank
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Type*} [AddCommGroup X] [Module D X] [FiniteDimensional D X]
    [Module k X] [IsScalarTower k D X]
    (i : n) :
    LinearMap.trace k (n → X)
      (DistribSMul.toLinearMap k (n → X) (Matrix.single i i (1 : D))) =
        Module.finrank k X := by
  letI : Module.Finite k X := Module.Finite.trans D X
  letI : ∀ j : n, Module.Free k ((fun _ : n ↦ X) j) := fun _ ↦ inferInstance
  letI : ∀ j : n, Module.Finite k ((fun _ : n ↦ X) j) := fun _ ↦ inferInstance
  -- First rewrite the corner action as the product endomorphism with only one identity block.
  rw [matrix_corner_action_eq_pi_single_id (k := k) (D := D) (X := X) i]
  -- Then collapse the product trace to the surviving block trace.
  simpa [LinearMap.trace_id] using
    trace_pi_single_eq_trace_coordinate_factor (k := k) (M := fun _ : n ↦ X) (i := i)
      (f := (LinearMap.id : X →ₗ[k] X))

/-- Helper for Exercise 18-18.2-6: a Morita corner of a finite-dimensional matrix module is
finite-dimensional over the coefficient division ring. -/
lemma finiteDimensional_toModuleCatObj_of_matrix_module
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) D) M]
    [Module k M] [FiniteDimensional k M] [IsScalarTower k (Matrix (Fin m) (Fin m) D) M]
    (j : Fin m) :
    let _ : Module D M :=
      Module.compHom M
        (Matrix.scalarAlgHom (Fin m) k : D →ₐ[k] Matrix (Fin m) (Fin m) D).toRingHom
    let MM : ModuleCat (Matrix (Fin m) (Fin m) D) := ModuleCat.of (Matrix (Fin m) (Fin m) D) M
    let _ : IsScalarTower D (Matrix (Fin m) (Fin m) D) M :=
      MatrixModCat.isScalarTower_toModuleCat (R := D) MM
    let _ : IsScalarTower k D M :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D) (n := Fin m) (M := M)
    FiniteDimensional D (MatrixModCat.toModuleCatObj D (↑MM) j) := by
  intro _ MM _ _
  -- A Morita corner is a submodule of the ambient finite-dimensional `D`-module.
  letI : Module.Finite D M := Module.Finite.of_restrictScalars_finite k D M
  infer_instance

/-- Helper for Exercise 18-18.2-6: the trace of a primitive matrix-corner idempotent is the
`k`-dimension of the corresponding Morita coefficient module. -/
lemma trace_matrix_corner_action_eq_finrank_toModuleCatObj
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) D) M]
    [Module k M] [FiniteDimensional k M] [IsScalarTower k (Matrix (Fin m) (Fin m) D) M]
    (j : Fin m) :
    let _ : Module D M :=
      Module.compHom M
        (Matrix.scalarAlgHom (Fin m) k : D →ₐ[k] Matrix (Fin m) (Fin m) D).toRingHom
    let MM : ModuleCat (Matrix (Fin m) (Fin m) D) := ModuleCat.of (Matrix (Fin m) (Fin m) D) M
    let _ : IsScalarTower D (Matrix (Fin m) (Fin m) D) M :=
      MatrixModCat.isScalarTower_toModuleCat (R := D) MM
    let _ : IsScalarTower k D M :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D) (n := Fin m) (M := M)
    let Xj := MatrixModCat.toModuleCatObj D (↑MM) j
    LinearMap.trace k M
      (DistribSMul.toLinearMap k M (Matrix.single j j (1 : D))) =
        Module.finrank k Xj := by
  intro _ MM _ _ Xj
  let fK : M →ₗ[k] M := DistribSMul.toLinearMap k M (Matrix.single j j (1 : D))
  let YjK : Submodule k M := LinearMap.range fK
  have hf_idem : IsIdempotentElem fK := by
    -- The primitive matrix corner is an idempotent projector on the ambient `k`-space.
    change fK * fK = fK
    ext x
    change
      Matrix.single j j (1 : D) • (Matrix.single j j (1 : D) • x) =
        Matrix.single j j (1 : D) • x
    rw [← smul_assoc]
    congr 1
    simpa using (Matrix.single_mul_single_same (c := (1 : D)) j j j (d := (1 : D)))
  have htraceY :
      LinearMap.trace k M fK = (Module.finrank k YjK : k) := by
    -- The trace of an idempotent equals the dimension of its image.
    letI : Module.Free k YjK := inferInstance
    letI : Module.Finite k YjK := inferInstance
    letI : Module.Free k (LinearMap.ker fK) := inferInstance
    letI : Module.Finite k (LinearMap.ker fK) := inferInstance
    simpa [fK, YjK] using
      (LinearMap.IsProj.trace (R := k) (M := M) (p := YjK) (f := fK)
        (LinearMap.IsIdempotentElem.isProj_range fK hf_idem))
  have hYeq : YjK = Submodule.restrictScalars k Xj := by
    -- The range of the corner projector is exactly the Morita corner cut out by `E_{jj}`.
    ext x
    constructor
    · rintro ⟨y, hy⟩
      change x ∈ Xj
      exact ⟨y, hy⟩
    · intro hx
      change ∃ y : M, Matrix.single j j (1 : D) • y = x at hx
      rcases hx with ⟨y, hy⟩
      exact ⟨y, hy⟩
  -- Rewrite the projector trace through its range and then identify that range with the Morita
  -- corner.
  calc
    LinearMap.trace k M (DistribSMul.toLinearMap k M (Matrix.single j j (1 : D))) =
        LinearMap.trace k M fK := by
          rfl
    _ = Module.finrank k YjK := htraceY
    _ = Module.finrank k (Submodule.restrictScalars k Xj) := by rw [hYeq]
    _ = Module.finrank k Xj := by
          rfl

/-- Helper for Exercise 18-18.2-6: on a matrix-algebra module, the negative primitive corner
projector has reverse characteristic polynomial `(X + 1)^m`, where `m` is the base-field
dimension of the associated Morita corner module. -/
lemma neg_charpoly_reverse_matrix_corner_action_eq_pow_one_add
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {m : ℕ} [NeZero m]
    {M : Type*} [AddCommGroup M] [Module (Matrix (Fin m) (Fin m) D) M]
    [Module k M] [FiniteDimensional k M] [IsScalarTower k (Matrix (Fin m) (Fin m) D) M]
    (j : Fin m) :
    let _ : Module D M :=
      Module.compHom M
        (Matrix.scalarAlgHom (Fin m) k : D →ₐ[k] Matrix (Fin m) (Fin m) D).toRingHom
    let MM : ModuleCat (Matrix (Fin m) (Fin m) D) :=
      ModuleCat.of (Matrix (Fin m) (Fin m) D) M
    let _ : IsScalarTower D (Matrix (Fin m) (Fin m) D) M :=
      MatrixModCat.isScalarTower_toModuleCat (R := D) MM
    let _ : IsScalarTower k D M :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D) (n := Fin m) (M := M)
    let Xj := MatrixModCat.toModuleCatObj D (↑MM) j
    let hX : Submodule k M := Submodule.restrictScalars k Xj
    let _ : FiniteDimensional k hX := inferInstance
    (-DistribSMul.toLinearMap k M (Matrix.single j j (1 : D))).charpoly.reverse =
      (Polynomial.X + 1) ^ Module.finrank k hX := by
  intro _ MM _ _ Xj hX _
  let fK : M →ₗ[k] M := DistribSMul.toLinearMap k M (Matrix.single j j (1 : D))
  have hpos_restrict :
      fK.restrict (show hX ≤ hX.comap fK by
        intro x hx
        change fK x ∈ Xj
        exact ⟨x, rfl⟩) = LinearMap.id := by
    -- The primitive corner projector is literally the identity on its Morita corner submodule.
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.id_coe, id_eq]
    rcases x.property with ⟨y, hy⟩
    rw [← hy]
    change Matrix.single j j (1 : D) • (Matrix.single j j (1 : D) • y) =
      Matrix.single j j (1 : D) • y
    rw [← smul_assoc]
    congr 1
    simp
  let hstable : hX ≤ hX.comap (-fK) := by
    intro x hx
    change (-fK) x ∈ Xj
    exact Xj.neg_mem ⟨x, rfl⟩
  have hrestrict : (-fK).restrict hstable = -LinearMap.id := by
    -- After negating the projector, the restriction becomes `-id` on the same corner.
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
    have hxsub : (fK.restrict (show hX ≤ hX.comap fK by
          intro z hz
          change fK z ∈ Xj
          exact ⟨z, rfl⟩)) x = x := by
      simpa using congrArg (fun g : hX →ₗ[k] hX ↦ g x) hpos_restrict
    have hx : fK x = x := congrArg Subtype.val hxsub
    simp [hx]
  have hmapQ : hX.mapQ hX (-fK) hstable = 0 := by
    -- Modding out by the range kills the projector, so the quotient action is zero.
    apply hX.quot_hom_ext
    intro y
    rw [Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (p := hX) (x := (-fK) y)).2 <| by
      change (-fK) y ∈ Xj
      exact Xj.neg_mem ⟨y, rfl⟩
  have hchar :
      (-fK).charpoly = ((Polynomial.X + 1) ^ Module.finrank k hX) *
        Polynomial.X ^ Module.finrank k (M ⧸ hX) := by
    -- Split the characteristic polynomial into the corner piece and the zero quotient piece.
    rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ ((-fK)) hX hstable, hrestrict, hmapQ,
      LinearMap.charpoly_zero]
    have hone := LinearMap.charpoly_sub_smul (0 : hX →ₗ[k] hX) (1 : k)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hone
  have hreverse_pow :
      (((Polynomial.X : Polynomial k) + 1) ^ Module.finrank k hX).reverse =
        (Polynomial.X + 1) ^ Module.finrank k hX := by
    -- The reverse operation fixes `(X + 1)^n`.
    have hX1 : Polynomial.reverse ((Polynomial.X : Polynomial k) + 1) = Polynomial.X + 1 := by
      rw [show ((Polynomial.X : Polynomial k) + 1) = Polynomial.C (1 : k) + Polynomial.X by
        simp [add_comm]]
      rw [Polynomial.reverse_C_add]
      simp [Polynomial.reverse, add_comm]
    induction Module.finrank k hX with
    | zero =>
        simp [Polynomial.reverse]
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, hX1]
  have hreverse_X_pow :
      (Polynomial.X ^ Module.finrank k (M ⧸ hX) : Polynomial k).reverse = 1 := by
    -- Every trailing `X`-power disappears under `reverse`.
    induction Module.finrank k (M ⧸ hX) with
    | zero =>
        simp [Polynomial.reverse]
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_X, ih]
  -- Dropping the quotient's `X`-factor leaves exactly the binomial corner polynomial.
  rw [hchar, Polynomial.reverse_mul_of_domain, hreverse_pow, hreverse_X_pow]
  all_goals simp

/-- Helper for Exercise 18-18.2-6: on the standard matrix module, the corner matrix
`Matrix.single i i c` acts only on the `i`-th coordinate by scalar multiplication by `c`. -/
lemma matrix_corner_action_eq_pi_single_smul
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Type*} [AddCommGroup X] [Module D X] [Module k X] [IsScalarTower k D X]
    (i : n) (c : D) :
    (DistribSMul.toLinearMap k (n → X) (Matrix.single i i c)) =
      LinearMap.piMap (φ := fun _ : n ↦ X) (ψ := fun _ : n ↦ X)
        (Pi.single i (DistribSMul.toLinearMap k X c)) := by
  -- Evaluate the corner action coordinatewise: only the `i`-th row contributes, and it keeps
  -- only the `i`-th coordinate with coefficient `c`.
  apply LinearMap.ext
  intro v
  funext j
  change
    (Matrix.single i i c • v) j =
      (LinearMap.piMap (φ := fun _ : n ↦ X) (ψ := fun _ : n ↦ X)
        (Pi.single i (DistribSMul.toLinearMap k X c)) v) j
  rw [Matrix.Module.single_smul]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h, h]

end EquivalenceCriterion

end Representation
