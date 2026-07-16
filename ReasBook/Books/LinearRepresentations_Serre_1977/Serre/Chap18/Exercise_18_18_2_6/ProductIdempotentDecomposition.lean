import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_2_6.MatrixCornerActions

noncomputable section

namespace Representation

section EquivalenceCriterion

variable {k : Type} [Field k]

/-- Helper for Exercise 18-18.2-6: multiplication by the `i`-th product idempotent is linear over
the whole product algebra because that idempotent is central. -/
def pi_coordinate_projection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) : M →ₗ[Π i, R i] M where
  toFun x := (Pi.single i (1 : R i)) • x
  map_add' x y := by simp [smul_add]
  map_smul' a x := by
    -- Commute the scalar `a` past the central idempotent `Pi.single i 1`.
    calc
      (Pi.single i (1 : R i)) • (a • x) = (((Pi.single i (1 : R i)) : Π j, R j) * a) • x := by
        rw [mul_smul]
      _ = ((a * Pi.single i (1 : R i)) • x : M) := by
        congr 1
        ext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj]
      _ = a • ((Pi.single i (1 : R i)) • x) := by
        rw [mul_smul]

/-- Helper for Exercise 18-18.2-6: the `i`-th central idempotent in a finite product algebra cuts
out the corresponding coordinate submodule. -/
def pi_coordinate_submodule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) : Submodule (Π i, R i) M :=
  LinearMap.range (pi_coordinate_projection (k := k) (R := R) (M := M) i)

/-- Helper for Exercise 18-18.2-6: membership in the coordinate submodule means coming from the
action of the `i`-th central idempotent. -/
lemma mem_pi_coordinate_submodule_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) {x : M} :
    x ∈ pi_coordinate_submodule (k := k) (R := R) (M := M) i ↔
      ∃ y : M, (Pi.single i (1 : R i)) • y = x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [pi_coordinate_projection] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [pi_coordinate_projection] using hy⟩

/-- Helper for Exercise 18-18.2-6: the image of the `i`-th product idempotent already lies in the
corresponding coordinate submodule. -/
lemma pi_coordinate_projection_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) (x : M) :
    pi_coordinate_projection (k := k) (R := R) (M := M) i x ∈
      pi_coordinate_submodule (k := k) (R := R) (M := M) i := by
  -- The coordinate submodule is defined as the range of the projection map.
  exact ⟨x, rfl⟩

/-- Helper for Exercise 18-18.2-6: the `i`-th coordinate summand inherits the projected action of
the full product algebra. -/
def pi_coordinate_toSubmodule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) : M →ₗ[Π i, R i] pi_coordinate_submodule (k := k) (R := R) (M := M) i :=
  LinearMap.codRestrict
    (pi_coordinate_submodule (k := k) (R := R) (M := M) i)
    (pi_coordinate_projection (k := k) (R := R) (M := M) i)
    (pi_coordinate_projection_mem (k := k) (R := R) (M := M) i)

/-- Helper for Exercise 18-18.2-6: on the `i`-th coordinate summand, the full product action only
depends on the `i`-th factor. -/
lemma pi_coordinate_submodule_action_factors_through_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) (b : Π j, R j)
    (x : pi_coordinate_submodule (k := k) (R := R) (M := M) i) :
    b • (x : M) = (Pi.single i (b i)) • (x : M) := by
  rcases x with ⟨x, hx⟩
  rcases (mem_pi_coordinate_submodule_iff (k := k) (R := R) (M := M) i).1 hx with ⟨y, rfl⟩
  -- Unpack the coordinate summand as the image of the `i`-th central idempotent.
  calc
    b • ((Pi.single i (1 : R i)) • y) =
        (((b : Π j, R j) * Pi.single i (1 : R i)) • y : M) := by
          rw [← mul_smul]
    _ = ((Pi.single i (b i) : Π j, R j) • y : M) := by
          congr 1
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]
    _ = ((((Pi.single i (b i) : Π j, R j) * Pi.single i (1 : R i))) • y : M) := by
          congr 1
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]
    _ = (Pi.single i (b i)) • ((Pi.single i (1 : R i)) • y) := by
          rw [mul_smul]

/-- Helper for Exercise 18-18.2-6: the `i`-th central idempotent acts as the identity on its own
coordinate summand. -/
lemma pi_coordinate_submodule_single_smul_eq_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι)
    (x : pi_coordinate_submodule (k := k) (R := R) (M := M) i) :
    (Pi.single i (1 : R i)) • (x : M) = x := by
  rcases x with ⟨x, hx⟩
  rcases (mem_pi_coordinate_submodule_iff (k := k) (R := R) (M := M) i).1 hx with ⟨y, rfl⟩
  -- Squaring the central idempotent leaves its image fixed.
  rw [← mul_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

/-- Helper for Exercise 18-18.2-6: a central idempotent from a different factor annihilates the
`j`-th coordinate summand. -/
lemma pi_coordinate_submodule_single_smul_eq_zero_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    {i j : ι} (hij : i ≠ j)
    (x : pi_coordinate_submodule (k := k) (R := R) (M := M) j) :
    (Pi.single i (1 : R i)) • (x : M) = 0 := by
  -- Reduce the action to the `j`-th coordinate, where the off-diagonal idempotent vanishes.
  have h :=
    pi_coordinate_submodule_action_factors_through_eval
      (k := k) (R := R) (M := M) j (Pi.single i (1 : R i)) x
  have hij0 : (Pi.single i (1 : R i) : Π l, R l) j = 0 := by
    simp [Pi.single_eq_of_ne (show j ≠ i from hij.symm)]
  calc
    (Pi.single i (1 : R i)) • (x : M) = (Pi.single j ((Pi.single i (1 : R i) : Π l, R l) j)) •
        (x : M) := h
    _ = 0 := by
        rw [hij0]
        calc
          (Pi.single j (0 : R j) : Π l, R l) • (x : M) = (0 : Π l, R l) • (x : M) := by
            congr 1
            ext l
            by_cases hl : l = j
            · subst hl
              simp
            · simp [Pi.single_eq_of_ne hl]
          _ = 0 := by
            simp

/-- Helper for Exercise 18-18.2-6: collect all coordinate projections into a map from the module
to the product of its coordinate summands. -/
def pi_coordinate_decompose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M] :
    M →ₗ[Π i, R i] (∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
  LinearMap.pi fun i ↦ pi_coordinate_toSubmodule (k := k) (R := R) (M := M) i

/-- Helper for Exercise 18-18.2-6: sum the coordinate summands back into the ambient module. -/
def pi_coordinate_reassemble
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M] :
    (∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i) →ₗ[Π i, R i] M :=
  LinearMap.lsum (Π i, R i)
    (fun i ↦ pi_coordinate_submodule (k := k) (R := R) (M := M) i)
    ℕ
    fun i ↦ (pi_coordinate_submodule (k := k) (R := R) (M := M) i).subtype

/-- Helper for Exercise 18-18.2-6: summing the idempotent pieces of a vector recovers the vector
itself. -/
lemma pi_coordinate_reassemble_decompose_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (x : M) :
    pi_coordinate_reassemble (k := k) (R := R) (M := M)
        (pi_coordinate_decompose (k := k) (R := R) (M := M) x) =
      x := by
  -- The product idempotents sum to `1`, so their images reconstruct `x`.
  simpa [pi_coordinate_reassemble, pi_coordinate_decompose, pi_coordinate_toSubmodule,
    pi_coordinate_projection] using
    show (∑ i : ι, (Pi.single i (1 : R i)) • x) = x by
      rw [← Finset.sum_smul]
      calc
        (∑ i : ι, (Pi.single i (1 : R i) : Π j, R j)) • x = (1 : Π j, R j) • x := by
          congr 1
          ext j
          simp
        _ = x := by
          simp

/-- Helper for Exercise 18-18.2-6: decomposing a tuple of coordinate vectors and then summing it
back leaves each coordinate unchanged. -/
lemma pi_coordinate_decompose_reassemble_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (x : ∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i) :
    pi_coordinate_decompose (k := k) (R := R) (M := M)
        (pi_coordinate_reassemble (k := k) (R := R) (M := M) x) =
      x := by
  funext i
  apply Subtype.ext
  -- Only the `i`-th idempotent acts nontrivially on the `i`-th summand.
  simpa [pi_coordinate_decompose, pi_coordinate_reassemble, pi_coordinate_toSubmodule,
    pi_coordinate_projection] using
    show (∑ j : ι, (Pi.single i (1 : R i)) • (x j : M)) = (x i : M) by
      rw [Finset.sum_eq_single i]
      · simpa using pi_coordinate_submodule_single_smul_eq_self
          (k := k) (R := R) (M := M) i (x i)
      · intro j _ hji
        simpa using pi_coordinate_submodule_single_smul_eq_zero_of_ne
          (k := k) (R := R) (M := M) (show i ≠ j from hji.symm) (x j)
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- Helper for Exercise 18-18.2-6: the coordinate projection map is bijective, with inverse given
by summing the coordinate inclusions. -/
lemma pi_coordinate_decompose_bijective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M] :
    Function.Bijective (pi_coordinate_decompose (k := k) (R := R) (M := M)) := by
  constructor
  · intro x y hxy
    -- Apply the reassembly map to both sides and use the verified left inverse.
    have hxy' :=
      congrArg (pi_coordinate_reassemble (k := k) (R := R) (M := M)) hxy
    simpa [pi_coordinate_reassemble_decompose_apply] using hxy'
  · intro x
    -- The explicit inverse is the sum of the coordinate-submodule inclusions.
    exact ⟨pi_coordinate_reassemble (k := k) (R := R) (M := M) x,
      pi_coordinate_decompose_reassemble_apply (k := k) (R := R) (M := M) x⟩

/-- Helper for Exercise 18-18.2-6: every module over a finite product algebra splits as the
product of the coordinate summands cut out by the central idempotents. -/
noncomputable def pi_idempotent_linearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M] :
    M ≃ₗ[Π i, R i] (∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
  LinearEquiv.ofBijective
    (pi_coordinate_decompose (k := k) (R := R) (M := M))
    (pi_coordinate_decompose_bijective (k := k) (R := R) (M := M))

/-- Helper for Exercise 18-18.2-6: the `i`-th coordinate summand carries the natural action of the
`i`-th factor, implemented through the corresponding product idempotent. -/
@[reducible] def pi_coordinate_submodule_factorModule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) :
    Module (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) where
  smul a x :=
    ⟨(Pi.single i a) • (x : M),
      (pi_coordinate_submodule (k := k) (R := R) (M := M) i).smul_mem (Pi.single i a) x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((Pi.single i (1 : R i)) • (x : M)) = x
    simpa using
      pi_coordinate_submodule_single_smul_eq_self (k := k) (R := R) (M := M) i x
  mul_smul a b x := by
    apply Subtype.ext
    change ((Pi.single i (a * b) : Π j, R j) • (x : M)) =
      ((Pi.single i a : Π j, R j) • ((Pi.single i b : Π j, R j) • (x : M)))
    rw [← mul_smul]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  smul_zero a := by
    apply Subtype.ext
    change ((Pi.single i a : Π j, R j) • (0 : M)) = 0
    simp
  smul_add a x y := by
    apply Subtype.ext
    change ((Pi.single i a : Π j, R j) • ((x : M) + y)) =
      ((Pi.single i a : Π j, R j) • (x : M)) + ((Pi.single i a : Π j, R j) • (y : M))
    simp
  zero_smul x := by
    apply Subtype.ext
    change ((Pi.single i (0 : R i) : Π j, R j) • (x : M)) = 0
    simp
  add_smul a b x := by
    apply Subtype.ext
    change ((Pi.single i (a + b) : Π j, R j) • (x : M)) =
      ((Pi.single i a : Π j, R j) • (x : M)) + ((Pi.single i b : Π j, R j) • (x : M))
    rw [← add_smul]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]

/-- Helper for Exercise 18-18.2-6: the factor action on the `i`-th coordinate summand is
compatible with the ambient `k`-scalar action. -/
lemma pi_coordinate_submodule_factor_isScalarTower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    (i : ι) :
    let Xi := pi_coordinate_submodule (k := k) (R := R) (M := M) i
    let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
    IsScalarTower k (R i) Xi := by
  let B := Π j, R j
  let Xi := pi_coordinate_submodule (k := k) (R := R) (M := M) i
  let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
  -- Compare the induced factor action with the original `k`-action on the ambient module.
  exact
    IsScalarTower.of_algebraMap_smul (R := k) (A := R i) (M := Xi) fun r x ↦ by
      apply Subtype.ext
      have hcoord :=
        pi_coordinate_submodule_action_factors_through_eval
          (k := k) (R := R) (M := M) i ((algebraMap k B) r) x
      calc
        ((((algebraMap k (R i)) r) • x : Xi) : M) =
            ((Pi.single i ((algebraMap k (R i)) r) : B) • (x : M)) := by
              rfl
        _ = ((Pi.single i (((algebraMap k B) r) i) : B) • (x : M)) := by
              rfl
        _ = ((algebraMap k B) r) • (x : M) := by
              symm
              exact hcoord
        _ = r • (x : M) := by
              simpa using IsScalarTower.algebraMap_smul (R := k) (A := B) r (x : M)

/-- Helper for Exercise 18-18.2-6: the trace of `Pi.single i a` on a module over a product algebra
is the trace of the induced action on the `i`-th coordinate summand. -/
lemma trace_pi_single_action_eq_trace_coordinate_action
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [FiniteDimensional k M] [IsScalarTower k (Π i, R i) M]
    (i : ι) (a : R i) :
    let Xi := pi_coordinate_submodule (k := k) (R := R) (M := M) i
    let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
    let _ : IsScalarTower k (R i) Xi :=
      pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) i
    LinearMap.trace k M (DistribSMul.toLinearMap k M (Pi.single i a)) =
      LinearMap.trace k Xi (DistribSMul.toLinearMap k Xi a) := by
  let Xi := pi_coordinate_submodule (k := k) (R := R) (M := M) i
  let _ : Module (R i) Xi := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
  let _ : IsScalarTower k (R i) Xi :=
    pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) i
  let e := pi_idempotent_linearEquiv (k := k) (R := R) (M := M)
  let ek := e.restrictScalars k
  let f :
      (j : ι) →
        pi_coordinate_submodule (k := k) (R := R) (M := M) j →ₗ[k]
          pi_coordinate_submodule (k := k) (R := R) (M := M) j :=
    fun j ↦
      if h : j = i then by
        subst h
        exact DistribSMul.toLinearMap k Xi a
      else 0
  have hconj :
      ek.conj (DistribSMul.toLinearMap k M (Pi.single i a)) =
        LinearMap.piMap f := by
    -- Conjugating by the product-idempotent decomposition turns `Pi.single i a` into the
    -- block-diagonal endomorphism supported only on the `i`-th coordinate.
    apply LinearMap.ext
    intro x
    funext j
    rcases ek.surjective x with ⟨y, rfl⟩
    by_cases hj : j = i
    · subst j
      apply Subtype.ext
      rw [LinearEquiv.conj_apply_apply]
      simp [ek, e, pi_idempotent_linearEquiv,
        pi_coordinate_decompose, pi_coordinate_toSubmodule, pi_coordinate_projection, f,
        pi_coordinate_submodule_factorModule]
      rfl
    · apply Subtype.ext
      simp [LinearEquiv.conj_apply_apply, ek, e, pi_idempotent_linearEquiv,
        pi_coordinate_decompose, pi_coordinate_toSubmodule, pi_coordinate_projection, f, hj]
      rw [← mul_smul]
      have hmul :
          ((Pi.single i a : Π l, R l) * (Pi.single j (1 : R j) : Π l, R l)) = 0 := by
        ext l
        by_cases hli : l = i
        · subst hli
          simp [Pi.single_eq_of_ne (fun h => hj h.symm)]
        · by_cases hlj : l = j
          · subst hlj
            simp [Pi.single_eq_of_ne hj]
          · simp [Pi.single_eq_of_ne hlj, Pi.single_eq_of_ne hli]
      rw [hmul, zero_smul]
  have hpi :
      LinearMap.piMap f =
        LinearMap.piMap
          (Pi.single i
            (DistribSMul.toLinearMap k
              (pi_coordinate_submodule (k := k) (R := R) (M := M) i) a)) := by
    apply LinearMap.ext
    intro x
    funext j
    by_cases hj : j = i
    · subst j
      simp [f]
    · simp [f, hj]
  let _ :
      ∀ j, Module.Finite k (pi_coordinate_submodule (k := k) (R := R) (M := M) j) := fun j ↦
    Module.Finite.of_injective
      ((pi_coordinate_submodule (k := k) (R := R) (M := M) j).subtype.restrictScalars k)
      Subtype.val_injective
  -- Trace is invariant under conjugation, and the product trace keeps only the `i`-th block.
  calc
        LinearMap.trace k M (DistribSMul.toLinearMap k M (Pi.single i a)) =
        LinearMap.trace k (∀ j, pi_coordinate_submodule (k := k) (R := R) (M := M) j)
          (ek.conj (DistribSMul.toLinearMap k M (Pi.single i a))) := by
            symm
            exact LinearMap.trace_conj' (DistribSMul.toLinearMap k M (Pi.single i a))
              ek
    _ = LinearMap.trace k (∀ j, pi_coordinate_submodule (k := k) (R := R) (M := M) j)
          (LinearMap.piMap f) := by
            rw [hconj]
    _ = LinearMap.trace k Xi (DistribSMul.toLinearMap k Xi a) := by
          rw [hpi]
          change
            LinearMap.trace k
                (∀ j, pi_coordinate_submodule (k := k) (R := R) (M := M) j)
                (LinearMap.piMap
                  (Pi.single i
                    (DistribSMul.toLinearMap k
                      (pi_coordinate_submodule (k := k) (R := R) (M := M) i) a))) =
              LinearMap.trace k Xi (DistribSMul.toLinearMap k Xi a)
          simpa using
            trace_pi_single_eq_trace_coordinate_factor (k := k)
              (M := fun j ↦ pi_coordinate_submodule (k := k) (R := R) (M := M) j)
              (i := i)
              (f := DistribSMul.toLinearMap k
                (pi_coordinate_submodule (k := k) (R := R) (M := M) i) a)

/-- Helper for Exercise 18-18.2-6: a factorwise linear equivalence between coordinate summands is
automatically linear for the ambient product algebra. -/
noncomputable def coordinate_linearEquiv_is_product_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type*} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [IsScalarTower k (Π i, R i) M]
    {N : Type*} [AddCommGroup N] [Module (Π i, R i) N] [Module k N]
    [IsScalarTower k (Π i, R i) N]
    (i : ι) :
    let XiM := pi_coordinate_submodule (k := k) (R := R) (M := M) i
    let XiN := pi_coordinate_submodule (k := k) (R := R) (M := N) i
    let _ : Module (R i) XiM := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
    let _ : Module (R i) XiN := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := N) i
    (XiM ≃ₗ[R i] XiN) → XiM ≃ₗ[Π j, R j] XiN := by
  let XiM := pi_coordinate_submodule (k := k) (R := R) (M := M) i
  let XiN := pi_coordinate_submodule (k := k) (R := R) (M := N) i
  let _ : Module (R i) XiM := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
  let _ : Module (R i) XiN := pi_coordinate_submodule_factorModule (k := k) (R := R) (M := N) i
  dsimp
  intro e
  -- The underlying equivalence is already additive and bijective; only ambient product-linearity
  -- remains to be checked.
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro b x
  -- On both source and target, the ambient product action factors through the `i`-th
  -- coordinate, so `R i`-linearity of `e` is enough.
  have hx :
      b • x = ((b i) • x : XiM) := by
    have hx_single :
        ((((b i) • x : XiM)) : M) =
          (Pi.single i (b i)) • (x : M) := by
      rfl
    apply Subtype.ext
    calc
      b • (x : M) = (Pi.single i (b i)) • (x : M) := by
        exact
          pi_coordinate_submodule_action_factors_through_eval
            (k := k) (R := R) (M := M) i b x
      _ = (((b i) • x : XiM) : M) := by
            symm
            exact hx_single
  have hy :
      b • e x = ((b i) • e x : XiN) := by
    have hy_single :
        ((((b i) • e x : XiN)) : N) =
          (Pi.single i (b i)) • (e x : N) := by
      rfl
    apply Subtype.ext
    calc
      b • (e x : N) = (Pi.single i (b i)) • (e x : N) := by
        exact
          pi_coordinate_submodule_action_factors_through_eval
            (k := k) (R := R) (M := N) i b (e x)
      _ = (((b i) • e x : XiN) : N) := by
            symm
            exact hy_single
  calc
    e (b • x) = e ((b i) • x) := by rw [hx]
    _ = (b i) • e x := e.map_smul (b i) x
    _ = b • e x := by rw [hy]

end EquivalenceCriterion

end Representation
