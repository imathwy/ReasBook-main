import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace SetValuedOperator

-- Semantic recall: `lean_leansearch` did not surface a more specific monotone-operator owner, and
-- local precedent from `Chap02.Definition_2_23` already uses the names
-- `IsStrictlyMonotone` and `IsStronglyMonotone`, so Chapter 22 reuses that API on
-- `SetValuedOperator`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 22.1 (1): a set-valued operator is paramonotone when it is monotone and every
pair of graph points with vanishing monotonicity pairing remains in the graph after swapping the
values. -/
class IsParamonotone (A : SetValuedOperator H H) : Prop where
  /-- Paramonotonicity includes ordinary monotonicity. -/
  monotone : A.IsMonotone
  /-- Vanishing monotonicity pairing allows the graph values to be swapped. -/
  swap :
    ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → ⟪x - y, u - v⟫_ℝ = 0 → v ∈ A x ∧ u ∈ A y

/-- Paramonotonicity includes ordinary monotonicity. -/
theorem IsParamonotone.isMonotone {A : SetValuedOperator H H} (hA : A.IsParamonotone) :
    A.IsMonotone :=
  hA.monotone

/-- Paramonotonicity is available to typeclass search as monotonicity. -/
instance instIsMonotoneOfIsParamonotone
    {A : SetValuedOperator H H} [hA : A.IsParamonotone] : A.IsMonotone :=
  hA.monotone

/-- A paramonotone operator allows swapping graph values when the monotonicity pairing vanishes. -/
theorem IsParamonotone.swap_mem {A : SetValuedOperator H H} (hA : A.IsParamonotone)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y)
    (hinner : ⟪x - y, u - v⟫_ℝ = 0) :
    v ∈ A x ∧ u ∈ A y :=
  hA.swap hu hv hinner

/-- Definition 22.1 (2): a set-valued operator is strictly monotone when distinct graph points in
the first coordinate have strictly positive monotonicity pairing. -/
def IsStrictlyMonotone (A : SetValuedOperator H H) : Prop :=
  ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → x ≠ y → 0 < ⟪x - y, u - v⟫_ℝ

/-- A strictly monotone operator satisfies the defining strict inequality on every pair of graph
points with distinct first coordinates. -/
theorem IsStrictlyMonotone.ineq {A : SetValuedOperator H H} (hA : A.IsStrictlyMonotone)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y) (hxy : x ≠ y) :
    0 < ⟪x - y, u - v⟫_ℝ := by
  -- This is exactly the defining strict inequality.
  exact hA hu hv hxy

/-- A strictly monotone set-valued operator is monotone. -/
theorem IsStrictlyMonotone.isMonotone {A : SetValuedOperator H H} (hA : A.IsStrictlyMonotone) :
    A.IsMonotone := by
  rw [isMonotone_iff]
  intro x u y v hu hv
  by_cases hxy : x = y
  · subst hxy
    simp
  · exact le_of_lt (hA hu hv hxy)

/-- A strictly monotone set-valued operator is paramonotone. -/
theorem IsStrictlyMonotone.isParamonotone {A : SetValuedOperator H H}
    (hA : A.IsStrictlyMonotone) :
    A.IsParamonotone := by
  refine ⟨hA.isMonotone, ?_⟩
  intro x u y v hu hv hinner
  by_cases hxy : x = y
  · subst hxy
    exact ⟨hv, hu⟩
  · have hpos : 0 < ⟪x - y, u - v⟫_ℝ := hA.ineq hu hv hxy
    exact False.elim <| (lt_irrefl (0 : ℝ)) (hinner ▸ hpos)

/-- Definition 22.1 (3): a set-valued operator is uniformly monotone with modulus `φ` when `φ` is
increasing, vanishes only at `0`, and uniformly bounds the monotonicity pairing from below. -/
class IsUniformlyMonotone (A : SetValuedOperator H H) (φ : outParam (NNReal → EReal)) : Prop where
  /-- The modulus of a uniformly monotone operator is monotone. -/
  monotone : Monotone φ
  /-- The modulus of a uniformly monotone operator vanishes exactly at `0`. -/
  eq_zero_iff : ∀ r : NNReal, φ r = 0 ↔ r = 0
  /-- Uniform monotonicity gives a lower bound on the monotonicity pairing. -/
  lower_bound :
    ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y →
      φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal)

/-- A uniformly monotone modulus is monotone. -/
theorem IsUniformlyMonotone.modulusMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ) :
    Monotone φ :=
  hA.monotone

/-- A uniformly monotone modulus vanishes exactly at `0`. -/
theorem IsUniformlyMonotone.modulus_eq_zero_iff
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ)
    (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  hA.eq_zero_iff r

/-- A uniformly monotone operator satisfies the defining lower bound on every pair of graph
points. -/
theorem IsUniformlyMonotone.ineq
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y) :
    φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal) :=
  hA.lower_bound hu hv

/-- A uniformly monotone set-valued operator is monotone. -/
theorem IsUniformlyMonotone.isMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ) :
    A.IsMonotone := by
  rw [isMonotone_iff]
  intro x u y v hu hv
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    have hφ0 : φ 0 = 0 := (hA.modulus_eq_zero_iff 0).2 rfl
    calc
      (0 : EReal) = φ 0 := by simp [hφ0]
      _ ≤ φ ‖x - y‖₊ := hA.modulusMonotone (show (0 : NNReal) ≤ ‖x - y‖₊ from bot_le)
  have hinner : (0 : EReal) ≤ (⟪x - y, u - v⟫_ℝ : EReal) := le_trans hφ_nonneg (hA.ineq hu hv)
  exact_mod_cast hinner

/-- Uniform monotonicity is available to typeclass search as monotonicity. -/
instance instIsMonotoneOfIsUniformlyMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} [hA : A.IsUniformlyMonotone φ] :
    A.IsMonotone :=
  hA.isMonotone

/-- A uniformly monotone set-valued operator is strictly monotone. -/
theorem IsUniformlyMonotone.isStrictlyMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ) :
    A.IsStrictlyMonotone := by
  intro x u y v hu hv hxy
  have hdist_pos : (0 : NNReal) < ‖x - y‖₊ := by
    exact_mod_cast norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    have hφ0 : φ 0 = 0 := (hA.modulus_eq_zero_iff 0).2 rfl
    calc
      (0 : EReal) = φ 0 := by simp [hφ0]
      _ ≤ φ ‖x - y‖₊ := hA.modulusMonotone (show (0 : NNReal) ≤ ‖x - y‖₊ from bot_le)
  have hφ_ne_zero : φ ‖x - y‖₊ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hdist_pos) ((hA.modulus_eq_zero_iff ‖x - y‖₊).1 hzero)
  have hφ_pos : (0 : EReal) < φ ‖x - y‖₊ :=
    lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
  have hinner : (0 : EReal) < (⟪x - y, u - v⟫_ℝ : EReal) := lt_of_lt_of_le hφ_pos (hA.ineq hu hv)
  exact_mod_cast hinner

/-- Uniform monotonicity is available to typeclass search as strict monotonicity. -/
instance instIsStrictlyMonotoneOfIsUniformlyMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} [hA : A.IsUniformlyMonotone φ] :
    A.IsStrictlyMonotone :=
  hA.isStrictlyMonotone

/-- Definition 22.1 (4): a set-valued operator is `β`-strongly monotone when `β > 0` and the
monotonicity pairing dominates `β ‖x - y‖²` at every pair of graph points. -/
class IsStronglyMonotone (A : SetValuedOperator H H) (β : outParam ℝ) : Prop where
  /-- The parameter of a strongly monotone operator is positive. -/
  beta_pos : 0 < β
  /-- Strong monotonicity gives the defining quadratic lower bound. -/
  lower_bound :
    ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → β * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ

/-- The parameter of a strongly monotone set-valued operator is positive. -/
theorem IsStronglyMonotone.pos
    {A : SetValuedOperator H H} {β : ℝ} (hA : A.IsStronglyMonotone β) :
    0 < β :=
  hA.beta_pos

/-- A strongly monotone set-valued operator satisfies the defining lower bound on every pair of
graph points. -/
theorem IsStronglyMonotone.ineq
    {A : SetValuedOperator H H} {β : ℝ} (hA : A.IsStronglyMonotone β)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y) :
    β * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ :=
  hA.lower_bound hu hv

/-- A strongly monotone set-valued operator is strictly monotone. -/
theorem IsStronglyMonotone.isStrictlyMonotone
    {A : SetValuedOperator H H} {β : ℝ} (hA : A.IsStronglyMonotone β) :
    A.IsStrictlyMonotone := by
  intro x u y v hu hv hxy
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsq : 0 < ‖x - y‖ ^ 2 := pow_pos hnorm 2
  have hlower : 0 < β * ‖x - y‖ ^ 2 := mul_pos hA.pos hsq
  exact lt_of_lt_of_le hlower (hA.ineq hu hv)

/-- Strong monotonicity is available to typeclass search as strict monotonicity. -/
instance instIsStrictlyMonotoneOfIsStronglyMonotone
    {A : SetValuedOperator H H} {β : ℝ} [hA : A.IsStronglyMonotone β] :
    A.IsStrictlyMonotone :=
  hA.isStrictlyMonotone

/-- A strongly monotone set-valued operator is monotone. -/
theorem IsStronglyMonotone.isMonotone
    {A : SetValuedOperator H H} {β : ℝ} (hA : A.IsStronglyMonotone β) :
    A.IsMonotone :=
  hA.isStrictlyMonotone.isMonotone

/-- Strong monotonicity is available to typeclass search as monotonicity. -/
instance instIsMonotoneOfIsStronglyMonotone
    {A : SetValuedOperator H H} {β : ℝ} [hA : A.IsStronglyMonotone β] :
    A.IsMonotone :=
  hA.isMonotone

/-- Helper for Definition 22.1: membership in the shifted operator `A - β Id` is equivalent to
membership of the translated vector in the original fiber. -/
private theorem mem_add_neg_smul_id_iff
    (A : SetValuedOperator H H) (β : ℝ) (x w : H) :
    w ∈ (A + (-β) • ((id : H → H).toSetValuedOperator)) x ↔ w + β • x ∈ A x := by
  constructor
  · intro hw
    -- Decompose the shifted graph point and cancel the `(-β) • x` contribution.
    rcases Set.mem_add.mp hw with ⟨u, hu, z, hz, huz⟩
    rw [Pi.smul_apply] at hz
    rcases Set.mem_smul_set.mp hz with ⟨z', hz', rfl⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hz'
    subst z'
    have huw : w + β • x = u := by
      have hsum : w + β • x = (u + (-β) • x) + β • x := by
        simpa using congrArg (fun t : H ↦ t + β • x) huz.symm
      calc
        w + β • x = (u + (-β) • x) + β • x := hsum
        _ = u + ((-β) • x + β • x) := by abel_nf
        _ = u := by simp
    simpa [huw] using hu
  · intro hw
    -- Rebuild the shifted witness from the translated element of `A x`.
    have hshift_mem : (-β) • x ∈ ((-β) • ((id : H → H).toSetValuedOperator)) x := by
      rw [Pi.smul_apply, Set.mem_smul_set]
      exact ⟨x, by simp [Function.toSetValuedOperator_apply], rfl⟩
    have hdecomp : (w + β • x) + (-β) • x = w := by
      calc
        (w + β • x) + (-β) • x = w + (β • x + (-β) • x) := by abel_nf
        _ = w := by simp
    exact Set.mem_add.2 ⟨w + β • x, hw, (-β) • x, hshift_mem, hdecomp⟩

/-- Helper for Definition 22.1: shifting both graph values by `β Id` adds the quadratic term
`β ‖x - y‖²` to the monotonicity pairing. -/
private theorem inner_sub_add_smul_sub_eq
    (β : ℝ) (x y u v : H) :
    ⟪x - y, (u + β • x) - (v + β • y)⟫_ℝ =
      ⟪x - y, u - v⟫_ℝ + β * ‖x - y‖ ^ 2 := by
  have hsplit : (u + β • x) - (v + β • y) = (u - v) + β • (x - y) := by
    -- Rearranging the shifted outputs isolates the original difference and the `β Id` term.
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Expand the right slot linearly and identify the self-inner-product with the squared norm.
  calc
    ⟪x - y, (u + β • x) - (v + β • y)⟫_ℝ
        = ⟪x - y, u - v⟫_ℝ + ⟪x - y, β • (x - y)⟫_ℝ := by
            rw [hsplit, inner_add_right]
    _ = ⟪x - y, u - v⟫_ℝ + β * ‖x - y‖ ^ 2 := by
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- The source wording `A - β Id` is monotone exactly when the corresponding lower-bound
inequality holds; the positivity of `β` remains part of strong monotonicity. -/
theorem isStronglyMonotone_iff_add_neg_smul_id_isMonotone
    (A : SetValuedOperator H H) (β : ℝ) :
    A.IsStronglyMonotone β ↔
      0 < β ∧ (A + (-β) • id.toSetValuedOperator).IsMonotone := by
  constructor
  · intro hA
    constructor
    · exact hA.pos
    · rw [isMonotone_iff]
      intro x u y v hu hv
      -- Pull the shifted graph points back to graph points of `A`.
      have huA : u + β • x ∈ A x :=
        (mem_add_neg_smul_id_iff (A := A) (β := β) (x := x) (w := u)).1 hu
      have hvA : v + β • y ∈ A y :=
        (mem_add_neg_smul_id_iff (A := A) (β := β) (x := y) (w := v)).1 hv
      have hineq : β * ‖x - y‖ ^ 2 ≤ ⟪x - y, (u + β • x) - (v + β • y)⟫_ℝ :=
        hA.ineq huA hvA
      -- Normalize the shifted pairing and cancel the common quadratic term.
      rw [inner_sub_add_smul_sub_eq β x y u v] at hineq
      linarith
  · rintro ⟨hβ, hmono⟩
    refine ⟨hβ, ?_⟩
    rw [isMonotone_iff] at hmono
    intro x u y v hu hv
    -- Insert the graph points of `A` into the shifted operator by subtracting `β Id`.
    have hu_shift : u - β • x ∈ (A + (-β) • ((id : H → H).toSetValuedOperator)) x :=
      (mem_add_neg_smul_id_iff (A := A) (β := β) (x := x) (w := u - β • x)).2 <| by
        simpa [sub_eq_add_neg]
    have hv_shift : v - β • y ∈ (A + (-β) • ((id : H → H).toSetValuedOperator)) y :=
      (mem_add_neg_smul_id_iff (A := A) (β := β) (x := y) (w := v - β • y)).2 <| by
        simpa [sub_eq_add_neg]
    have hshift : 0 ≤ ⟪x - y, (u - β • x) - (v - β • y)⟫_ℝ :=
      hmono hu_shift hv_shift
    have hnormalized : 0 ≤ ⟪x - y, (u + (-β) • x) - (v + (-β) • y)⟫_ℝ := by
      simpa [sub_eq_add_neg] using hshift
    -- Rewriting the shifted pairing recovers the strong-monotonicity lower bound.
    rw [inner_sub_add_smul_sub_eq (-β) x y u v] at hnormalized
    linarith

end SetValuedOperator
