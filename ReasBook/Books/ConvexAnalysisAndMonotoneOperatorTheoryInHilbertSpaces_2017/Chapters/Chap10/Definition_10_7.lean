import Mathlib.Analysis.Convex.Strong
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Jensen gap of an `]-∞,+∞]`-valued function at the convex combination with weight `α`. -/
noncomputable def jensenGap (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ) (x y : H) : EReal :=
  (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) -
    (f (α • x + (1 - α) • y) : EReal)

/-- Definition 10.7 (3): a function is uniformly convex on a nonempty subset `C` of its effective
domain with modulus `φ` when `φ` is increasing, vanishes only at `0`, and the uniform Jensen
inequality holds for all points of `C`. -/
def UniformlyConvexOn
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) (φ : NNReal → EReal) : Prop :=
  C.Nonempty ∧
    C ⊆ effectiveDomain f ∧
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y

/-- Definition 10.7 (1): a proper `]-∞,+∞]`-valued function is uniformly convex with modulus `φ`
when `φ` is increasing, vanishes only at `0`, and the uniform Jensen inequality holds on the
effective domain of `f`. -/
def UniformlyConvex (f : H → Set.Ioi (⊥ : EReal)) (φ : NNReal → EReal) : Prop :=
  UniformlyConvexOn f (effectiveDomain f) φ

/-- The quadratic modulus attached to strong convexity with constant `β`. -/
noncomputable def strongConvexityModulus (β : ℝ) : NNReal → EReal :=
  fun r ↦ (((β / 2 : ℝ) * (r : ℝ) ^ 2 : ℝ) : EReal)

/-- Definition 10.7 (2): a proper `]-∞,+∞]`-valued function is strongly convex with constant `β`
when its effective domain is nonempty, `β > 0`, and the quadratic Jensen inequality holds on the
effective domain. -/
def StronglyConvex (f : H → Set.Ioi (⊥ : EReal)) (β : ℝ) : Prop :=
  (effectiveDomain f).Nonempty ∧
    0 < β ∧
      ∀ ⦃x : H⦄, x ∈ effectiveDomain f → ∀ ⦃y : H⦄, y ∈ effectiveDomain f →
        ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
          ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
            jensenGap f α x y

/-- Helper for Definition 10.7: a monotone modulus that vanishes only at `0` is nonnegative. -/
private theorem uniformModulus_nonneg
    {φ : NNReal → EReal} (hφ_mono : Monotone φ) (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (r : NNReal) :
    0 ≤ φ r := by
  -- Normalize the left endpoint to `φ 0` and use monotonicity on `NNReal`.
  rw [← (hφ_zero 0).2 rfl]
  exact hφ_mono bot_le

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- Helper for Definition 10.7: the weighted Jensen sum is finite at effective-domain points. -/
private theorem weightedJensenSum_neTop
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
  -- The endpoint values are finite on the effective domain.
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have h1α0 : 0 < 1 - α := by
    linarith
  have h1α_nonneg : 0 ≤ (1 - α : EReal) := by
    exact_mod_cast h1α0.le
  have hα_mul_ne_top : (α : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hfx_top⟩
  have h1α_mul_ne_top : (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfy_top⟩
  exact EReal.add_ne_top hα_mul_ne_top h1α_mul_ne_top

omit [NormedSpace ℝ H] in
/-- Helper for Definition 10.7: the uniform modulus term is nonnegative once the quadratic weight
is nonnegative. -/
private theorem uniformModulusTerm_nonneg
    {H : Type u} [NormedAddCommGroup H]
    {φ : NNReal → EReal} (hφ_mono : Monotone φ) (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    {α : ℝ} (hα_nonneg : 0 ≤ α * (1 - α)) (x y : H) :
    (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := by
  -- Combine the nonnegative scalar weight with the nonnegative modulus value.
  exact mul_nonneg (by exact_mod_cast hα_nonneg) (uniformModulus_nonneg hφ_mono hφ_zero _)

-- Semantic recall: `lean_leansearch` pointed to
-- `Mathlib.Analysis.Convex.Strong.UniformConvexOn` and `StrongConvexOn`; local precedent already
-- uses the source-facing owners `ERealFunction.StrictlyConvex` and
-- `ERealFunction.StrictlyConvexOn`, so the bridges below keep that API rather than repackaging
-- Definition 10.7 through a new wrapper.

-- Proof sketch: unfold `UniformlyConvexOn` and extract the first conjunct.
/-- A uniformly convex-on set is nonempty. -/
theorem UniformlyConvexOn.nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    C.Nonempty :=
  by
  -- Extract the nonemptiness component stored in the definition.
  exact hf.1

-- Proof sketch: unfold `UniformlyConvexOn` and extract the domain-inclusion conjunct.
/-- A uniformly convex-on set is contained in the effective domain. -/
theorem UniformlyConvexOn.subset_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    C ⊆ effectiveDomain f :=
  by
  -- Extract the domain-inclusion component stored in the definition.
  exact hf.2.1

-- Proof sketch: unfold `UniformlyConvexOn` and extract the monotonicity conjunct.
/-- A uniformly convex-on modulus is monotone. -/
theorem UniformlyConvexOn.monotone
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    Monotone φ :=
  by
  -- Extract the monotonicity component stored in the definition.
  exact hf.2.2.1

-- Proof sketch: unfold `UniformlyConvexOn` and extract the vanishing-at-zero conjunct.
/-- A uniformly convex-on modulus vanishes exactly at `0`. -/
theorem UniformlyConvexOn.modulus_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  by
  -- Extract the vanishing-at-zero characterization stored in the definition.
  exact hf.2.2.2.1 r

/-- A function uniformly convex on `C` satisfies the defining Jensen-gap lower bound at every two
points of `C`. -/
theorem UniformlyConvexOn.gap_le
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y :=
  by
  -- Apply the Jensen-gap clause stored in the definition.
  exact hf.2.2.2.2 hx hy hα0 hα1

-- Proof sketch: unfold `UniformlyConvexOn` and apply the final conjunct.
/-- A function uniformly convex on `C` satisfies the defining inequality at every two points of
`C`. -/
theorem UniformlyConvexOn.ineq
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Rewrite the stored gap inequality into the additive Jensen form.
  have hx_dom : x ∈ effectiveDomain f := hf.subset_effectiveDomain hx
  have hy_dom : y ∈ effectiveDomain f := hf.subset_effectiveDomain hy
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
    ne_of_gt (f _).2
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ :=
    weightedJensenSum_neTop hx_dom hy_dom hα0 hα1
  simpa [add_comm] using
    (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1
      (hf.gap_le hx hy hα0 hα1)

/-- A uniformly convex-on function is convex on the same set. -/
theorem UniformlyConvexOn.convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    ConvexOn f C := by
  refine ⟨hf.nonempty, hf.subset_effectiveDomain, ?_⟩
  intro x hx y hy α hα0 hα1
  -- Drop the nonnegative modulus term from the additive Jensen inequality.
  have hα_nonneg : 0 ≤ α * (1 - α) := by
    nlinarith [hα0, hα1]
  have hterm_nonneg :
      (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
    uniformModulusTerm_nonneg hf.monotone hf.modulus_eq_zero_iff hα_nonneg x y
  calc
    (f (α • x + (1 - α) • y) : EReal)
        ≤ (f (α • x + (1 - α) • y) : EReal) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
      le_add_of_nonneg_right hterm_nonneg
    _ ≤ (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) :=
      hf.ineq hx hy hα0 hα1

-- Proof sketch: `UniformlyConvex` is defined as the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
/-- A uniformly convex function is uniformly convex on its effective domain. -/
theorem UniformlyConvex.uniformlyConvexOn
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    UniformlyConvexOn f (effectiveDomain f) φ := by
  simpa [UniformlyConvex] using hf

-- Proof sketch: the subtype codomain rules out `-∞`, and `UniformlyConvex` is the
-- `effectiveDomain` specialization of `UniformlyConvexOn`.
/-- A uniformly convex `]-∞,+∞]`-valued function is proper. -/
theorem UniformlyConvex.isProper
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    IsProper f.asEReal := by
  refine ⟨?_, ?_⟩
  · -- The subtype codomain excludes `-∞` everywhere.
    intro x
    exact ne_of_gt (f x).2
  · -- Uniform convexity already includes a nonempty effective domain.
    rcases hf.uniformlyConvexOn.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [effectiveDomain, dom, Function.asEReal] using hx

-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
/-- A uniformly convex modulus is monotone. -/
theorem UniformlyConvex.monotone
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    Monotone φ := by
  -- Specialize the uniform-convex-on accessor to the effective domain.
  exact hf.uniformlyConvexOn.monotone

-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
/-- A uniformly convex modulus vanishes exactly at `0`. -/
theorem UniformlyConvex.modulus_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    (r : NNReal) :
    φ r = 0 ↔ r = 0 := by
  -- Specialize the uniform-convex-on accessor to the effective domain.
  exact hf.uniformlyConvexOn.modulus_eq_zero_iff r

/-- A uniformly convex function satisfies the defining Jensen-gap lower bound on the effective
domain. -/
theorem UniformlyConvex.gap_le
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y := by
  -- Reuse the effective-domain specialization of uniform convexity on a set.
  exact hf.uniformlyConvexOn.gap_le hx hy hα0 hα1

-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
/-- A uniformly convex function satisfies its defining inequality on the effective domain. -/
theorem UniformlyConvex.ineq
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Reuse the effective-domain specialization of uniform convexity on a set.
  exact hf.uniformlyConvexOn.ineq hx hy hα0 hα1

/-- A uniformly convex function is convex on its effective domain. -/
theorem UniformlyConvex.convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    ConvexOn f (effectiveDomain f) := by
  -- Reuse the effective-domain specialization of uniform convexity on a set.
  exact hf.uniformlyConvexOn.convexOn

/-- A uniformly convex function is strictly convex. -/
theorem UniformlyConvex.strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    StrictlyConvex f := by
  intro x hx y hy hxy α hα0 hα1
  let m : H := α • x + (1 - α) • y
  -- The penalty term is strictly positive at distinct points.
  have hαterm_pos : (0 : EReal) < ((α * (1 - α) : ℝ) : EReal) := by
    exact_mod_cast show 0 < α * (1 - α) by nlinarith
  have hdist_pos : (0 : NNReal) < ‖x - y‖₊ := by
    exact_mod_cast norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ :=
    uniformModulus_nonneg hf.monotone hf.modulus_eq_zero_iff _
  have hφ_ne_zero : φ ‖x - y‖₊ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hdist_pos) ((hf.modulus_eq_zero_iff ‖x - y‖₊).1 hzero)
  have hφ_pos : (0 : EReal) < φ ‖x - y‖₊ :=
    lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
  have hterm_pos :
      (0 : EReal) < ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
    EReal.mul_pos hαterm_pos hφ_pos
  have hconv : Convex ℝ (effectiveDomain f) := hf.convexOn.convex_effectiveDomain
  have hm : m ∈ effectiveDomain f := by
    exact hconv hx hy hα0.le (sub_nonneg.mpr hα1.le) (by ring)
  have hm_ne_bot : (f m : EReal) ≠ ⊥ := ne_of_gt (f m).2
  have hm_ne_top : (f m : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hm)
  have hlt :
      (f m : EReal) < (f m : EReal) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := by
    simpa [m, add_comm] using
      EReal.add_lt_add_of_lt_of_le hterm_pos le_rfl hm_ne_bot hm_ne_top
  exact lt_of_lt_of_le hlt (hf.ineq hx hy hα0 hα1)

/-- A positive strong-convexity constant induces a monotone quadratic modulus. -/
theorem strongConvexityModulus_monotone {β : ℝ} (hβ : 0 < β) :
    Monotone (strongConvexityModulus β) := by
  intro r s hrs
  -- The quadratic modulus is increasing on `NNReal` because the coefficient is positive.
  have hβ_nonneg : 0 ≤ β / 2 := by
    positivity
  have hrsq : (r : ℝ) ^ (2 : ℕ) ≤ (s : ℝ) ^ (2 : ℕ) := by
    nlinarith [show (r : ℝ) ≤ s from hrs, r.2, s.2]
  have hmul :
      (β / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) ≤ (β / 2 : ℝ) * (s : ℝ) ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hrsq hβ_nonneg
  have hmulE :
      (((β / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) : ℝ) : EReal) ≤
        (((β / 2 : ℝ) * (s : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
    exact_mod_cast hmul
  simpa [strongConvexityModulus] using hmulE

/-- A positive strong-convexity constant induces a quadratic modulus vanishing exactly at `0`. -/
theorem strongConvexityModulus_eq_zero_iff {β : ℝ} (hβ : 0 < β) (r : NNReal) :
    strongConvexityModulus β r = 0 ↔ r = 0 := by
  constructor
  · intro hzero
    -- Cast the quadratic equality down to `ℝ` and use positivity of `β`.
    have hzeroE :
        (((β / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) : ℝ) : EReal) = 0 := by
      simpa [strongConvexityModulus] using hzero
    have hreal : (β / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) = 0 := by
      exact_mod_cast hzeroE
    have hβhalf_ne : (β / 2 : ℝ) ≠ 0 := by
      linarith
    have hr_sq : (r : ℝ) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hreal).resolve_left hβhalf_ne
    have hr_real : (r : ℝ) = 0 := by
      nlinarith
    apply NNReal.eq
    exact hr_real
  · intro hr
    -- The modulus vanishes at the zero radius.
    subst hr
    simp [strongConvexityModulus]

/-- A strongly convex function has nonempty effective domain. -/
theorem StronglyConvex.nonempty {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    (effectiveDomain f).Nonempty := by
  -- Extract the nonemptiness component stored in the definition.
  exact hf.1

-- Proof sketch: unfold `StronglyConvex` and extract the positivity conjunct.
/-- A strongly convex function has positive convexity constant. -/
theorem StronglyConvex.pos {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    0 < β := by
  -- Extract the positivity component stored in the definition.
  exact hf.2.1

/-- A strongly convex function is proper. -/
theorem StronglyConvex.isProper {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    IsProper f.asEReal := by
  refine ⟨?_, ?_⟩
  · -- The subtype codomain excludes `-∞` everywhere.
    intro x
    exact ne_of_gt (f x).2
  · -- Strong convexity already includes a nonempty effective domain.
    rcases hf.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [effectiveDomain, dom, Function.asEReal] using hx

/-- A strongly convex function satisfies the quadratic Jensen-gap lower bound on its effective
domain. -/
theorem StronglyConvex.gap_le {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) {x y : H} (hx : x ∈ effectiveDomain f)
    (hy : y ∈ effectiveDomain f) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤ jensenGap f α x y :=
  by
  -- Apply the quadratic Jensen-gap clause stored in the definition.
  exact hf.2.2 hx hy hα0 hα1

/-- A uniformly convex function with the quadratic modulus coming from a positive constant is
strongly convex with that constant. -/
theorem UniformlyConvex.stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hβ : 0 < β)
    (hf : UniformlyConvex f (strongConvexityModulus β)) :
    StronglyConvex f β := by
  refine ⟨hf.uniformlyConvexOn.nonempty, hβ, ?_⟩
  intro x hx y hy α hα0 hα1
  -- The quadratic modulus case is exactly the strong-convexity inequality.
  exact hf.gap_le hx hy hα0 hα1

/-- A strongly convex function satisfies the quadratic Jensen inequality on its effective
domain. -/
theorem StronglyConvex.ineq {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) {x y : H} (hx : x ∈ effectiveDomain f)
    (hy : y ∈ effectiveDomain f) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Rewrite the stored gap inequality into the additive Jensen form.
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
    ne_of_gt (f _).2
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ :=
    weightedJensenSum_neTop hx hy hα0 hα1
  simpa [add_comm] using
    (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1
      (hf.gap_le hx hy hα0 hα1)

-- Proof sketch: the quadratic modulus is monotone and vanishes only at `0` when `β > 0`, so the
-- defining strong-convexity inequality is exactly the corresponding uniform-convexity inequality.
/-- A strongly convex function is uniformly convex with the associated quadratic modulus. -/
theorem StronglyConvex.uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hf : StronglyConvex f β) :
    UniformlyConvex f (strongConvexityModulus β) := by
  refine ⟨hf.nonempty, ?_, strongConvexityModulus_monotone hf.pos,
    strongConvexityModulus_eq_zero_iff hf.pos, ?_⟩
  · -- The ambient set is already the effective domain.
    intro x hx
    exact hx
  · intro x hx y hy α hα0 hα1
    -- Reuse the quadratic Jensen-gap inequality from strong convexity.
    exact hf.gap_le hx hy hα0 hα1

/-- A canonical mathlib uniformly convexity statement on a nonempty set for an everywhere-finite
real-valued function yields the source-facing `EReal` uniformly convexity statement on the same
set with the same modulus. -/
theorem UniformConvexOn.toUniformlyConvexOn
    {g : H → ℝ} {C : Set H} {φ : ℝ → ℝ} (hC_nonempty : C.Nonempty) (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0) (hf : UniformConvexOn C φ g) :
    UniformlyConvexOn g.toEReal C (fun r : NNReal ↦ ((φ r : ℝ) : EReal)) := by
  refine ⟨hC_nonempty, ?_, ?_, ?_, ?_⟩
  · -- A real-valued function is finite everywhere.
    intro x hx
    simp [Function.effectiveDomain_toEReal]
  · intro r s hrs
    -- Restrict the real monotonicity hypothesis to nonnegative radii.
    change (((φ r : ℝ) : EReal) ≤ ((φ s : ℝ) : EReal))
    exact_mod_cast hφ_mono (show (r : ℝ) ≤ s from hrs)
  · intro r
    constructor
    · intro hzero
      have hzeroE : (((φ (r : ℝ) : ℝ) : EReal) = 0) := by
        simpa using hzero
      have hreal : φ (r : ℝ) = 0 := (EReal.coe_eq_zero).1 hzeroE
      exact (hφ_zero r).1 hreal
    · intro hr
      have hreal : φ (r : ℝ) = 0 := (hφ_zero r).2 hr
      have hzeroE : (((φ (r : ℝ) : ℝ) : EReal) = 0) := (EReal.coe_eq_zero).2 hreal
      simpa using hzeroE
  · intro x hx y hy α hα0 hα1
    have hα_nonneg : 0 ≤ α := hα0.le
    have h1α_nonneg : 0 ≤ 1 - α := by
      linarith
    have hα_sum : α + (1 - α) = 1 := by
      ring
    have hbase :
        g (α • x + (1 - α) • y) ≤
          α * g x + (1 - α) * g y - α * (1 - α) * φ ‖x - y‖ := by
      simpa using hf.2 hx hy hα_nonneg h1α_nonneg hα_sum
    have hineq :
        g (α • x + (1 - α) • y) + α * (1 - α) * φ ‖x - y‖ ≤
          α * g x + (1 - α) * g y := by
      linarith
    have hineqE :
        (((g (α • x + (1 - α) • y) + α * (1 - α) * φ ‖x - y‖ : ℝ) : EReal)) ≤
          (((α * g x + (1 - α) * g y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    have hx_dom : x ∈ effectiveDomain g.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hy_dom : y ∈ effectiveDomain g.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hcombo_ne_bot : (g.toEReal (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
      ne_of_gt (g.toEReal _).2
    have hsum_ne_top :
        (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
      weightedJensenSum_neTop hx_dom hy_dom hα0 hα1
    have hgap :
        ((α * (1 - α) : ℝ) : EReal) * ((φ ‖x - y‖₊ : ℝ) : EReal) ≤
          (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) -
            (g.toEReal (α • x + (1 - α) • y) : EReal) := by
      rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
      simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_left_comm, add_comm] using hineqE
    simpa [jensenGap] using hgap

/-- A canonical mathlib uniform-convexity statement on `Set.univ` for an everywhere-finite
real-valued function yields the source-facing `EReal` uniformly convexity statement with the same
modulus. -/
theorem UniformConvexOn.toUniformlyConvex
    {g : H → ℝ} {φ : ℝ → ℝ} (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hf : UniformConvexOn (Set.univ : Set H) φ g) :
    UniformlyConvex g.toEReal (fun r : NNReal ↦ ((φ r : ℝ) : EReal)) := by
  -- Specialize the bridge theorem to `Set.univ`.
  simpa [UniformlyConvex, Function.effectiveDomain_toEReal] using
    (UniformConvexOn.toUniformlyConvexOn
      (C := Set.univ) ⟨0, by simp⟩ hφ_mono hφ_zero hf)

/-- A canonical mathlib strongly-convexity statement on `Set.univ` for an everywhere-finite
real-valued function yields the source-facing `EReal` strong convexity statement with the same
constant. -/
theorem StrongConvexOn.toStronglyConvex
    {g : H → ℝ} {β : ℝ} (hβ : 0 < β) (hf : StrongConvexOn (Set.univ : Set H) β g) :
    StronglyConvex g.toEReal β := by
  refine ⟨by simp [Function.effectiveDomain_toEReal], hβ, ?_⟩
  intro x hx y hy α hα0 hα1
  -- Rewrite the real strong-convexity inequality into the source Jensen-gap form.
  have hα_nonneg : 0 ≤ α := hα0.le
  have h1α_nonneg : 0 ≤ 1 - α := by
    linarith
  have hα_sum : α + (1 - α) = 1 := by
    ring
  have hbase :
      g (α • x + (1 - α) • y) ≤
        α * g x + (1 - α) * g y - α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
    simpa [StrongConvexOn] using hf.2 (by simp) (by simp) hα_nonneg h1α_nonneg hα_sum
  have hineq :
      g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) ≤
        α * g x + (1 - α) * g y := by
    linarith
  have hineqE :
      (((g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) : ℝ) :
        EReal)) ≤ (((α * g x + (1 - α) * g y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  have hx_dom : x ∈ effectiveDomain g.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hy_dom : y ∈ effectiveDomain g.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hcombo_ne_bot : (g.toEReal (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
    ne_of_gt (g.toEReal _).2
  have hsum_ne_top :
      (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
    weightedJensenSum_neTop hx_dom hy_dom hα0 hα1
  have hgap :
      ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
        (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) -
          (g.toEReal (α • x + (1 - α) • y) : EReal) := by
    rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
    simpa [strongConvexityModulus, Function.toEReal_apply, EReal.coe_add, EReal.coe_mul,
      mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hineqE
  simpa [jensenGap] using hgap

/-- An everywhere-finite source-facing uniformly convex function yields the canonical mathlib
uniformly convexity statement on `Set.univ`. -/
theorem UniformlyConvex.toUniformConvexOn
    {g : H → ℝ} {φ : ℝ → ℝ}
    (hf : UniformlyConvex g.toEReal (fun r : NNReal ↦ ((φ r : ℝ) : EReal))) :
    UniformConvexOn (Set.univ : Set H) φ g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · -- The endpoint case reduces to the right endpoint value.
    have hb1 : b = 1 := by
      linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · -- The endpoint case reduces to the left endpoint value.
    have ha1 : a = 1 := by
      linarith
    simp [hb0, ha1]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha_lt_one : a < 1 := by
    nlinarith [hb_pos, hab]
  have hb_eq : b = 1 - a := by
    linarith
  have hineqE :
      (((g (a • x + b • y) + a * b * φ ‖x - y‖ : ℝ) : EReal)) ≤
        (((a * g x + b * g y : ℝ) : EReal)) := by
    simpa [Function.toEReal_apply, hb_eq, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm] using
      hf.uniformlyConvexOn.ineq (by simp) (by simp) ha_pos ha_lt_one
  have hineq :
      g (a • x + b • y) + a * b * φ ‖x - y‖ ≤ a * g x + b * g y := by
    exact_mod_cast hineqE
  rw [le_sub_iff_add_le]
  simpa [mul_assoc] using hineq

/-- Under an explicit convexity hypothesis on `C`, the source-facing `EReal` notion induces the
canonical mathlib uniformly convexity statement for the finite real-valued model. -/
theorem UniformlyConvexOn.toUniformConvexOn
    {g : H → ℝ} {C : Set H} {φ : ℝ → ℝ} (hC : Convex ℝ C)
    (hf : UniformlyConvexOn g.toEReal C (fun r : NNReal ↦ ((φ r : ℝ) : EReal))) :
    UniformConvexOn C φ g := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · -- The endpoint case reduces to the right endpoint value.
    have hb1 : b = 1 := by
      linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · -- The endpoint case reduces to the left endpoint value.
    have ha1 : a = 1 := by
      linarith
    simp [hb0, ha1]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha_lt_one : a < 1 := by
    nlinarith [hb_pos, hab]
  have hb_eq : b = 1 - a := by
    linarith
  have hineqE :
      (((g (a • x + b • y) + a * b * φ ‖x - y‖ : ℝ) : EReal)) ≤
        (((a * g x + b * g y : ℝ) : EReal)) := by
    simpa [Function.toEReal_apply, hb_eq, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm] using hf.ineq hx hy ha_pos ha_lt_one
  have hineq :
      g (a • x + b • y) + a * b * φ ‖x - y‖ ≤ a * g x + b * g y := by
    exact_mod_cast hineqE
  rw [le_sub_iff_add_le]
  simpa [mul_assoc] using hineq

/-- A source-facing strongly convex `EReal` function on an everywhere-finite real model yields the
canonical mathlib `StrongConvexOn` statement on `Set.univ`. -/
theorem StronglyConvex.toStrongConvexOn
    {g : H → ℝ} {β : ℝ} (hf : StronglyConvex g.toEReal β) :
    StrongConvexOn (Set.univ : Set H) β g := by
  -- Convert the quadratic-modulus uniform convexity bridge back to mathlib's owner.
  simpa [StrongConvexOn, strongConvexityModulus] using
    (hf.uniformlyConvex.toUniformConvexOn
      (g := g) (φ := fun r : ℝ ↦ β / 2 * r ^ (2 : ℕ)))

end ERealFunction
