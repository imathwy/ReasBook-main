import BauschkeLean.Chap08.Proposition_8_35
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Proposition_6_19
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Example_9_41
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Example_13_2
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Proposition_16_69

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Real
open scoped InnerProductSpace Pointwise
open WithLp

universe u

namespace ERealFunction

section SubdifferentialOfScalarComposition

open SetValuedOperator

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [CompleteSpace H] in
/-- Helper: coercing a continuous convex real-valued function through
`toEReal` preserves convexity on its effective domain. -/
lemma convexOn_toEReal_of_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Function.effectiveDomain_toEReal]
  · simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * f x + (1 - a) * f y : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper: the subdifferential of a constant `]-∞,+∞]`-valued function is
the singleton `{0}` at every base point. -/
lemma subdifferential_const_eq_singleton_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : Set.Ioi (⊥ : EReal)) (hc : (c : EReal) < ⊤) (x : E) :
    (∂ fun _ : E ↦ c) x = ({0} : Set E) := by
  ext u
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    -- Testing the supporting inequality at `x + u` forces the norm square of `u` to vanish.
    have htest : (⟪(x + u) - x, u⟫_ℝ : EReal) + (c : EReal) ≤ (c : EReal) := by
      simpa using hu (x + u)
    have hc_top : (c : EReal) ≠ ⊤ := ne_of_lt hc
    have hc_bot : (c : EReal) ≠ ⊥ := ne_of_gt c.2
    have htest' :
        (((‖u‖ ^ 2 + (c : EReal).toReal : ℝ) : EReal)) ≤ (c : EReal) := by
      rw [EReal.coe_add, EReal.coe_toReal hc_top hc_bot]
      simpa [real_inner_self_eq_norm_sq] using htest
    have hsq : (‖u‖ ^ 2 : ℝ) ≤ 0 := by
      have hrealE :
          (((‖u‖ ^ 2 + (c : EReal).toReal : ℝ) : EReal)) ≤
            (((c : EReal).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hc_top hc_bot] using htest'
      have hreal : ‖u‖ ^ 2 + (c : EReal).toReal ≤ (c : EReal).toReal := by
        exact_mod_cast hrealE
      linarith
    have hnorm : ‖u‖ = 0 := by
      nlinarith [sq_nonneg ‖u‖, hsq]
    exact Set.mem_singleton_iff.mpr (norm_eq_zero.mp hnorm)
  · intro hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    -- The zero vector satisfies the constant support inequality trivially.
    intro z
    simp

omit [CompleteSpace H] in
/-- Helper: when `f` is constant with value `f xbar`, the composition
`φ ∘ f` has subdifferential `{0}` at `xbar`. -/
lemma subdifferential_comp_constant_eq_singleton_zero
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (xbar : H) (hxbar : f xbar ∈ effectiveDomain φ) (hconst : ∀ z : H, f z = f xbar) :
    (∂ (φ ∘ f)) xbar = ({0} : Set H) := by
  have hconst_fun : (φ ∘ f) = fun _ : H ↦ φ (f xbar) := by
    funext z
    -- The constant-value hypothesis rewrites the composition to a literal constant function.
    simp [Function.comp, hconst z]
  have hfinite : (φ (f xbar) : EReal) < ⊤ := by
    simpa [mem_effectiveDomain_iff] using hxbar
  -- Reduce to the constant-function subdifferential computed above.
  rw [hconst_fun]
  exact subdifferential_const_eq_singleton_zero (φ (f xbar)) hfinite xbar

omit [CompleteSpace H] in
/-- Helper: when `f` is constant with value `f xbar`, the coercion
`f.toEReal` has subdifferential `{0}` at `xbar`. -/
lemma subdifferential_toEReal_constant_eq_singleton_zero
    (f : H → ℝ) (xbar : H) (hconst : ∀ z : H, f z = f xbar) :
    (∂ f.toEReal) xbar = ({0} : Set H) := by
  have hconst_fun :
      f.toEReal = (fun _ : H ↦ (f xbar : ℝ)).toEReal := by
    funext z
    -- The real-valued coercion preserves the constant-value reduction.
    apply Subtype.ext
    simp [Function.toEReal_apply, hconst z]
  have hfinite :
      ((((fun _ : H ↦ (f xbar : ℝ)).toEReal xbar : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) := by
    simp [Function.toEReal_apply]
  -- Apply the constant-function computation to the `toEReal` coercion.
  simpa [hconst_fun] using
    subdifferential_const_eq_singleton_zero
      ((fun _ : H ↦ (f xbar : ℝ)).toEReal xbar) hfinite xbar

omit [CompleteSpace H] in
/-- Helper: if the scalar subdifferential at `f xbar` is nonempty and `f` is
constant, then the union of scaled subdifferentials on the right-hand side collapses to `{0}`. -/
lemma iUnion_smul_subdifferential_toEReal_constant_eq_singleton_zero_of_nonempty
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (xbar : H) (hconst : ∀ z : H, f z = f xbar)
    (hsub_nonempty : ((∂ φ) (f xbar)).Nonempty) :
    (⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar)) = ({0} : Set H) := by
  have hzero_sub :
      (∂ f.toEReal) xbar = ({0} : Set H) :=
    subdifferential_toEReal_constant_eq_singleton_zero f xbar hconst
  obtain ⟨α, hα⟩ := hsub_nonempty
  ext u
  constructor
  · intro hu
    rcases Set.mem_iUnion.mp hu with ⟨β, huβ⟩
    rcases Set.mem_iUnion.mp huβ with ⟨hβmem, hβ⟩
    have hβzero : u ∈ β • ({0} : Set H) := by
      simpa [hzero_sub] using hβ
    clear huβ hβ
    rename_i hβ
    rcases Set.mem_smul_set.mp hβzero with ⟨v, hv, rfl⟩
    have hv0 : v = 0 := by
      simpa using hv
    simp [hv0]
  · intro hu
    have hu0 : u = 0 := by
      simpa using hu
    subst hu0
    -- Any scalar subgradient indexes the same singleton zero slice.
    refine Set.mem_iUnion.mpr ⟨α, Set.mem_iUnion.mpr ?_⟩
    refine ⟨hα, ?_⟩
    have hzero_mem : (0 : H) ∈ α • ({0} : Set H) := by
      exact Set.mem_smul_set.mpr ⟨0, by simp, by simp⟩
    rw [hzero_sub]
    exact hzero_mem

omit [CompleteSpace H] in
/-- Helper: if the scalar subdifferential at `f xbar` is empty and `f` is
constant, then the union of scaled subdifferentials on the right-hand side is empty. -/
lemma iUnion_smul_subdifferential_toEReal_constant_eq_empty_of_empty
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (xbar : H)
    (hsub_empty : (∂ φ) (f xbar) = (∅ : Set ℝ)) :
    (⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar)) = (∅ : Set H) := by
  -- No scalar subgradient contributes a slice, so the indexed union is empty.
  simp [hsub_empty]

omit [CompleteSpace H] in
/-- Helper: in the constant branch, an empty scalar subdifferential forces the
displayed chain-rule equality to fail. -/
lemma subdifferential_comp_constant_ne_iUnion_smul_of_scalarSubdifferential_empty
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (xbar : H) (hxbar : f xbar ∈ effectiveDomain φ) (hconst : ∀ z : H, f z = f xbar)
    (hsub_empty : (∂ φ) (f xbar) = (∅ : Set ℝ)) :
    (∂ (φ ∘ f)) xbar ≠ ⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar) := by
  -- The left-hand side is `{0}` for a constant composition, while the right-hand side is empty.
  rw [subdifferential_comp_constant_eq_singleton_zero f φ xbar hxbar hconst]
  rw [iUnion_smul_subdifferential_toEReal_constant_eq_empty_of_empty f φ xbar hsub_empty]
  simp

omit [CompleteSpace H] in
/-- Helper: the scalar Boltzmann entropy has empty subdifferential at `0`. -/
lemma boltzmannEntropy_subdifferential_zero_eq_empty :
    (∂ boltzmannEntropy) (0 : ℝ) = (∅ : Set ℝ) := by
  ext u
  constructor
  · intro hu
    -- Testing the subgradient inequality at `exp u` produces an immediate contradiction.
    have htest :=
      (mem_subdifferential_iff (f := boltzmannEntropy) (x := (0 : ℝ)) (u := u)).1 hu
        (Real.exp u)
    have hinner : ⟪Real.exp u, u⟫_ℝ = Real.exp u * u := by
      calc
        ⟪Real.exp u, u⟫_ℝ = (starRingEnd ℝ) (Real.exp u) * u := RCLike.inner_apply' _ _
        _ = Real.exp u * u := by simp
    have hineq' :
        (⟪Real.exp u, u⟫_ℝ : EReal) ≤
          (((Real.exp u) * Real.log (Real.exp u) - Real.exp u : ℝ) : EReal) := by
      calc
        (⟪Real.exp u, u⟫_ℝ : EReal)
            = (⟪Real.exp u - 0, u⟫_ℝ : EReal) + (boltzmannEntropy 0 : EReal) := by
                simp
        _ ≤ (boltzmannEntropy (Real.exp u) : EReal) := htest
        _ = (((Real.exp u) * Real.log (Real.exp u) - Real.exp u : ℝ) : EReal) := by
              rw [boltzmannEntropy_apply_of_pos (Real.exp_pos u)]
    have hineq :
        (((Real.exp u) * u : ℝ) : EReal) ≤
          (((Real.exp u) * Real.log (Real.exp u) - Real.exp u : ℝ) : EReal) := by
      simpa [hinner] using hineq'
    have hreal : Real.exp u * u ≤ Real.exp u * Real.log (Real.exp u) - Real.exp u := by
      exact_mod_cast hineq
    rw [Real.log_exp] at hreal
    linarith [Real.exp_pos u]
  · intro hu
    simp at hu

/-- Helper for Corollary 16.72: a real singleton is its own relative interior. -/
lemma self_mem_relativeInterior_singletonReal (r : ℝ) :
    r ∈ Set.relativeInterior ({r} : Set ℝ) := by
  rw [Set.mem_relativeInterior_iff]
  have hr_mem : r ∈ ({r} : Set ℝ) := by
    simp
  refine ⟨hr_mem, ?_⟩
  have hsub : ({r} : Set ℝ) - ({r} : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_sub.mp hy with ⟨a, ha, b, hb, hab⟩
      rcases Set.mem_singleton_iff.mp ha with rfl
      rcases Set.mem_singleton_iff.mp hb with rfl
      simpa using hab.symm
    · intro hy
      have hzero : y = 0 := Set.mem_singleton_iff.mp hy
      subst hzero
      exact Set.mem_sub.mpr ⟨r, hr_mem, r, hr_mem, sub_self r⟩
  have hcone_zero : Set.cone ({0} : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ (((⊥ : Submodule ℝ ℝ).toConvexCone : ConvexCone ℝ ℝ) : Set ℝ) :=
        ConvexCone.hull_min (C := (⊥ : Submodule ℝ ℝ).toConvexCone)
          (fun z hz ↦ by simpa using hz) hy
      simpa using hy'
    · intro hy
      have hy' : y ∈ ((⊥ : Submodule ℝ ℝ) : Set ℝ) := by
        simpa using hy
      exact ConvexCone.subset_hull hy'
  have hspan_zero : (Submodule.span ℝ ({0} : Set ℝ) : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
      simp
    · intro hy
      have hzero : y = 0 := by simpa using hy
      subst hzero
      exact Submodule.zero_mem _
  -- The translated cone-span criterion collapses to the zero subspace on a singleton.
  rw [hsub, hcone_zero, hspan_zero]

/-- Helper for Corollary 16.72: the constant-zero / Boltzmann data satisfies every visible
hypothesis of the displayed theorem. -/
lemma constantZeroBoltzmannSatisfiesVisibleHypotheses :
    Continuous (fun _ : ℝ ↦ (0 : ℝ)) ∧
      _root_.ConvexOn ℝ Set.univ (fun _ : ℝ ↦ (0 : ℝ)) ∧
      boltzmannEntropy ∈ Γ₀(ℝ) ∧
      MonotoneOn boltzmannEntropy (Set.range (fun _ : ℝ ↦ (0 : ℝ))) ∧
      ((ri (Set.range (fun _ : ℝ ↦ (0 : ℝ))) + Ioi (0 : ℝ)) ∩
        ri (effectiveDomain boltzmannEntropy)).Nonempty ∧
      (0 : ℝ) ∈ effectiveDomain boltzmannEntropy := by
  refine ⟨continuous_const, ?_, boltzmannEntropy_mem_gammaZero, ?_, ?_, ?_⟩
  · -- The constant-zero map is convex on all of `ℝ`.
    simpa using
      (convexOn_const (0 : ℝ) convex_univ :
        _root_.ConvexOn ℝ (Set.univ : Set ℝ) (fun _ : ℝ ↦ (0 : ℝ)))
  · intro a ha b hb hab
    -- The range is the singleton `{0}`, so monotonicity reduces to reflexivity.
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    rfl
  · refine ⟨1, ?_, ?_⟩
    · have hzero_ri : (0 : ℝ) ∈ ri (Set.range (fun _ : ℝ ↦ (0 : ℝ))) := by
        -- The constant-zero range is the singleton `{0}`.
        simpa [Set.range_const] using self_mem_relativeInterior_singletonReal (0 : ℝ)
      -- The positive slack `1` places the witness in `ri (range f) + ℝ_{++}`.
      exact Set.mem_add.mpr ⟨0, hzero_ri, 1, by norm_num, by norm_num⟩
    · have h1_int : (1 : ℝ) ∈ interior (Set.Ici (0 : ℝ)) := by
        rw [interior_Ici]
        norm_num
      -- On `ℝ`, the effective domain `[0,+∞)` has relative interior `(0,+∞)`.
      rw [effectiveDomain_boltzmannEntropy]
      rw [← interior_eq_relativeInterior_of_convex_nonempty_interior
        (convex_Ici (0 : ℝ)) ⟨1, h1_int⟩]
      exact h1_int
  · -- The Boltzmann entropy is finite at `0`.
    simpa [effectiveDomain_boltzmannEntropy]

/-- Helper for Corollary 16.72: the constant-zero composition with `boltzmannEntropy` already
violates the displayed chain-rule equality at `0`. -/
lemma constantZeroCounterexampleViolatesChainRule :
    (∂ (boltzmannEntropy ∘ fun _ : ℝ ↦ (0 : ℝ))) (0 : ℝ) ≠
      ⋃ α ∈ (∂ boltzmannEntropy) (0 : ℝ),
        α • ((∂ (fun _ : ℝ ↦ (0 : ℝ)).toEReal) (0 : ℝ)) := by
  -- The generic constant-branch obstruction applies once the scalar subdifferential is empty.
  refine subdifferential_comp_constant_ne_iUnion_smul_of_scalarSubdifferential_empty
    (f := fun _ : ℝ ↦ (0 : ℝ)) (φ := boltzmannEntropy) (xbar := (0 : ℝ)) ?_ ?_ ?_
  · -- The constant value `0` lies in the effective domain of `boltzmannEntropy`.
    simp [effectiveDomain_boltzmannEntropy]
  · intro z
    rfl
  · exact boltzmannEntropy_subdifferential_zero_eq_empty

omit [CompleteSpace H] in
/-- Helper for Corollary 16.72: `-1` is a subgradient of the nonnegative-halfline indicator at
`0`. -/
lemma negOne_mem_subdifferential_indicator_Ici_zero :
    (-1 : ℝ) ∈ (∂ ι[Set.Ici (0 : ℝ)]) (0 : ℝ) := by
  rw [mem_subdifferential_iff]
  intro t
  have hinner_one : ⟪t, (1 : ℝ)⟫_ℝ = t := by
    calc
      ⟪t, (1 : ℝ)⟫_ℝ = (starRingEnd ℝ) t * (1 : ℝ) := RCLike.inner_apply' _ _
      _ = t := by simp
  have hinner_neg : ⟪t - 0, (-1 : ℝ)⟫_ℝ = -⟪t, (1 : ℝ)⟫_ℝ := by
    calc
      ⟪t - 0, (-1 : ℝ)⟫_ℝ = -t := by
        calc
          ⟪t - 0, (-1 : ℝ)⟫_ℝ = (starRingEnd ℝ) (t - 0) * (-1 : ℝ) := RCLike.inner_apply' _ _
          _ = -t := by simp
      _ = -⟪t, (1 : ℝ)⟫_ℝ := by rw [hinner_one]
  by_cases ht : 0 ≤ t
  · have hnonneg : 0 ≤ ⟪t, (1 : ℝ)⟫_ℝ := by
      simpa [hinner_one] using ht
    have h0 : (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal) = 0 := by
      simp [ERealFunction.indicator]
    have ht0 : (ι[Set.Ici (0 : ℝ)] t : EReal) = 0 := by
      simp [ERealFunction.indicator, ht]
    show (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) + (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal) ≤
      (ι[Set.Ici (0 : ℝ)] t : EReal)
    calc
      (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) + (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal)
          = -(((⟪t, (1 : ℝ)⟫_ℝ : ℝ) : EReal)) + 0 := by
              rw [hinner_neg, h0, EReal.coe_neg]
      _ ≤ 0 := by
        have hneg0 : -(((⟪t, (1 : ℝ)⟫_ℝ : ℝ) : EReal)) ≤ (0 : EReal) := by
          exact_mod_cast (neg_nonpos.mpr hnonneg)
        simpa using add_le_add_right hneg0 (0 : EReal)
      _ = (ι[Set.Ici (0 : ℝ)] t : EReal) := by rw [ht0]
  · have h0 : (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal) = 0 := by
      simp [ERealFunction.indicator]
    have htop : (ι[Set.Ici (0 : ℝ)] t : EReal) = ⊤ := by
      simp [ERealFunction.indicator, ht]
    show (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) + (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal) ≤
      (ι[Set.Ici (0 : ℝ)] t : EReal)
    calc
      (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) + (ι[Set.Ici (0 : ℝ)] (0 : ℝ) : EReal)
          = -(((⟪t, (1 : ℝ)⟫_ℝ : ℝ) : EReal)) + 0 := by
              rw [hinner_neg, h0, EReal.coe_neg]
      _ ≤ ⊤ := by simp
      _ = (ι[Set.Ici (0 : ℝ)] t : EReal) := by rw [htop]

omit [CompleteSpace H] in
/-- Helper for Corollary 16.72: `-1` is a subgradient of `|·|` at `0`. -/
lemma negOne_mem_subdifferential_abs_zero :
    (-1 : ℝ) ∈ (∂ (fun ξ : ℝ ↦ |ξ|).toEReal) (0 : ℝ) := by
  rw [mem_subdifferential_iff]
  intro t
  have hinner_one : ⟪t, (1 : ℝ)⟫_ℝ = t := by
    calc
      ⟪t, (1 : ℝ)⟫_ℝ = (starRingEnd ℝ) t * (1 : ℝ) := RCLike.inner_apply' _ _
      _ = t := by simp
  have hinner_neg : ⟪t - 0, (-1 : ℝ)⟫_ℝ = -⟪t, (1 : ℝ)⟫_ℝ := by
    calc
      ⟪t - 0, (-1 : ℝ)⟫_ℝ = -t := by
        calc
          ⟪t - 0, (-1 : ℝ)⟫_ℝ = (starRingEnd ℝ) (t - 0) * (-1 : ℝ) := RCLike.inner_apply' _ _
          _ = -t := by simp
      _ = -⟪t, (1 : ℝ)⟫_ℝ := by rw [hinner_one]
  have hreal : -⟪t, (1 : ℝ)⟫_ℝ ≤ |t| := by
    simpa [hinner_one] using neg_le_abs t
  show (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) +
      (((fun ξ : ℝ ↦ |ξ|).toEReal 0 : Set.Ioi (⊥ : EReal)) : EReal) ≤
    (((fun ξ : ℝ ↦ |ξ|).toEReal t : Set.Ioi (⊥ : EReal)) : EReal)
  calc
    (⟪t - 0, (-1 : ℝ)⟫_ℝ : EReal) +
        (((fun ξ : ℝ ↦ |ξ|).toEReal 0 : Set.Ioi (⊥ : EReal)) : EReal)
        = -(((⟪t, (1 : ℝ)⟫_ℝ : ℝ) : EReal)) + 0 := by
            rw [hinner_neg]
            simp [Function.toEReal_apply]
    _ ≤ (((|t| : ℝ)) : EReal) := by
      have hrealE : -(((⟪t, (1 : ℝ)⟫_ℝ : ℝ) : EReal)) ≤ (((|t| : ℝ)) : EReal) := by
        exact_mod_cast hreal
      simpa using add_le_add_right hrealE (0 : EReal)
    _ = (((fun ξ : ℝ ↦ |ξ|).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) := by
        simp [Function.toEReal_apply]

omit [CompleteSpace H] in
/-- Helper for Corollary 16.72: even the nonempty-scalar-subdifferential variant fails for
`f = |·|` and `φ = ι_[0,∞)` at `0`. -/
lemma absIndicatorCounterexampleViolatesNonemptyChainRule :
    (∂ (ι[Set.Ici (0 : ℝ)] ∘ fun ξ : ℝ ↦ |ξ|)) (0 : ℝ) ≠
      ⋃ α ∈ (∂ ι[Set.Ici (0 : ℝ)]) (0 : ℝ),
        α • ((∂ (fun ξ : ℝ ↦ |ξ|).toEReal) (0 : ℝ)) := by
  intro hEq
  have hleft :
      (∂ (ι[Set.Ici (0 : ℝ)] ∘ fun ξ : ℝ ↦ |ξ|)) (0 : ℝ) = ({0} : Set ℝ) := by
    have hconst :
        (ι[Set.Ici (0 : ℝ)] ∘ fun ξ : ℝ ↦ |ξ|) =
          fun _ : ℝ ↦ ι[Set.Ici (0 : ℝ)] (0 : ℝ) := by
      funext ξ
      -- The indicator sees only that `|ξ|` stays in the nonnegative halfline.
      simp [Function.comp, ERealFunction.indicator, abs_nonneg]
    have hfinite :
        (((ι[Set.Ici (0 : ℝ)] (0 : ℝ) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) := by
      simp [ERealFunction.indicator]
    -- Reduce the constant composition to the singleton-zero subdifferential computation.
    rw [hconst]
    exact subdifferential_const_eq_singleton_zero
      (ι[Set.Ici (0 : ℝ)] (0 : ℝ)) hfinite (0 : ℝ)
  have hneg_abs : (-1 : ℝ) ∈ (∂ (fun ξ : ℝ ↦ |ξ|).toEReal) (0 : ℝ) := by
    exact negOne_mem_subdifferential_abs_zero
  have hone_mem_rhs :
      (1 : ℝ) ∈ ⋃ α ∈ (∂ ι[Set.Ici (0 : ℝ)]) (0 : ℝ),
        α • ((∂ (fun ξ : ℝ ↦ |ξ|).toEReal) (0 : ℝ)) := by
    refine Set.mem_iUnion.mpr ⟨(-1 : ℝ), Set.mem_iUnion.mpr ?_⟩
    refine ⟨negOne_mem_subdifferential_indicator_Ici_zero, ?_⟩
    refine Set.mem_smul_set.mpr ⟨(-1 : ℝ), hneg_abs, ?_⟩
    norm_num
  have hone_mem_left :
      (1 : ℝ) ∈ (∂ (ι[Set.Ici (0 : ℝ)] ∘ fun ξ : ℝ ↦ |ξ|)) (0 : ℝ) := by
    rw [hEq]
    exact hone_mem_rhs
  rw [hleft] at hone_mem_left
  simp at hone_mem_left

omit [CompleteSpace H] in
/-- Helper: if `f z` is strictly larger than `f x`, then convexity forces the
values of `f` along the ray `x + T • (z - x)` to dominate the affine extrapolation from the chord
`[x, z]`. -/
lemma extrapolated_value_lower_bound
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) {x z : H}
    {T : ℝ} (hT : 1 ≤ T) :
    f x + T * (f z - f x) ≤ f (x + T • (z - x)) := by
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hα_nonneg : 0 ≤ 1 - (1 / T : ℝ) := by
    have hdiv_le_one : (1 / T : ℝ) ≤ 1 := by
      field_simp [hT_ne]
      linarith
    linarith
  have hβ_nonneg : 0 ≤ (1 / T : ℝ) := one_div_nonneg.mpr hT_pos.le
  have hsum : (1 - (1 / T : ℝ)) + (1 / T : ℝ) = 1 := by
    ring
  have hz_combo :
      (1 - (1 / T : ℝ)) • x + ((1 / T : ℝ) • x + (1 / T : ℝ) • (T • (z - x))) = z := by
    calc
      (1 - (1 / T : ℝ)) • x + ((1 / T : ℝ) • x + (1 / T : ℝ) • (T • (z - x)))
          = ((1 - (1 / T : ℝ)) + (1 / T : ℝ)) • x + (1 / T : ℝ) • (T • (z - x)) := by
            rw [← add_assoc, ← add_smul]
      _ = x + ((1 / T : ℝ) * T) • (z - x) := by
            rw [hsum, one_smul, smul_smul]
      _ = x + (z - x) := by
            simp [hT_ne]
      _ = z := by
            abel
  have hconv_step :
      f z ≤ (1 - (1 / T : ℝ)) * f x + (1 / T : ℝ) * f (x + T • (z - x)) := by
    have hconv_step_raw :
        f ((1 - (1 / T : ℝ)) • x + (1 / T : ℝ) • (x + T • (z - x))) ≤
          (1 - (1 / T : ℝ)) * f x + (1 / T : ℝ) * f (x + T • (z - x)) := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : x + T • (z - x) ∈ Set.univ)
          hα_nonneg hβ_nonneg hsum
    rw [show (1 - (1 / T : ℝ)) • x + (1 / T : ℝ) • (x + T • (z - x)) =
        (1 - (1 / T : ℝ)) • x + ((1 / T : ℝ) • x + (1 / T : ℝ) • (T • (z - x))) by
          rw [smul_add]] at hconv_step_raw
    rw [hz_combo] at hconv_step_raw
    exact hconv_step_raw
  have hmul :
      T * f z ≤ T * ((1 - (1 / T : ℝ)) * f x + (1 / T : ℝ) * f (x + T • (z - x))) := by
    exact mul_le_mul_of_nonneg_left hconv_step hT_pos.le
  have hmul' :
      T * f z ≤ (T - 1) * f x + f (x + T • (z - x)) := by
    have hrew :
        T * ((1 - (1 / T : ℝ)) * f x + (1 / T : ℝ) * f (x + T • (z - x))) =
          (T - 1) * f x + f (x + T • (z - x)) := by
      field_simp [hT_ne]
    rw [hrew] at hmul
    exact hmul
  -- Rearranging the extrapolated convexity inequality yields the desired affine lower bound.
  linarith

omit [CompleteSpace H] in
/-- Helper: a nonconstant convex function on all of `H` always attains a
strictly larger value than the one at the chosen base point. -/
lemma exists_strictly_larger_value_of_nonconstant_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) (x : H)
    (hne : ∃ z, f z ≠ f x) :
    ∃ z, f x < f z := by
  rcases hne with ⟨z, hzneq⟩
  by_cases hlt : f x < f z
  · exact ⟨z, hlt⟩
  · have hlt' : f z < f x := lt_of_le_of_ne (le_of_not_gt hlt) hzneq
    let z' := x + (x - z)
    have hlarge :
        f z + (2 : ℝ) * (f x - f z) ≤ f (z + (2 : ℝ) • (x - z)) :=
      extrapolated_value_lower_bound f hconv (by norm_num)
    -- Extrapolating the line through `z` and `x` beyond `x` forces a value strictly above `f x`.
    have hz'_eq :
        z + (2 : ℝ) • (x - z) = z' := by
      simp [z', two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
    have hz'gt : f x < f z' := by
      have hlarge' : f z + (2 : ℝ) * (f x - f z) ≤ f z' := by
        simpa [hz'_eq] using hlarge
      clear hlarge
      linarith
    exact ⟨z', hz'gt⟩

omit [CompleteSpace H] in
/-- Helper: once `f` is nonconstant, continuity and convexity imply that every
scalar above `f x` already lies in the range of `f`. -/
lemma range_mem_of_ge_of_nonconstant_continuous_convexOn_univ
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) (x : H)
    (hne : ∃ z, f z ≠ f x) {r : ℝ} (hr : f x ≤ r) :
    r ∈ Set.range f := by
  by_cases hr_eq : r = f x
  · exact ⟨x, hr_eq.symm⟩
  obtain ⟨z, hz⟩ := exists_strictly_larger_value_of_nonconstant_convexOn_univ f hconv x hne
  let T : ℝ := max 1 ((r - f x) / (f z - f x))
  have hT : 1 ≤ T := by
    simp [T]
  have hz_gap : 0 < f z - f x := sub_pos.mpr hz
  have hfrac : (r - f x) / (f z - f x) ≤ T := by
    simp [T]
  have hray :
      r ≤ f x + T * (f z - f x) := by
    have hmul : r - f x ≤ T * (f z - f x) := by
      field_simp [hz_gap.ne'] at hfrac
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hfrac
    linarith
  have hupper :
      r ≤ f (x + T • (z - x)) := by
    exact le_trans hray (extrapolated_value_lower_bound f hconv hT)
  let g : ℝ → ℝ := fun t ↦ f (x + t • (z - x))
  have hgcont : Continuous g := by
    -- Restrict `f` to the affine line through `x` and `z`.
    simpa [g] using hcont.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hr_mem :
      r ∈ Set.Icc (g 0) (g T) := by
    constructor
    · simpa [g] using hr
    · simpa [g] using hupper
  have hr_image :
      r ∈ g '' Set.Icc (0 : ℝ) T :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ T by linarith)
      hgcont.continuousOn) hr_mem
  rcases hr_image with ⟨t, -, htg⟩
  exact ⟨x + t • (z - x), by simpa [g] using htg⟩

/-- Helper: the second-coordinate pullback `p ↦ φ p.2` is finite exactly when
its scalar coordinate lies in `effectiveDomain φ`. -/
lemma effectiveDomain_second_coordinate_eq_univ_prod
    (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (fun p : H × ℝ ↦ φ p.2) = Set.univ ×ˢ effectiveDomain φ := by
  ext p
  constructor
  · intro hp
    -- Only the scalar coordinate contributes to finiteness of the pullback.
    refine ⟨by simp, ?_⟩
    simpa [mem_effectiveDomain_iff] using hp
  · intro hp
    -- Conversely, a finite scalar second coordinate makes the pullback finite.
    simpa [mem_effectiveDomain_iff] using hp.2


/-- Helper: the difference `gra F - dom g` for the epigraphical operator and
the second-coordinate pullback separates into a free first coordinate and the scalar difference
`((range f) + ℝ₊) - dom φ`. -/
lemma graph_minus_effectiveDomain_second_coordinate_eq_univ_prod_sub
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    gra (epigraphicalOperator f.toEReal) - effectiveDomain (fun p : H × ℝ ↦ φ p.2) =
      Set.univ ×ˢ (((Set.range f) + Set.Ici (0 : ℝ)) - effectiveDomain φ) := by
  ext p
  rcases p with ⟨u, v⟩
  constructor
  · intro hp
    rcases Set.mem_sub.mp hp with ⟨a, ha, b, hb, hab⟩
    rcases a with ⟨x, y⟩
    rcases b with ⟨x', y'⟩
    have hy_ge : f x ≤ y := by
      -- Unpack graph membership into the scalar epigraph inequality.
      simpa [SetValuedOperator.mem_graph, epigraphicalOperator, Function.toEReal_apply] using ha
    have hy'_dom : y' ∈ effectiveDomain φ := by
      -- Only the second coordinate controls the pullback effective domain.
      simpa [mem_effectiveDomain_iff] using hb
    have hy_mem :
        y ∈ (Set.range f) + Set.Ici (0 : ℝ) := by
      -- Write the graph height as `f x + t` with `t ≥ 0`.
      refine Set.mem_add.mpr ⟨f x, ⟨x, rfl⟩, y - f x, ?_, ?_⟩
      · simpa using sub_nonneg.mpr hy_ge
      · linarith
    have hv_eq : y - y' = v := by
      exact congrArg Prod.snd hab
    refine ⟨by simp, ?_⟩
    exact Set.mem_sub.mpr ⟨y, hy_mem, y', hy'_dom, hv_eq⟩
  · rintro ⟨_, hv⟩
    rcases Set.mem_sub.mp hv with ⟨s, hs, y', hy', hsv⟩
    rcases Set.mem_add.mp hs with ⟨a, ha, t, ht, hast⟩
    rcases ha with ⟨x, rfl⟩
    refine Set.mem_sub.mpr ?_
    refine ⟨(x, f x + t), ?_, (x - u, y'), ?_, ?_⟩
    · -- Rebuild a graph point from the range witness `f x` and the nonnegative offset `t`.
      have hgraph : f x ≤ f x + t := le_add_of_nonneg_right (by simpa using ht)
      simpa [SetValuedOperator.mem_graph, epigraphicalOperator, Function.toEReal_apply] using
        hgraph
    · -- The effective domain pullback ignores the first coordinate.
      simpa [mem_effectiveDomain_iff] using hy'
    · -- The pair difference matches the prescribed free first coordinate and scalar difference.
      ext
      · change x - (x - u) = u
        abel
      · calc
          (f x + t) - y' = s - y' := by rw [hast]
          _ = v := hsv

/-- Helper: the subdifferential of the second-coordinate pullback
`p ↦ φ p.2` is exactly `({0} : Set H) ×ˢ (∂ φ) ybar`. -/
lemma subdifferential_second_coordinate_pullback_eq_zero_prod
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (xbar : H) (ybar : ℝ) :
    (∂ (fun p : H × ℝ ↦ φ p.2)) (xbar, ybar) = ({0} : Set H) ×ˢ ((∂ φ) ybar) := by
  ext p
  rcases p with ⟨u, a⟩
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    have hybar_dom : ybar ∈ effectiveDomain φ := by
      rcases hφ.2.nonempty with ⟨t0, ht0⟩
      have htest :
          (⟪(xbar, t0) - (xbar, ybar), (u, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤
            (φ t0 : EReal) := by
        simpa using hu (xbar, t0)
      have ht0_top : (φ t0 : EReal) < ⊤ := mem_effectiveDomain_iff.mp ht0
      by_contra hybar_dom
      have hybar_top : (φ ybar : EReal) = ⊤ := by
        have hybar_not_lt : ¬ ((φ ybar : EReal) < ⊤) := by
          simpa [mem_effectiveDomain_iff] using hybar_dom
        exact top_unique <| le_of_not_gt hybar_not_lt
      have htop : (⊤ : EReal) ≤ (φ t0 : EReal) := by
        simpa [hybar_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] using htest
      exact ht0_top.not_ge htop
    have hybar_top : (φ ybar : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hybar_dom)
    have hybar_bot : (φ ybar : EReal) ≠ ⊥ := ne_of_gt (φ ybar).2
    have hu_zero : u = 0 := by
      have htest :
          (⟪(xbar + u, ybar) - (xbar, ybar), (u, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤
            (φ ybar : EReal) := by
        simpa using hu (xbar + u, ybar)
      have htest_pair :
          (⟪(u, (0 : ℝ)), (u, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤ (φ ybar : EReal) := by
        simpa using htest
      have hinner_pair : ⟪(u, (0 : ℝ)), (u, a)⟫_ℝ = ⟪u, u⟫_ℝ := by
        change ⟪u, u⟫_ℝ + ⟪(0 : ℝ), a⟫_ℝ = ⟪u, u⟫_ℝ
        simp
      have htest0 : (⟪u, u⟫_ℝ : EReal) + (φ ybar : EReal) ≤ (φ ybar : EReal) := by
        simpa [hinner_pair] using htest_pair
      have htest' :
          (((‖u‖ ^ 2 + (φ ybar : EReal).toReal : ℝ) : EReal)) ≤ (φ ybar : EReal) := by
        rw [EReal.coe_add, EReal.coe_toReal hybar_top hybar_bot]
        simpa [real_inner_self_eq_norm_sq] using htest0
      have hsq : (‖u‖ ^ 2 : ℝ) ≤ 0 := by
        have hrealE :
            (((‖u‖ ^ 2 + (φ ybar : EReal).toReal : ℝ) : EReal)) ≤
              ((((φ ybar : EReal).toReal : ℝ)) : EReal) := by
          simpa [EReal.coe_toReal hybar_top hybar_bot] using htest'
        have hreal : ‖u‖ ^ 2 + (φ ybar : EReal).toReal ≤ (φ ybar : EReal).toReal := by
          exact_mod_cast hrealE
        linarith
      have hnorm : ‖u‖ = 0 := by
        nlinarith [sq_nonneg ‖u‖, hsq]
      exact norm_eq_zero.mp hnorm
    constructor
    · exact Set.mem_singleton_iff.mpr hu_zero
    · subst u
      -- Once the first coordinate vanishes, testing only vertical variations gives the scalar
      -- subgradient inequality.
      rw [mem_subdifferential_iff]
      intro t
      have htest :
          (⟪(xbar, t) - (xbar, ybar), (0, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤
            (φ t : EReal) := by
        simpa using hu (xbar, t)
      have htest_pair :
          (⟪((0 : H), t - ybar), (0, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤ (φ t : EReal) := by
        simpa using htest
      have hinner_pair : ⟪((0 : H), t - ybar), (0, a)⟫_ℝ = ⟪t - ybar, a⟫_ℝ := by
        change ⟪(0 : H), (0 : H)⟫_ℝ + ⟪t - ybar, a⟫_ℝ = ⟪t - ybar, a⟫_ℝ
        simp
      simpa [hinner_pair] using htest_pair
  · rintro ⟨hu, ha⟩
    rcases Set.mem_singleton_iff.mp hu with rfl
    rw [mem_subdifferential_iff] at ha
    intro q
    rcases q with ⟨z, t⟩
    -- The converse direction is the scalar subgradient inequality read through the second
    -- coordinate projection.
    have htest : (⟪t - ybar, a⟫_ℝ : EReal) + (φ ybar : EReal) ≤ (φ t : EReal) := ha t
    have hinner_pair : ⟪(z - xbar, t - ybar), (0, a)⟫_ℝ = ⟪t - ybar, a⟫_ℝ := by
      change ⟪z - xbar, (0 : H)⟫_ℝ + ⟪t - ybar, a⟫_ℝ = ⟪t - ybar, a⟫_ℝ
      simp
    have htest_pair :
        (⟪(z - xbar, t - ybar), (0, a)⟫_ℝ : EReal) + (φ ybar : EReal) ≤ (φ t : EReal) := by
      simpa [hinner_pair] using htest
    simpa [hinner_pair] using htest_pair

/-- Helper: under tail monotonicity, infimizing `φ` over the epigraphical
fiber of `f` reproduces the scalar composition `φ (f x)`. -/
lemma marginal_epigraphical_operator_lower_bound_of_monotoneOn_range
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hmono : MonotoneOn φ ((Set.range f) + Set.Ici (0 : ℝ)))
    (x : H) (y : ℝ) :
    (φ (f x) : EReal) ≤
      (pointwiseAdd
          (fun p : H × ℝ ↦ φ p.2)
          (ERealFunction.indicator (gra (epigraphicalOperator f.toEReal))) (x, y) :
        EReal) := by
  let G : H × ℝ → Set.Ioi (⊥ : EReal) :=
    pointwiseAdd
      (fun p : H × ℝ ↦ φ p.2)
      (ERealFunction.indicator (gra (epigraphicalOperator f.toEReal)))
  by_cases hy : (x, y) ∈ gra (epigraphicalOperator f.toEReal)
  · have hy_ge : f x ≤ y := by
      -- On the graph branch, the epigraphical fiber condition is exactly `f x ≤ y`.
      simpa [SetValuedOperator.mem_graph, epigraphicalOperator, Function.toEReal_apply] using hy
    have hfx_tail : f x ∈ (Set.range f) + Set.Ici (0 : ℝ) := by
      exact Set.mem_add.mpr ⟨f x, ⟨x, rfl⟩, 0, by simp, by ring⟩
    have hy_tail : y ∈ (Set.range f) + Set.Ici (0 : ℝ) := by
      exact Set.mem_add.mpr ⟨f x, ⟨x, rfl⟩, y - f x, sub_nonneg.mpr hy_ge, by ring⟩
    have hmono_le : φ (f x) ≤ φ y := hmono hfx_tail hy_tail hy_ge
    have hmono_le_ereal : (φ (f x) : EReal) ≤ (φ y : EReal) := by
      exact_mod_cast hmono_le
    -- The indicator vanishes on the graph, so monotonicity gives the whole lower bound.
    calc
      (φ (f x) : EReal) ≤ (φ y : EReal) := hmono_le_ereal
      _ = (G (x, y) : EReal) := by
          simp [G, pointwiseAdd_apply, ERealFunction.indicator_apply, hy]
  · have hphi_ne_bot : (φ y : EReal) ≠ ⊥ := ne_of_gt (φ y).2
    -- Off the graph, the indicator contributes `⊤`, so the whole fiber value is `⊤`.
    calc
      (φ (f x) : EReal) ≤ ⊤ := le_top
      _ = (G (x, y) : EReal) := by
          simp [G, pointwiseAdd_apply, ERealFunction.indicator_apply, hy,
            EReal.add_top_of_ne_bot hphi_ne_bot]

/-- Helper: under tail monotonicity, infimizing `φ` over the epigraphical
fiber of `f` reproduces the scalar composition `φ (f x)`. -/
lemma marginal_epigraphical_operator_eq_scalar_composition_of_nonconstant
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hmono : MonotoneOn φ ((Set.range f) + Set.Ici (0 : ℝ)))
    (x : H) :
    marginalFunction
        (pointwiseAdd
          (fun p : H × ℝ ↦ φ p.2)
          (ERealFunction.indicator (gra (epigraphicalOperator f.toEReal)))) x =
      (φ (f x) : EReal) := by
  let G : H × ℝ → Set.Ioi (⊥ : EReal) :=
    pointwiseAdd
      (fun p : H × ℝ ↦ φ p.2)
      (ERealFunction.indicator (gra (epigraphicalOperator f.toEReal)))
  apply le_antisymm
  · -- The graph point `(x, f x)` gives the source-faithful upper bound `marginal ≤ φ (f x)`.
    calc
      marginalFunction G x ≤ (G (x, f x) : EReal) :=
        marginalFunction_le G _ _
      _ = (φ (f x) : EReal) := by
        have hx_graph : (x, f x) ∈ gra (epigraphicalOperator f.toEReal) := by
          -- The active graph point uses the canonical epigraph witness `f x ≤ f x`.
          simpa [SetValuedOperator.mem_graph, epigraphicalOperator, Function.toEReal_apply] using
            (show f x ≤ f x by simp)
        simp [G, pointwiseAdd_apply, ERealFunction.indicator_apply, hx_graph]
  · -- Every fiber value lies above `φ (f x)`, so the infimum does as well.
    rw [marginalFunction]
    refine le_sInf ?_
    rintro _ ⟨y, rfl⟩
    exact marginal_epigraphical_operator_lower_bound_of_monotoneOn_range
      f φ hmono x y

/-- Helper for Corollary 16.72: the source marginal-identity step already fails for the
constant-zero / Boltzmann pair, so monotonicity only on `range f` is insufficient. -/
lemma constantZeroBoltzmannMarginalNeScalarValue :
    marginalFunction
        (pointwiseAdd
          (fun p : ℝ × ℝ ↦ boltzmannEntropy p.2)
          (ι[gra (epigraphicalOperator (fun _ : ℝ ↦ (0 : ℝ)).toEReal)])) (0 : ℝ) ≠
      (boltzmannEntropy 0 : EReal) := by
  let G : ℝ × ℝ → Set.Ioi (⊥ : EReal) :=
    pointwiseAdd
      (fun p : ℝ × ℝ ↦ boltzmannEntropy p.2)
      (ι[gra (epigraphicalOperator (fun _ : ℝ ↦ (0 : ℝ)).toEReal)])
  have hle : marginalFunction G (0 : ℝ) ≤ (-1 : EReal) := by
    calc
      marginalFunction G (0 : ℝ) ≤ (G (0, 1) : EReal) :=
        marginalFunction_le G (0 : ℝ) (1 : ℝ)
      _ = (-1 : EReal) := by
          have hgraph :
              ((0 : ℝ), (1 : ℝ)) ∈ gra (epigraphicalOperator (fun _ : ℝ ↦ (0 : ℝ)).toEReal) := by
            -- The constant-zero epigraph contains every point of height at least `0`.
            simpa [SetValuedOperator.mem_graph, epigraphicalOperator, Function.toEReal_apply] using
              (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
          -- Evaluating at height `1` gives the strict gap `-1 < 0`.
          simp [G, pointwiseAdd_apply, ERealFunction.indicator_apply, hgraph,
            boltzmannEntropy_apply_of_pos (show (0 : ℝ) < (1 : ℝ) by norm_num)]
  intro hEq
  have hcontra : (boltzmannEntropy 0 : EReal) ≤ (-1 : EReal) := by
    -- Route correction: the marginal sits below the active fiber value `φ 1 = -1`.
    simpa [G, hEq] using hle
  have hfalse : ¬ ((0 : EReal) ≤ (-1 : EReal)) := by
    norm_num
  -- The scalar value at `0` is exactly `0`, so the displayed inequality is impossible.
  exact hfalse (by simpa using hcontra)

omit [CompleteSpace H] in
/-- Helper: the range of a continuous map into `ℝ` is convex because the
image of the convex domain `univ` is preconnected, hence an interval. -/
lemma range_convex_of_continuous_univ
    (f : H → ℝ) (hcont : Continuous f) :
    Convex ℝ (Set.range f) := by
  have hrange_preconnected : IsPreconnected (Set.range f) := by
    -- The real image of the convex set `univ` under a continuous map is preconnected.
    simpa [Set.image_univ] using
      (_root_.convex_univ : Convex ℝ (Set.univ : Set H)).isPreconnected.image f hcont.continuousOn
  exact hrange_preconnected.convex

/-- Helper: a point of `A + Ioi 0` already lies in the interior of
`A + Ici 0` because the positive scalar slack absorbs a neighborhood. -/
lemma mem_interior_add_Ici_of_mem_add_Ioi
    {A : Set ℝ} {x : ℝ} (hx : x ∈ A + Set.Ioi (0 : ℝ)) :
    x ∈ interior (A + Set.Ici (0 : ℝ)) := by
  rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
  have hb_pos : 0 < b := hb
  have hhalf_pos : 0 < b / 2 := by
    linarith
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (a + b) hhalf_pos) ?_
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hy_abs : |y - (a + b)| < b / 2 := hy
  have hy_left : -(b / 2) < y - (a + b) := (abs_lt.mp hy_abs).1
  have hy_slack : 0 ≤ b + (y - (a + b)) := by
    linarith
  -- Keep the same range point `a` and use the remaining positive slack in `Ici 0`.
  refine Set.mem_add.mpr ⟨a, ha, b + (y - (a + b)), hy_slack, ?_⟩
  ring

omit [CompleteSpace H] in
/-- Helper: the scalar difference
`((range f) + Ici 0) - effectiveDomain φ` satisfies the strong-relative-interior regularity
required by the epigraphical chain rule. -/
lemma zero_mem_sri_add_Ici_sub_effectiveDomain_of_regularity
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hcont : Continuous f) (hφ : φ ∈ Γ₀(ℝ))
    (hregular :
      ((ri (Set.range f) + Set.Ioi (0 : ℝ)) ∩ ri (effectiveDomain φ)).Nonempty) :
    (0 : ℝ) ∈ sri (((Set.range f) + Set.Ici (0 : ℝ)) - effectiveDomain φ) := by
  let C : Set ℝ := effectiveDomain φ
  let D : Set ℝ := (Set.range f) + Set.Ici (0 : ℝ)
  have hC_convex : Convex ℝ C := by
    simpa [C] using hφ.2.convex_effectiveDomain
  have hD_convex : Convex ℝ D := by
    -- The Minkowski sum stays convex once we know `range f` is an interval in `ℝ`.
    simpa [D] using (range_convex_of_continuous_univ f hcont).add (convex_Ici (0 : ℝ))
  rcases hregular with ⟨y, hyD_source, hyC_ri⟩
  have hyD_mem : y ∈ (Set.range f) + Set.Ioi (0 : ℝ) := by
    rcases Set.mem_add.mp hyD_source with ⟨a, ha, b, hb, hab⟩
    exact Set.mem_add.mpr ⟨a, (Set.mem_relativeInterior_iff.mp ha).1, b, hb, hab⟩
  have hyD_int : y ∈ interior D := by
    -- The strict positive offset in `ri (range f) + Ioi 0` upgrades directly to interior.
    exact mem_interior_add_Ici_of_mem_add_Ioi hyD_mem
  have hyD_ri : y ∈ ri D := by
    -- For this convex scalar set, nonempty interior identifies `interior` with `ri`.
    rw [← interior_eq_relativeInterior_of_convex_nonempty_interior hD_convex ⟨y, hyD_int⟩]
    exact hyD_int
  have hC_nonempty : C.Nonempty := by
    exact ⟨y, (Set.mem_relativeInterior_iff.mp hyC_ri).1⟩
  have hD_nonempty : D.Nonempty := by
    exact ⟨y, interior_subset hyD_int⟩
  have hyC_image :
      y ∈ ri ((ContinuousLinearMap.id ℝ ℝ) '' C) := by
    simpa [C] using hyC_ri
  have hreg_image :
      strongRelativeInteriorSubImageRegularity C D (ContinuousLinearMap.id ℝ ℝ) := by
    -- Use the finite-dimensional `ri D ∩ ri (L '' C)` clause of Proposition 6.19.
    dsimp [strongRelativeInteriorSubImageRegularity]
    exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨inferInstance, ⟨y, hyD_ri, hyC_image⟩⟩
  -- Proposition 6.19 now applies to the scalar difference owner directly.
  simpa [C, D] using
    zero_mem_strongRelativeInterior_sub_image_of_regularity
      hC_nonempty hD_nonempty hC_convex hD_convex (ContinuousLinearMap.id ℝ ℝ) hreg_image


/-- Corollary 16.72.

Let `f : H → ℝ` be continuous and convex, and let `φ ∈ Γ₀(ℝ)` be increasing on
`range f`.
Suppose that `(ri (range f) + ℝ_{++}) ∩ ri (dom φ) ≠ ∅`. Let `xbar ∈ H` be such that
`f xbar ∈ dom φ`. Then

`∂ (φ ∘ f) xbar = {α u | (α, u) ∈ ∂ φ (f xbar) × ∂ f xbar}`. -/
-- Route correction: `constantZeroCounterexampleViolatesChainRule` specializes the statement to
-- `f := fun _ : ℝ ↦ 0`, `φ := boltzmannEntropy`, and `xbar := 0`, where the left-hand side is
-- `{0}` and the right-hand side is `∅`. The labeled theorem is therefore not provable without an
-- additional hypothesis forcing scalar subgradient nonemptiness.
theorem subdifferential_comp_eq_iUnion_smul_of_continuous_convexOn_univ_of_monotoneOn_range
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) (hφ : φ ∈ Γ₀(ℝ))
    (hmono : MonotoneOn φ (Set.range f))
    (hregular :
      ((ri (Set.range f) + Ioi (0 : ℝ)) ∩ ri (effectiveDomain φ)).Nonempty)
    (xbar : H) (hxbar : f xbar ∈ effectiveDomain φ) :
    (∂ (φ ∘ f)) xbar = ⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar) := sorry

-- Route correction: the stronger-looking auxiliary theorem below is also false. The helper
-- `absIndicatorCounterexampleViolatesNonemptyChainRule` takes `f := |·|`, `φ := ι_[0,∞)`, and
-- `xbar := 0`; then the left-hand side is `{0}`, while the right-hand side contains `1`.
/-- Auxiliary tail-monotonicity chain rule: if `f : H → ℝ` is continuous and convex,
`φ ∈ Γ₀(ℝ)` is increasing on `(range f) + ℝ₊`, the regularity condition
`(ri (range f) + ℝ_{++}) ∩ ri (dom φ) ≠ ∅` holds, `f xbar ∈ dom φ`, and
`((∂ φ) (f xbar)).Nonempty`, then the subdifferential of `φ ∘ f` at `xbar` is the union of the
scalar multiples `α • (∂ f.toEReal) xbar` for `α ∈ (∂ φ) (f xbar)`. -/
theorem
    subdifferential_comp_eq_iUnion_smul_of_monotoneOn_range_of_subdifferential_nonempty
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) (hφ : φ ∈ Γ₀(ℝ))
    (hmono : MonotoneOn φ ((Set.range f) + Set.Ici (0 : ℝ)))
    (hregular :
      ((ri (range f) + Ioi (0 : ℝ)) ∩ ri (effectiveDomain φ)).Nonempty)
    (xbar : H) (hxbar : f xbar ∈ effectiveDomain φ)
    (hsub_nonempty : ((∂ φ) (f xbar)).Nonempty) :
    (∂ (φ ∘ f)) xbar = ⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar) := sorry

end SubdifferentialOfScalarComposition

end ERealFunction
