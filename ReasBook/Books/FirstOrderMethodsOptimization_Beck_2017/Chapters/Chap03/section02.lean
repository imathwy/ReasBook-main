import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_2_1 (from Chap03) -/
universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → EReal) (x : E)
variable (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))

/- Lemma 3.2.1 is `source-facing` in the chapter directional-derivative API. The ambient owner
objects already live upstream: `directional_derivative` from Chapter 3 and
`is_convex_function`, together with its canonical source bridge
`is_convex_function_iff_segment_ineq`, from Chapter 2. Under the present `NormedSpace`
hypotheses the project has no stronger owner abstraction bundling convexity and positive
homogeneity of `directional_derivative f x`, so the public API stays with these two atomic
owner-level consequences instead of introducing a parallel wrapper. The primitive local hypothesis
is the chapter owner `x ∈ interior (finite_domain f)`, from which nearby finiteness is derived as
needed; the earlier split `effective_domain`/`≠ ⊥` assumptions are therefore not kept as public
data. -/
recall directional_derivative
recall is_convex_function
recall is_convex_function_iff_segment_ineq
recall finite_domain

-- Proof sketch: apply the chapter owner characterization of convexity from
-- `is_convex_function_iff_segment_ineq` to the function `d ↦ directional_derivative f x d`. For
-- `t ∈ [0, 1]`, compare the directional difference quotient in the mixed direction
-- `t • d₁ + (1 - t) • d₂` with the corresponding convex combination of the quotients in the
-- directions `d₁` and `d₂` using convexity of `f`, then pass to the right-hand limit. The
-- hypothesis `hx` already supplies the local finite-valued neighborhood needed to keep those
-- quotients meaningful near `0`.
/-- Lemma 3.2.1 (1): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is a convex extended-real-valued function of the direction. -/
theorem directional_derivative_is_convex_function :
    is_convex_function (directional_derivative f x) := sorry

-- Proof sketch: if `a = 0`, compute directly from the difference quotient. For `a > 0`, rewrite
-- the quotient in direction `a • d` by the change of variables `β = α * a`, factor out the scalar
-- `(a : EReal)`, and pass to the right-hand limit defining `directional_derivative`.
/-- Lemma 3.2.1 (2): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is positively homogeneous in the direction variable. -/
theorem directional_derivative_nonneg_smul (a : ℝ) (ha : 0 ≤ a) (d : E) :
    directional_derivative f x (a • d) = (a : EReal) * directional_derivative f x d := sorry

end

/-! ### Definition_3_2 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.2 is `source-facing` in the chapter subgradient API. The primitive mathematical
data already lives in Definition 3.1 as the predicate `is_subgradient_at`; the owner object
introduced here is the set-valued map `subdifferential`. Later normed/real-valued files only build
bridge/view APIs such as `strongDualSubdifferential` and `subdifferentialAt`, so this file keeps
just the owner set and its atomic membership/emptiness lemmas. -/

/-- Definition 3.2: the subdifferential `∂ f(x)` is the set of dual vectors `g ∈ E*` such that
`g` is a subgradient of `f` at `x` in the sense of Definition 3.1. Consequently, when
`x ∉ dom(f)`, this set is empty by definition. -/
def subdifferential (f : E → EReal) (x : E) : Set (Module.Dual ℝ E) :=
  is_subgradient_at f x

notation "∂" f "(" x ")" => subdifferential f x

-- Proof sketch: `subdifferential` is defined by collecting the subgradients from Definition 3.1,
-- so membership is exactly the predicate `is_subgradient_at`.
/-- Membership in the subdifferential means being a subgradient at the given point. -/
@[simp] lemma mem_subdifferential {f : E → EReal} {x : E} {g : Module.Dual ℝ E} :
    g ∈ ∂ f(x) ↔ is_subgradient_at f x g :=
  Iff.rfl

-- Proof sketch: extensionality on `g`; after rewriting membership with `mem_subdifferential`, the
-- hypothesis `x ∉ effective_domain f` makes the defining domain condition in
-- `is_subgradient_at` false, so both sides are empty.
/-- Outside the effective domain, the subdifferential is empty. -/
@[simp] theorem subdifferential_eq_empty_of_not_mem_effective_domain
    {f : E → EReal} {x : E} (hx : x ∉ effective_domain f) :
    ∂ f(x) = ∅ := by
  ext g
  change is_subgradient_at f x g ↔ False
  constructor
  · intro hg
    exact hx hg.1
  · intro hg
    exact False.elim hg

-- Proof sketch: if `g₁` and `g₂` satisfy all subgradient inequalities at `x`, then every convex
-- combination `t • g₁ + (1 - t) • g₂` satisfies the same inequalities by taking the same convex
-- combination of the two affine lower bounds; if `x ∉ effective_domain f`, the subdifferential is
-- empty, hence convex.
/-- The subdifferential `∂ f(x)` is a convex subset of the ambient dual space. -/
theorem convex_subdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ f(x)) := sorry

end

/-! ### Lemma_3_2 (from Chap03) -/
universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.2 is a `source-facing` consequence in the chapter directional-derivative API. The owner
objects are the Chapter 3 directional-derivative declarations
`has_directional_derivative_at`/`directional_derivative`, together with the owner existence theorem
`exists_real_has_directional_derivative_at_of_convex_interior_point` from Theorem 3.8 and the
Chapter 2 convexity API `is_convex_function`, with
`is_convex_function_iff_segment_ineq` supplying the canonical segment-inequality view. Unlike
Theorem 3.11, this lemma does not assume an inner-product or finite-dimensional structure, so its
main statement should remain a direct affine lower bound rather than being collapsed into a
subdifferential-max formula. -/
recall effective_domain
recall is_convex_function
recall is_convex_function_iff_segment_ineq
recall has_directional_derivative_at
recall directional_derivative
recall directional_derivative_eq_of_has_directional_derivative_at
recall exists_real_has_directional_derivative_at_of_convex_interior_point

-- Proof sketch: if `y ∉ effective_domain f`, then `f y = ⊤` and the inequality is automatic. For
-- `y ∈ effective_domain f`, restrict `f` to the segment from `x` to `y`. Convexity gives
-- `(f (x + t • (y - x)) - f x) / t ≤ f y - f x` for every `t ∈ (0, 1)`. Since `x` is an interior
-- point of `finite_domain f`, the right-hand limit of these
-- difference quotients is the directional derivative at `x` along `y - x`, and passing to the
-- limit yields the claimed affine lower bound.
/-- Lemma 3.2: if `f` is a convex extended-real-valued function that never takes the value `-∞`
and `x` lies in the interior of its effective domain, then every point `y` satisfies the affine
lower bound determined by the directional derivative of `f` at `x` in the direction `y - x`. -/
theorem value_ge_value_add_directional_derivative_of_mem_effective_domain
    (f : E → EReal) (x y : E) (hconvex : is_convex_function f)
    (h_ne_bot : ∀ z, f z ≠ ⊥) (hx : x ∈ interior (effective_domain f)) :
    f y ≥ f x + directional_derivative f x (y - x) := by
  by_cases hy : y ∈ effective_domain f
  · rcases
      exists_real_has_directional_derivative_at_of_convex_interior_point
        f x (y - x)
        hconvex
        (by
          have hfinite : finite_domain f = effective_domain f :=
            finite_domain_eq_effective_domain h_ne_bot
          simpa [hfinite] using hx) with
      ⟨ℓ, hℓ⟩
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    sorry
  · have hfy_top : f y = ⊤ := by
      have hy' : ¬ f y < ⊤ := by
        simpa [effective_domain] using hy
      exact le_antisymm le_top (not_lt.mp hy')
    simp [hfy_top]

end

/-! ### Proposition_3_2 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: unfold `subdifferential`, `extendedIndicator`, and `normal_cone`. If `x ∈ S`, then
-- `extendedIndicator S x = 0`, and the subgradient inequality is equivalent to
-- `g (z - x) ≤ 0` for every `z ∈ S`. If `x ∉ S`, then `x ∉ effective_domain (extendedIndicator S)`,
-- so `subdifferential (extendedIndicator S) x = ∅`, and `normal_cone S x` is also empty by
-- definition.
/-- Proposition 3.2: the subdifferential of the indicator function `δ_S` coincides with the normal
cone of `S` at every point. In this bridge formulation, the textbook nonemptiness hypothesis on
`S` is redundant because both sides are empty outside `S`. -/
theorem subdifferential_extended_indicator_eq_normal_cone (S : Set E) (x : E) :
    subdifferential (extendedIndicator S) x = normal_cone S x := by
  by_cases hx : x ∈ S
  · ext g
    rw [mem_subdifferential, mem_normal_cone S hx]
    constructor
    · intro hg z hz
      have hsub : (g (z - x) : EReal) ≤ 0 := by
        simpa [extendedIndicator, hx, hz] using hg.2 z
      exact_mod_cast hsub
    · intro hg
      refine ⟨by simpa using hx, ?_⟩
      intro z
      by_cases hz : z ∈ S
      · have hsub : (g (z - x) : EReal) ≤ 0 := by
          exact_mod_cast hg z hz
        simpa [extendedIndicator, hx, hz] using hsub
      · simp [extendedIndicator, hx, hz]
  · rw [subdifferential_eq_empty_of_not_mem_effective_domain, normal_cone_eq_empty_of_not_mem S hx]
    simpa using hx

end

/-! ### Theorem_3_2 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.2 is `source-facing` in finite-dimensional convex geometry. Its owner abstractions are
Mathlib's separation theorem `geometric_hahn_banach_of_nonempty_interior_point`, together with the
finite-dimensional affine-span and dual-annihilator API. The primitive data are only the convex set
`C` and the comparison point `y`; the supporting functional is derived from those owner
constructions rather than stored through any local wrapper. -/

-- Proof sketch: if `interior C` is nonempty, apply
-- `geometric_hahn_banach_of_nonempty_interior_point` directly. If `interior C = ∅`, then
-- `affineSpan ℝ C` is proper. When `y ∉ affineSpan ℝ C`, strictly separate `y` from that closed
-- affine subspace. When `y ∈ affineSpan ℝ C`, choose a nonzero functional in the dual
-- annihilator of the direction of `affineSpan ℝ C`; it is constant on the affine span, hence on
-- `C`, so its value on `C` equals its value at `y`.
/-- Theorem 3.2: supporting hyperplane theorem. A nonempty convex set and a point outside its
interior admit a nonzero continuous linear functional whose value on the set is bounded above by
its value at the point. -/
theorem supporting_hyperplane_of_not_mem_interior {C : Set E} {y : E} (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hy : y ∉ interior C) :
    ∃ p : StrongDual ℝ E, p ≠ 0 ∧ ∀ x ∈ C, p x ≤ p y := by
  by_cases hCint : (interior C).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hC_convex hy hCint
  · let A : AffineSubspace ℝ E := affineSpan ℝ C
    have hA_nonempty : (A : Set E).Nonempty := by
      rcases hC_nonempty with ⟨x, hx⟩
      exact ⟨x, by simpa [A] using subset_affineSpan ℝ C hx⟩
    by_cases hyA : y ∈ A
    · have hdir_ne_top : A.direction ≠ (⊤ : Submodule ℝ E) := by
        intro hdir
        have htop : A = (⊤ : AffineSubspace ℝ E) :=
          (AffineSubspace.direction_eq_top_iff_of_nonempty hA_nonempty).1 hdir
        exact hCint ((hC_convex.interior_nonempty_iff_affineSpan_eq_top).2 (by simpa [A] using htop))
      have hann_ne_bot :
          A.direction.dualAnnihilator ≠ (⊥ : Submodule ℝ (Module.Dual ℝ E)) := by
        intro hann
        exact hdir_ne_top ((Submodule.dualAnnihilator_eq_bot_iff).1 hann)
      obtain ⟨φ, hφmem, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann_ne_bot
      refine ⟨LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
      · exact fun hzero ↦
          hφne ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).injective hzero)
      · intro x hx
        have hxA : x ∈ A := by simpa [A] using subset_affineSpan ℝ C hx
        have hxy_dir : x - y ∈ A.direction := by
          simpa using A.vsub_mem_direction hxA hyA
        have hxy_zero : φ (x - y) = 0 :=
          (Submodule.mem_dualAnnihilator φ).1 hφmem _ hxy_dir
        have hxy_eq : φ x = φ y := sub_eq_zero.mp (by simpa using hxy_zero)
        simp [hxy_eq]
    · obtain ⟨p, α, hpA, hpy⟩ :=
        geometric_hahn_banach_closed_point A.convex A.closed_of_finiteDimensional hyA
      obtain ⟨x₀, hx₀⟩ := hC_nonempty
      refine ⟨p, ?_, fun x hx ↦ (hpA x (by simpa [A] using subset_affineSpan ℝ C hx)).le.trans hpy.le⟩
      intro hp0
      have h0lt : (0 : ℝ) < α := by
        simpa [A, hp0] using hpA x₀ (by simpa [A] using subset_affineSpan ℝ C hx₀)
      have hαlt : α < 0 := by
        simpa [hp0] using hpy
      exact (not_lt_of_ge h0lt.le hαlt).elim

end
