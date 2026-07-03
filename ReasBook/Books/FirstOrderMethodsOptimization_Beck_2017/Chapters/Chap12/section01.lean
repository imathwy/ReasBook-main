import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_1 (from Chap12) -/
universe u v

section

open Set

variable {E : Type u} {Y : Type v}

/- Definition 12.1 has two layers:
- `bridge/view`: the primal objective `x ↦ f x + g (A x)` is the Chapter 10 owner
  `composite_model_objective` specialized to the pair of summands `f` and `g ∘ A`;
- `source-facing`: the associated primal optimal value.

Domain sampling in the surrounding project gives:
- `source-facing`: the primal model `x ↦ f x + g (A x)`;
- `core/canonical`: `composite_model_objective` from Definition 10.2;
- `bridge/view`: precomposition of the second term along `A`, namely `g ∘ A`.

The primitive data are therefore only `f`, `g`, and `A`; no new Chapter 12 owner object is needed.
The only genuinely new declaration in this file is the source-facing optimal value attached to the
canonical objective `composite_model_objective f (g ∘ A)`. -/

/- Definition 12.1: the primal objective for the dual-based proximal-gradient model is the
Chapter 10 composite objective specialized to `f` and `g ∘ A`. -/
recall composite_model_objective
recall composite_model_objective_apply

/-- The optimal value `f_opt` of the dual-based primal model is the infimum of the range of the
primal objective `x ↦ f x + g (A x)`. -/
noncomputable def dual_based_proximal_gradient_primal_optimal_value
    (f : E → EReal) (g : Y → EReal) (A : E → Y) : EReal :=
  sInf (range (composite_model_objective f (g ∘ A)))

-- Proof sketch: unfold `dual_based_proximal_gradient_primal_optimal_value`; the statement is the
-- defining `sInf` formula for the primal optimal value.
/-- Expanding the primal optimal value gives the infimum of the attained objective values. -/
@[simp] theorem dual_based_proximal_gradient_primal_optimal_value_eq_sInf
    (f : E → EReal) (g : Y → EReal) (A : E → Y) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf (range (composite_model_objective f (g ∘ A))) := rfl

end

/-! ### Definition_12_1_1 (from Chap12) -/
universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/- Definition 12.1.1 is `source-facing`: it packages the standing assumptions for the Chapter 12
dual-based proximal-gradient model `min_x {f x + g (A x)}`. Domain sampling in the surrounding
project fixes the owner abstractions already in play:
- `PosReal` from Chapter 6 for the primitive positive strong-convexity modulus,
- `IsProperExtendedRealFunction` from Chapter 2 for extended-real properness,
- `StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)` from Chapter 5 for strong
  convexity once the positive modulus is viewed in `ℝ`,
- `is_convex_function` from Chapter 2 for convexity, and
- `intrinsicInterior ℝ` for the relative-interior qualification.

Primitive data are therefore exactly the assumptions on `f`, `g`, and the qualification.
Derived API should stay small: the existential reformulation of the qualification, not an
auxiliary conjunction package or projection wrappers around fields that are already primitive. -/

-- Proof sketch: unpack the nonempty intersection as a point `x̂` lying in
-- `intrinsicInterior ℝ (effective_domain f)` whose image under `A` lies in
-- `intrinsicInterior ℝ (effective_domain g)`, and take `ẑ = A x̂`. The reverse direction rewrites
-- the image condition `A x̂ = ẑ` as membership in the preimage.
/-- The relative-interior qualification for the linear map `A` is equivalent to the source wording
that there exist `x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
theorem qualification_nonempty_iff_exists_ri_map_eq
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    (intrinsicInterior ℝ (effective_domain f) ∩
      A ⁻¹' intrinsicInterior ℝ (effective_domain g)).Nonempty ↔
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain f),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain g), A xHat = zHat := by
  constructor
  · rintro ⟨xHat, hxHat, hzHat⟩
    exact ⟨xHat, hxHat, A xHat, hzHat, rfl⟩
  · rintro ⟨xHat, hxHat, zHat, hzHat, hAz⟩
    refine ⟨xHat, hxHat, ?_⟩
    change A xHat ∈ intrinsicInterior ℝ (effective_domain g)
    simpa [hAz] using hzHat

/-- Definition 12.1.1: Assumption 12.1 means that `f : E → (-∞, ∞]` is proper, closed, and
`σ`-strongly convex for a positive parameter `σ : PosReal`; `g : V → (-∞, ∞]` is proper, closed,
and convex; `A : E →ₗ[ℝ] V` is linear; and the relative interiors of `dom f` and `dom g` satisfy
the qualification `ri (dom f) ∩ A⁻¹' (ri (dom g)) ≠ ∅`, equivalently there exist
`x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
class IsDualBasedProximalGradientProblem
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal) : Prop
    extends IsProperExtendedRealFunction f where
  f_closed : LowerSemicontinuous f
  f_strongly_convex :
    StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)
  g_proper : IsProperExtendedRealFunction g
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  qualification :
    (intrinsicInterior ℝ (effective_domain f) ∩
      A ⁻¹' intrinsicInterior ℝ (effective_domain g)).Nonempty

namespace IsDualBasedProximalGradientProblem

/-- Assumption 12.1 provides a point `x̂ ∈ ri(dom f)` whose image `A x̂` lies in
`ri(dom g)`. Equivalently, there exist `x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
theorem exists_mem_intrinsicInterior_map_eq
    {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V} {σ : PosReal}
    (h : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ xHat ∈ intrinsicInterior ℝ (effective_domain f),
      ∃ zHat ∈ intrinsicInterior ℝ (effective_domain g), A xHat = zHat :=
  (qualification_nonempty_iff_exists_ri_map_eq f g A).1 h.qualification

end IsDualBasedProximalGradientProblem

end

/-! ### Proposition_12_1 (from Chap12) -/
/- Proposition 12.1 is `source-facing`: it isolates the strong-duality equality from the stronger
Chapter 12 owner theorem `dual_based_proximal_gradient_strong_duality_with_dual_attainment`.
The equality companion itself is now owned by `Theorem_12_2`, so this file reuses that canonical
chapter theorem directly rather than keeping a parallel local projection wrapper. -/
recall dual_based_proximal_gradient_problem_strong_duality
