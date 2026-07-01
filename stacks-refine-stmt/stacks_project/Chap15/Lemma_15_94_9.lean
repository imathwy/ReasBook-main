import Mathlib
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: principal-adic completion kernels for derived-complete modules over a
  commutative ring;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `principalIdeal`,
  `principalPowerIdeal`,
  `AdicCompletion.of`;
- best owner abstraction: the source-facing principal-power intersection ideal
  `⨅ n : ℕ, principalPowerIdeal f n`, acting on the canonical completion-kernel owner
  `LinearMap.ker (AdicCompletion.of (principalIdeal f) M)`;
- primitive data: `f : A`, `M : ModuleCat A`, the derived-completeness hypothesis with respect to
  `(f)`, and the principal completion map;
- derived API: the ring specialization where the same ideal acts on its own completion kernel.

Layer triage:
- `source-facing`: the annihilation statement for the kernel of the principal completion map;
- `core/canonical`: `AdicCompletion.of`, `LinearMap.ker`, and
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the ring specialization yielding the square-zero conclusion. -/

local notation "J(" f ")" => ⨅ n : ℕ, principalPowerIdeal f n

-- Proof sketch: let `x` lie in the kernel of the principal-adic completion map and let
-- `g ∈ ⋂ n, (f)^n`. For each `n`, the kernel condition identifies `x` with an element divisible by
-- `f ^ n`, and since `g` lies in `(f)^n`, the products define a compatible sequence over the
-- localization `A_f`. Lemma `15.92.1` says every map from `A_f` into a derived-complete module
-- vanishes, so these products are all zero. Hence every element of `⋂ n, (f)^n` annihilates the
-- completion kernel.
/-- Lemma 15.94.9: if an `A`-module `M` is derived complete with respect to the principal ideal
`(f)`, then the intersection `J = ⋂ n, (f)^n` annihilates the kernel of the completion map
`M → lim_n M / (f)^n M`, modeled in Lean as `AdicCompletion.of (principalIdeal f) M`. -/
theorem principalPowerIntersection_smul_completionKernel_eq_bot_of_isDerivedComplete
    (f : A) (M : ModuleCat A)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) • LinearMap.ker (AdicCompletion.of (principalIdeal f) M) = ⊥ := sorry

-- Proof sketch: apply the previous theorem to the `A`-module `A` itself. The kernel of the
-- completion map `A → lim_n A / (f)^n` is exactly `⋂ n, (f)^n`, so the annihilation statement
-- becomes `J * J = 0`, i.e. `J ^ 2 = ⊥`.
/-- If the ring `A`, viewed as an `A`-module, is derived complete with respect to `(f)`, then the
intersection `⋂ n, (f)^n` is an ideal of square zero. -/
theorem principalPowerIntersection_sq_eq_bot_of_ring_isDerivedComplete
    (f : A)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) ^ 2 = ⊥ := sorry

end
