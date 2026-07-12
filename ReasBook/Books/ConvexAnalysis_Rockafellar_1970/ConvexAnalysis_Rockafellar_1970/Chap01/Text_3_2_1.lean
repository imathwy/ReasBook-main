import Mathlib.Analysis.Convex.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.2.1 states that a convex set is unchanged by writing it as the
  Minkowski sum `t C + (1 - t) C` for any weight `t` with `0 ≤ t ≤ 1`.
- `core/canonical`: the primitive owner-side statement only needs nonnegative coefficients
  `a, b` with `a + b = 1`; it is exactly the equality obtained from `Set.add_smul_subset`
  and `Convex.set_combo_subset`.
- `bridge/view`: the textbook expression uses the specialization `a = t`, `b = 1 - t`.
- Primitive data vs derived API: the canonical primitive inputs are the convex set `C` and the
  coefficient pair `(a, b)` with `a + b = 1`; the `1 - t` form is a derived bridge surface.
- Domain-style sampling: this item aligns with `Convex.set_combo_subset`, `Set.add_smul_subset`,
  and `one_smul`.
- Ambient minimization: the primitive owner theorem needs only
  `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]`; subtraction appears only in the
  textbook bridge specialization.
- Layer target: keep a primitive owner theorem at the semiring layer, and expose Text 3.2.1 as a
  thin bridge corollary.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: the owner is `Convex 𝕜 C` with pointwise `•` and `+` on
  `Set E`, with no concrete codomain specialization.
- Scalar/ambient structure too strong? `No`: the primitive owner theorem is kept at
  `[Semiring 𝕜] [PartialOrder 𝕜]` and does not use subtraction.
- Concrete-model owner leak? `No`: the owner is intrinsic (`Convex`) rather than model-specific.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is algebraic/convex, not
  a closure/interior statement.
- Owner-name and parameter surface canonical? `Yes`: use a short primitive owner name aligned with
  convex-combination data, and keep the `1 - t` text form as a bridge layer.
-/

/-- Primitive owner form behind Text 3.2.1: for a convex set `C`, nonnegative coefficients adding
up to `1` give the exact pointwise-set decomposition `C = a • C + b • C`. This is the equality
counterpart of the canonical owner `Convex.set_combo_subset`. -/
theorem Convex.set_combo_eq {C : Set E} (hC : Convex 𝕜 C) (a b : 𝕜)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    C = a • C + b • C := by
  refine Set.Subset.antisymm ?_ (hC.set_combo_subset ha hb hab)
  calc
    C = (1 : 𝕜) • C := by simp
    _ = (a + b) • C := by simp [hab]
    _ ⊆ a • C + b • C := Set.add_smul_subset a b C

end

section

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-- Text 3.2.1: if `C` is convex and `t ∈ [0, 1]`, then `C` equals the Minkowski sum
`t • C + (1 - t) • C`. This is the specialization of `Convex.set_combo_eq` at
`a = t`, `b = 1 - t`, and only needs additive order monotonicity to convert `t ≤ 1`
into `0 ≤ 1 - t`. -/
theorem Convex.eq_smul_add_one_sub {C : Set E} (hC : Convex 𝕜 C) (t : 𝕜)
    (ht : t ∈ Set.Icc (0 : 𝕜) 1) :
    C = t • C + (1 - t) • C := by
  have hsum : t + (1 - t) = (1 : 𝕜) := by
    simp
  exact hC.set_combo_eq t (1 - t) ht.1 (sub_nonneg.mpr ht.2) hsum

end
