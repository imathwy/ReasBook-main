

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_10 (from Chap04) -/
open InnerProductSpace (toDualMap)

noncomputable section

section

/- Proposition 4.10 is `source-facing`: its main content is that the scalar Fenchel objective
`x ↦ x * y - |x|^p / p` attains its maximum. The `core/canonical` owner abstraction for Chapter 4
conjugacy statements is `conjugate_function`, specialized on `ℝ` via `toDualMap ℝ ℝ`. There is no
additional primitive data here beyond that source integrand; the owner-level conjugacy formula
below is derived `bridge/view` API for downstream reuse. -/
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: rewrite the objective as the equality case of Young's inequality for the
-- Hölder-conjugate exponents `p` and `q`. The upper bound comes from `Real.young_inequality`,
-- and equality is attained at `x = sign y * |y| ^ (q - 1)`.
/-- Proposition 4.10: for the function `f(x) = |x|^p / p` with Hölder-conjugate exponent `q`,
the maximum of `x ↦ x * y - |x|^p / p` is `|y|^q / q`. Equivalently, the conjugate of
`x ↦ |x|^p / p` is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_isGreatest {p q : ℝ} (hpq : p.HolderConjugate q)
    (y : ℝ) :
    IsGreatest (Set.range fun x : ℝ ↦ x * y - (|x| ^ p) / p) ((|y| ^ q) / q) := sorry

-- Proof sketch: express the scalar Fenchel conjugate through the owner declaration
-- `conjugate_function` on `ℝ`, then identify its defining `sSup` with the greatest value from
-- `power_absolute_function_conjugate_isGreatest`.
/-- Proposition 4.10 in the Chapter 4 owner formulation: for `f(x) = |x|^p / p`, the Fenchel
conjugate `f*`, evaluated on `ℝ` via `toDualMap ℝ ℝ`, is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_eq {p q : ℝ} (hpq : p.HolderConjugate q) (y : ℝ) :
    conjugate_function (fun x : ℝ ↦ (((|x| ^ p) / p : ℝ) : EReal)) (toDualMap ℝ ℝ y) =
      (((|y| ^ q) / q : ℝ) : EReal) := sorry

end

/-! ### Theorem_4_10 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.10 is `source-facing` in the chapter Fenchel/subdifferential API. Domain sampling
shows that the `core/canonical` owners are already upstream: `is_convex_function` from
Definition 2.6, `subdifferential` from Definition 3.2, and `conjugate_function` from
Definition 4.1, together with the bridge theorems
`biconjugate_function_eq_self_of_closed_convex` from Theorem 4.2 and
`isProperExtendedRealFunction_conjugate_function` from Theorem 4.15. The primitive data here are
only `f`, `x`, `y`, and the genuinely active hypotheses; the subdifferential and conjugate
expressions are derived views through those owners, so this file keeps only the equivalence
theorems and no parallel local wrappers. -/

recall is_convex_function
recall subdifferential
recall conjugate_function

-- Proof sketch: rewrite `y ∈ subdifferential f x` using the defining subgradient inequality, then
-- rearrange it to the statement that `(y x : EReal) - f x` dominates every value
-- `(y z : EReal) - f z`. This says exactly that the value at `x` attains the supremum defining
-- `conjugate_function f y`, yielding Fenchel--Young equality, and the converse is the same
-- rearrangement in reverse. Only the no-`⊥` hypothesis is needed here to avoid `EReal`
-- pathologies; the nonempty-effective-domain part of properness is redundant because the statement
-- is already localized at the explicit point `x`. Convexity is not part of this equivalence.
/-- Theorem 4.10: if `f` never takes the value `-∞`, then Fenchel--Young equality at `(x, y)` is
equivalent to `y` belonging to the subdifferential of `f` at `x`. -/
theorem pairing_eq_add_conjugate_iff_mem_subdifferential
    (f : E → EReal) (hf_ne_bot : ∀ z, f z ≠ ⊥) (x : E) (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔ y ∈ subdifferential f x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply `pairing_eq_add_conjugate_iff_mem_subdifferential` to the conjugate
-- function `conjugate_function f` at the pair `(y, Module.Dual.eval ℝ E x)`. The resulting
-- Fenchel--Young equality for `f*` uses the no-`⊥` half of
-- `isProperExtendedRealFunction_conjugate_function`, and then rewrites through the biconjugate
-- identity `biconjugate_function_eq_self_of_closed_convex` to recover the original equality
-- `(y x : EReal) = f x + f*(y)`. Properness of `f` is semantically active here: for `f ≡ ⊤`, the
-- left-hand side is always false while `conjugate_function f = ⊥`, so the right-hand side becomes
-- trivially true.
/-- Under properness, convexity, and lower semicontinuity, Fenchel--Young equality at `(x, y)` is
equivalent to the canonical double-dual image of `x` lying in the subdifferential of the conjugate
`f*` at `y`. -/
theorem pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f) (x : E)
    (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔
      Module.Dual.eval ℝ E x ∈ subdifferential (conjugate_function f) y := sorry

end
