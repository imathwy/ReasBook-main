import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_2_1 (from Chap02) -/
universe u

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: compose `hf` with the continuous coercion `ℝ → EReal`, then apply
-- `Continuous.lowerSemicontinuous` to the resulting `EReal`-valued function.
/-- Corollary 2.1: a continuous real-valued function is closed, i.e. lower semicontinuous after
viewing it as an `EReal`-valued function. -/
theorem continuous_real_isClosed {f : E → ℝ} (hf : Continuous f) :
    LowerSemicontinuous (fun x ↦ (f x : EReal)) :=
  (continuous_coe_real_ereal.comp hf).lowerSemicontinuous

/-! ### Definition_2_1 (from Chap02) -/
universe u

section

variable {E : Type u}

/-- Definition 2.1: The effective domain of an extended real-valued function `f : E → EReal` is
the set of points where `f` takes a finite value, equivalently where `f x < ∞`. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

-- Proof sketch: Unfold `effective_domain`; membership in the defining set is exactly the
-- inequality `f x < ⊤`.
/-- A point belongs to the effective domain exactly when the function value is strictly less than
`∞`. -/
@[simp] lemma mem_effective_domain {f : E → EReal} {x : E} :
    x ∈ effective_domain f ↔ f x < ⊤ :=
  Iff.rfl

end

/-! ### Lemma_2_1 (from Chap02) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primal-space support function of `C`, obtained by evaluating the chapter owner
`support_function` along the Riesz map `InnerProductSpace.toDualMap`. This is the textbook support
function `σ_C` in Euclidean coordinates. -/
noncomputable abbrev support_function_primal (C : Set E) : E → EReal :=
  fun x ↦ support_function C (InnerProductSpace.toDualMap ℝ E x)

/-- Textbook notation for the primal-space support function. -/
notation "σ[" C "]" => support_function_primal C

-- Proof sketch: unfold `support_function_primal`; this is exactly the specialization of
-- `support_function` along `InnerProductSpace.toDualMap`.
/-- Evaluating `σ[C]` at `x` is the same as evaluating the chapter owner `support_function C` at
the dual vector corresponding to `x`. -/
@[simp] theorem support_function_primal_apply (C : Set E) (x : E) :
    σ[C] x = support_function C (InnerProductSpace.toDualMap ℝ E x) :=
  rfl

-- Proof sketch: specialize the chapter owner `support_function` along the canonical map
-- `InnerProductSpace.toDualMap ℝ E`; the resulting evaluation is exactly the supremum of the
-- pairings `c ↦ ⟪x, c⟫` over `C`.
/-- The inner-product-space support-function formula is the specialization of the chapter owner
`support_function` along `InnerProductSpace.toDualMap`, written on the source-facing owner
`σ[C]`. -/
theorem support_function_eq_sSup (C : Set E) (x : E) :
    σ[C] x = sSup ((fun c : E ↦ (inner ℝ x c : EReal)) '' C) := by
  simpa using support_function_apply C (InnerProductSpace.toDualMap ℝ E x)

-- Proof sketch: the specialized support function is the chapter owner support function on the dual
-- space, precomposed with the continuous linear map `InnerProductSpace.toDualMap`; closedness and
-- convexity are preserved under this specialization.
/-- Lemma 2.1: the support function of a subset of a real inner product space, expressed via the
chapter owner support function on the dual space and written on the source-facing owner `σ[C]`, is
closed, i.e. lower semicontinuous, and convex in the chapter owner sense `is_convex_function`. -/
theorem support_function_closed_and_convex (C : Set E) :
    LowerSemicontinuous (σ[C]) ∧ is_convex_function (σ[C]) := sorry

end

/-! ### Theorem_2_1 (from Chap02) -/
/- Theorem 2.1: for an extended-real-valued function, lower semicontinuity, closedness of the
real epigraph, and closedness of every real sublevel set are equivalent. This item is already
owned upstream in the chapter by `ereal_lowerSemicontinuous_tfae`. -/
recall ereal_lowerSemicontinuous_tfae

/-! ### proposition_2_1 (from Chap02) -/
open Set

universe u

/- Source-facing geometric description: the real epigraph of `δ_C` is exactly `C ×ˢ Ici 0`. -/
/-- The real epigraph of the extended-real-valued indicator function is `C ×ˢ Ici 0`. -/
theorem extendedIndicator_real_epigraph_eq {α : Type u} (C : Set α) :
    realEpigraph (extendedIndicator C) = C ×ˢ Ici (0 : ℝ) := by
  ext p
  by_cases hp : p.1 ∈ C <;> simp [realEpigraph, extendedIndicator, hp]

section

variable {α : Type u} [TopologicalSpace α]

-- Bridge/view layer: transport the canonical lower-semicontinuity criterion for `extendedIndicator`
-- through the chapter equivalence between lower semicontinuity and closed real epigraph.
/-- Proposition 2.1: the indicator function `δ_C` has closed real epigraph if and only if its
underlying set `C` is closed. -/
theorem extendedIndicator_isClosed_real_epigraph_iff_isClosed (C : Set α) :
    IsClosed (realEpigraph (extendedIndicator C)) ↔ IsClosed C := by
  rw [← lowerSemicontinuous_iff_isClosed_real_epigraph,
    extendedIndicator_lowerSemicontinuous_iff_isClosed]

end
