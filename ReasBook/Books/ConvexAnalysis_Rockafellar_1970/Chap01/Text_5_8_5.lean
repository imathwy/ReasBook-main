import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Pointwise

section

variable {E : Type*} [AddCommMonoid E]
variable {α : Type*} [ConditionallyCompleteLinearOrder α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.5 identifies the strict `μ`-sublevel set of the binary infimal
  max-convolution with the Minkowski sum of the strict `μ`-sublevel sets of the two input
  functions.
- `core/canonical`: the chapter owner abstraction is `infimal_max_convolution` from
  `Theorem_5_8_1`, specialized here to the canonical `Fin 2` family `![f₁, f₂]`.
- `bridge/view`: the `Fin 2` decomposition data `xs : Fin 2 → E` is the source-facing binary
  presentation of the owner object. The subtraction-based formula
  `x ↦ ⨅ y, max (f₁ (x - y)) (f₂ y)` from `Theorem_5_8_1` is a further bridge view available under
  stronger additive-group hypotheses, but it is not the right owner layer for this strict-sublevel
  identity.
- Primitive data vs derived API: the primitive data are the two functions `f₁`, `f₂`; the
  strict-sublevel-set identity is derived API of the owner construction, and the one-parameter
  infimum-of-`max` formula is a source-facing view.

Domain-style sampling used here:
- the chapter owner `infimal_max_convolution`;
- its owner-side decomposition formula `infimal_max_convolution_eq_sInf_decompositions`;
- `sInf_lt_iff` on `WithTopBot α`, `Fin.sum_univ_two`, and the order operation `max`;
- pointwise set addition on subsets of `E`.

The source phrases this corollary for proper convex functions on `ℝ^n`, but the displayed
set-theoretic identity depends only on the binary infimal-max construction itself. As in
`Text_5_4_0`, `Text_5_4_1`, and `Theorem_5_8_1`, the Lean statements therefore live at the
intrinsic additive-monoid owner level, with Euclidean-space applications handled by
specialization.
-/

/-- Bridge lemma for Text 5.8.5: the strict sublevel inequality for the binary infimal
max-convolution is equivalent to the existence of a binary decomposition whose two values are both
strictly below `μ`. -/
-- Proof sketch: rewrite the binary owner with the upstream bridge
-- `infimal_max_convolution_eq_sInf_decompositions`, then specialize the `Fin 2` family maximum to
-- `max`. A witness decomposition `xs : Fin 2 → E` with `x = xs 0 + xs 1` yields the two strict
-- inequalities, and conversely any decomposition `x = u + v` with strict bounds at `u` and `v`
-- gives a witness family `![u, v]` for the owner-side infimum.
private theorem infimal_max_convolution_two_lt_iff_exists_add
    (f₁ f₂ : E → WithTopBot α) (μ : WithTopBot α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x < μ ↔
      ∃ u v, f₁ u < μ ∧ f₂ v < μ ∧ u + v = x := by
  have hmax : ∀ xs : Fin 2 → E,
      (⨆ i : Fin 2, (![f₁, f₂] i) (xs i)) = max (f₁ (xs 0)) (f₂ (xs 1)) := by
    intro xs
    rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
    simp
  constructor
  · intro hx
    rw [infimal_max_convolution_eq_sInf_decompositions] at hx
    rcases sInf_lt_iff.mp hx with ⟨r, ⟨xs, hxs, rfl⟩, hr⟩
    have hlt : max (f₁ (xs 0)) (f₂ (xs 1)) < μ := by
      rw [← hmax xs]
      exact hr
    exact ⟨xs 0, xs 1, (max_lt_iff.mp hlt).1, (max_lt_iff.mp hlt).2,
      by simpa [Fin.sum_univ_two] using hxs⟩
  · intro hx
    rcases hx with ⟨u, v, hu, hv, huv⟩
    rw [infimal_max_convolution_eq_sInf_decompositions]
    refine sInf_lt_iff.mpr ?_
    refine ⟨max (f₁ u) (f₂ v), ?_, max_lt_iff.mpr ⟨hu, hv⟩⟩
    refine ⟨![u, v], ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using huv
    · rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
      simp

/-- Pointwise owner-level form of Text 5.8.5: the strict sublevel inequality for the binary
infimal max-convolution is equivalent to membership in the Minkowski sum of strict sublevel sets
of the two input functions. -/
theorem infimal_max_convolution_two_lt_iff_mem_add_strict_sublevel_set
    (f₁ f₂ : E → WithTopBot α) (μ : WithTopBot α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x < μ ↔
      x ∈ {u : E | f₁ u < μ} + {v : E | f₂ v < μ} := by
  constructor
  · intro hx
    rcases (infimal_max_convolution_two_lt_iff_exists_add (f₁ := f₁) (f₂ := f₂) (μ := μ)
      (x := x)).mp hx with ⟨u, v, hu, hv, huv⟩
    exact Set.mem_add.mpr ⟨u, hu, v, hv, huv⟩
  · intro hx
    rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
    exact (infimal_max_convolution_two_lt_iff_exists_add (f₁ := f₁) (f₂ := f₂) (μ := μ)
      (x := x)).mpr ⟨u, v, hu, hv, huv⟩

/-- Text 5.8.5: the strict `μ`-sublevel set of the binary infimal max-convolution is the
Minkowski sum of the strict `μ`-sublevel sets of the two input functions. -/
theorem infimal_max_convolution_two_strict_sublevel_set_eq_add
    (f₁ f₂ : E → WithTopBot α) (μ : WithTopBot α) :
    {x : E | infimal_max_convolution ![f₁, f₂] x < μ} =
      {u : E | f₁ u < μ} + {v : E | f₂ v < μ} := by
  ext x
  simpa using infimal_max_convolution_two_lt_iff_mem_add_strict_sublevel_set
    (f₁ := f₁) (f₂ := f₂) (μ := μ) (x := x)

end
