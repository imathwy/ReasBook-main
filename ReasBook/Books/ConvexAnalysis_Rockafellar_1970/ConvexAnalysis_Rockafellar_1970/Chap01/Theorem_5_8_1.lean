import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Rockafellar
open Function

noncomputable section

section

variable {E : Type*}
variable {ι : Type*}
variable {𝕜 : Type*}
variable {α : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.8.1 forms, from a finite family of convex functions, the function
  sending `x` to the infimum over all decompositions `x = ∑ i xᵢ` of the finite maximum of the
  values `fᵢ(xᵢ)`.
- `core/canonical`: once the ambient ordered-scalar module structure is available, this source
  owner is the chapter owner `Function.linearImage` from Theorem 5.7 applied to the finite-sum map
  `xs ↦ ∑ i, xs i` and the product-space maximum `xs ↦ ⨆ i, f i (xs i)`.
- `bridge/view`: the `Function.linearImage` presentation is the canonical bridge to the chapter
  owner; the older support-set/`verticalInfimum` packaging is only an implementation view and is
  not kept as primitive public API.
- Primitive data vs derived API: the primitive source data are the family `f` and the
  decomposition relation `∑ i, xᵢ = x`; `infimal_max_convolution` is therefore defined directly by
  the source infimum. The `Function.linearImage` comparison and convexity theorem are derived API.

Domain-style sampling used here:
- `Function.linearImage`, `Function.linearImage_eq_sInf_image`, and
  `Function.isConvex_linearImage` from `Theorem_5_7`;
- `Function.IsConvex.iSup` from `Theorem_5_5`;
- `LinearMap.lsum` / `LinearMap.lsum_apply` from mathlib's finite-product linear algebra API;
- the finite-family owner `finiteInfimalConvolution` from `Text_5_4_1`, which uses the same
  decomposition-image pattern with `∑ i` in place of `⨆ i`.

Layer target: `source-facing`; the textbook operation remains the public owner, defined directly by
its decomposition infimum, while the chapter owner `Function.linearImage` is exposed as the
canonical bridge under stronger ambient module hypotheses.
-/

private def infimalMaxConvolutionFamilyMaximum [ConditionallyCompleteLattice α] [Fintype ι]
    (f : ι → E → WithBotTop α) : (ι → E) → WithBotTop α :=
  fun xs ↦ ⨆ i, f i (xs i)

private def infimalMaxConvolutionDecompositionFiber [AddCommMonoid E] [Fintype ι] (x : E) :
    Set (ι → E) :=
  {xs : ι → E | (∑ i, xs i) = x}

private def infimalMaxConvolutionSumMap [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [Fintype ι] :
    (ι → E) →ₗ[𝕜] E :=
  let _ := Classical.decEq ι
  LinearMap.lsum 𝕜 (fun _ : ι ↦ E) ℕ fun _ ↦ LinearMap.id

section Geometric

variable [ConditionallyCompleteLattice α] [AddCommMonoid E] [Fintype ι]

/-- The finite infimal max-convolution of a finite family of `WithBotTop α`-valued functions
sends `x` to the infimum over all decompositions `x = ∑ i xᵢ` of the finite maximum value among
the terms `f i (xᵢ)`. -/
def infimal_max_convolution (f : ι → E → WithBotTop α) : E → WithBotTop α :=
  fun x ↦
    sInf
      (infimalMaxConvolutionFamilyMaximum f ''
        infimalMaxConvolutionDecompositionFiber (ι := ι) x)

/-- The value of `infimal_max_convolution f` at `x` is the infimum of the image of the
decomposition fiber `xs ↦ ⨆ i, f i (xs i)` with `∑ i, xs i = x`. -/
theorem infimal_max_convolution_eq_sInf_image_decompositions
    (f : ι → E → WithBotTop α) (x : E) :
    infimal_max_convolution f x =
      sInf
        (infimalMaxConvolutionFamilyMaximum f ''
          infimalMaxConvolutionDecompositionFiber (ι := ι) x) := rfl

/-- The value of `infimal_max_convolution f` at `x` is the infimum, over all decompositions
`x = ∑ i xᵢ`, of the finite supremum `⨆ i, f i (xᵢ)`. -/
theorem infimal_max_convolution_eq_sInf_decompositions
    (f : ι → E → WithBotTop α) (x : E) :
    infimal_max_convolution f x =
      sInf {r : WithBotTop α | ∃ xs : ι → E, (∑ i, xs i) = x ∧ r = ⨆ i, f i (xs i)} := by
  rw [infimal_max_convolution_eq_sInf_image_decompositions]
  congr 1
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, rfl⟩
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, rfl⟩

section

variable [Semiring 𝕜] [Module 𝕜 E]

-- Proof sketch: `Function.linearImage` is already the chapter owner for fiberwise infima along a
-- linear map. For the canonical finite-product sum map
-- `LinearMap.lsum 𝕜 (fun _ : ι ↦ E) ℕ (fun _ ↦ LinearMap.id)`, its fiber over `x` is exactly the
-- set of decompositions of `x`, and the source-facing value assigned to such a decomposition is
-- the family maximum `⨆ i, f i (xs i)`. This bridge stays private because its implementation
-- terms require local helper names and proof-only `DecidableEq` plumbing; the public API keeps
-- only the source-facing owner and its convexity theorem.
private theorem infimal_max_convolution_eq_linearImage
    (f : ι → E → WithBotTop α) :
    infimal_max_convolution f =
      (infimalMaxConvolutionSumMap (𝕜 := 𝕜) (E := E) (ι := ι)) ◁
        infimalMaxConvolutionFamilyMaximum f := by
  classical
  funext x
  rw [infimal_max_convolution_eq_sInf_image_decompositions, linearImage_eq_sInf_image]
  congr 1
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    refine ⟨xs, ?_, rfl⟩
    simpa [infimalMaxConvolutionDecompositionFiber, infimalMaxConvolutionSumMap,
      LinearMap.lsum_apply] using hxs
  · rintro ⟨xs, hxs, rfl⟩
    refine ⟨xs, ?_, rfl⟩
    simpa [infimalMaxConvolutionDecompositionFiber, infimalMaxConvolutionSumMap,
      LinearMap.lsum_apply] using hxs

end

end Geometric

section

variable [ConditionallyCompleteLinearOrder 𝕜] [AddCommMonoid E] [Fintype ι]
variable [Ring 𝕜] [Module 𝕜 E]
variable [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `infimal_max_convolution f` as the chapter owner
-- `Function.linearImage` of the canonical sum map on the product space `ι → E` applied to the
-- family maximum `xs ↦ ⨆ i, f i (xs i)`. For each `i`, the coordinate function
-- `xs ↦ f i (xs i)` is convex by composing `f i` with `LinearMap.proj i`, and the family maximum
-- is then convex by `Function.IsConvex.iSup`. Apply `Function.isConvex_linearImage`.
/-- Theorem 5.8.1: if `f₁, …, f_m` are convex functions, then the function
`x ↦ inf {max {f₁(x₁), …, f_m(x_m)} | x₁ + ··· + x_m = x}` is convex. -/
theorem Function.isConvex_infimal_max_convolution
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (infimal_max_convolution f).IsConvex 𝕜 := by
  classical
  rw [infimal_max_convolution_eq_linearImage (𝕜 := 𝕜) (E := E) (ι := ι) (f := f)]
  refine isConvex_linearImage (infimalMaxConvolutionSumMap (𝕜 := 𝕜) (E := E) (ι := ι))
    (infimalMaxConvolutionFamilyMaximum f) ?_
  have hfamily :
      infimalMaxConvolutionFamilyMaximum f =
        ⨆ i, (f i) ∘ (LinearMap.proj i : (ι → E) →ₗ[𝕜] E) := by
    funext xs
    simp [infimalMaxConvolutionFamilyMaximum]
  rw [hfamily]
  refine IsConvex.iSup fun i ↦ ?_
  simpa using (hf_convex i).comp_linearMap (LinearMap.proj i : (ι → E) →ₗ[𝕜] E)

end

section

variable [ConditionallyCompleteLattice α]
variable [AddCommGroup E]

-- Proof sketch: specialize `infimal_max_convolution_eq_sInf_decompositions` to `Fin 2`, where a
-- decomposition of `x` is exactly a pair `(x - y, y)`. The finite supremum over two coordinates
-- becomes `⊔`, and the decomposition set is the image of `y ↦ f₁ (x - y) ⊔ f₂ y`.
/-- Canonical `Fin 2` instance of `infimal_max_convolution`: in a lattice codomain, the binary
family supremum is `⊔`, so the operation is a one-parameter infimum of `f₁ (x - y) ⊔ f₂ y`. -/
theorem infimal_max_convolution_two_apply_sup
    (f₁ f₂ : E → WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x =
      ⨅ y : E, (f₁ (x - y)) ⊔ (f₂ y) := by
  have hsup : ∀ xs : Fin 2 → E,
      (⨆ i : Fin 2, (![f₁, f₂] i) (xs i)) = (f₁ (xs 0)) ⊔ (f₂ (xs 1)) := by
    intro xs
    rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
    simp
  have hdecomp :
      {r : WithBotTop α |
          ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧ r = ⨆ i : Fin 2, (![f₁, f₂] i) (xs i)} =
        {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
            r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} := by
    ext r
    constructor
    · rintro ⟨xs, hx, hr⟩
      exact ⟨xs, hx, hr.trans (hsup xs)⟩
    · rintro ⟨xs, hx, hr⟩
      exact ⟨xs, hx, hr.trans (hsup xs).symm⟩
  have hset :
      {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧ r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} =
        (fun y : E ↦ (f₁ (x - y)) ⊔ (f₂ y)) '' Set.univ := by
    ext r
    constructor
    · rintro ⟨xs, hx, rfl⟩
      refine ⟨xs 1, Set.mem_univ _, ?_⟩
      have hx' : xs 0 + xs 1 = x := by
        simpa [Fin.sum_univ_two] using hx
      have hx0 : xs 0 = x - xs 1 := by
        exact eq_sub_iff_add_eq.mpr hx'
      simp [hx0]
    · rintro ⟨y, -, rfl⟩
      refine ⟨![x - y, y], ?_, rfl⟩
      rw [Fin.sum_univ_two]
      exact sub_add_cancel x y
  calc
    infimal_max_convolution ![f₁, f₂] x
        = sInf {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
            r = ⨆ i : Fin 2, (![f₁, f₂] i) (xs i)} :=
          infimal_max_convolution_eq_sInf_decompositions _ _
    _ = sInf {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
          r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} := congrArg sInf hdecomp
    _ = ⨅ y : E, (f₁ (x - y)) ⊔ (f₂ y) := by
          rw [hset, sInf_image]
          simp

end

section

variable [ConditionallyCompleteLinearOrder α]
variable [AddCommGroup E]

/-- Textbook linear-order specialization of `infimal_max_convolution_two_apply_sup`: in this
setting `⊔` is `max`, yielding the one-parameter infimum of the binary maximum. -/
theorem infimal_max_convolution_two_apply
    (f₁ f₂ : E → WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x =
      ⨅ y : E, max (f₁ (x - y)) (f₂ y) := by
  simpa [sup_eq_maxDefault] using
    infimal_max_convolution_two_apply_sup (f₁ := f₁) (f₂ := f₂) x

end

end
