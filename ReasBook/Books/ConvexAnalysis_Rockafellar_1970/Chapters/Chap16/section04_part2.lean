import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_16_4_2 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

universe u

section

variable {ι : Type*} [Fintype ι]
variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.2 states the dual formula
  `(cl f₁ + ··· + cl f_m)^* = cl (f₁^* □ ··· □ f_m^*)` for a finite family of proper convex
  functions.
- `core/canonical`: the project owners already present are `lowerSemicontinuousHull` for the
  closure `cl`, `convexConjugate` for `f*`, `finiteInfimalConvolution` for `□`, and the chapter
  predicates `Function.IsConvex` and `Function.IsProper`.
- `bridge/view`: the textbook sum of closures is rendered directly by the pointwise finite sum
  `∑ i, cl(f i)`, so no surrogate wrapper is introduced.

Domain-style sampling used here:
- `convexConjugate_finiteInfimalConvolution_eq_sum` from Theorem 16.4.1;
- `Function.IsConvex.convexConjugate_isProper_iff` from Theorem 12.2;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from Theorem 12.2;
- `Function.isConvex_finiteInfimalConvolution` from Theorem 5.4.

Primitive data vs derived API:
- primitive input: a finite family `f : ι → E → WithBotTop 𝕜`;
- primitive owner-side hypothesis for the core identity: pointwise exclusion of `⊥` for each
  conjugate summand `f i⋆`, stated directly as `((f i)⋆) x ≠ ⊥`;
- source-facing companion hypothesis: properness of each `f i`, used only to recover the previous
  primitive condition through Theorem 12.2;
- derived API: the duality identity itself.

Layer target: `source-facing`. The source states the theorem on `R^n` for a finite nonempty
family, but the owner declarations it uses already live on arbitrary finite-dimensional scalar
field spaces equipped with a continuous linear self-pairing and arbitrary finite index types, so
this file keeps the theorem on that canonical ambient owner layer.
-/

-- Proof sketch: apply Theorem 16.4.1 to the conjugate family `fun i ↦ convexConjugate (f i)`.
-- Theorem 12.2 identifies the biconjugates `f i⋆⋆` with `lowerSemicontinuousHull (f i)`. This
-- gives that the conjugate of
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i))` is the pointwise sum of the closures
-- `cl f_i`. Applying Theorem 12.2 once more to that convex finite infimal convolution identifies
-- its biconjugate with the lower semicontinuous hull on the right-hand side.
/-- Theorem 16.4.2 at the primitive owner layer: for a finite family of convex functions on a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, if each
conjugate summand is never `⊥`, then the conjugate of the pointwise sum of the closures
`cl f_i` is the closure of the finite infimal convolution of the individual conjugates. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_conj_ne_bot : ∀ i x, ((f i)⋆ : E → WithBotTop 𝕜) x ≠ ⊥) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hsum_cl :
      (∑ i, cl(f i)) = (∑ i, ((f i)⋆⋆ : E → WithBotTop 𝕜)) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa using ((hf_convex i).biconjugate_eq_lowerSemicontinuousHull).symm
  have hsum_conj :
      (∑ i, ((f i)⋆⋆ : E → WithBotTop 𝕜)) =
        ((finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)))⋆ :
          E → WithBotTop 𝕜) := by
    simpa using
      (convexConjugate_finiteInfimalConvolution_eq_sum
        (f := fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))
        hf_conj_ne_bot).symm
  have hconvex_finiteInfimalConvolution :
      (finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))).IsConvex 𝕜 := by
    refine Function.isConvex_finiteInfimalConvolution
      (f := fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) ?_
    intro i
    simpa using (Function.isConvex_convexConjugate (f := f i))
  calc
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
        ((((finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)))⋆)⋆) :
          E → WithBotTop 𝕜) := by
      rw [hsum_cl, hsum_conj]
    _ = cl(finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜))) := by
      simpa using hconvex_finiteInfimalConvolution.biconjugate_eq_lowerSemicontinuousHull

/-- Owner-bridge companion for Theorem 16.4.2: the same identity under the conjugate-side properness
owner hypothesis. This is a direct reformulation of the primitive `⊥`-exclusion hypothesis via
`Function.IsProper.ne_bot`. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_conjugate_proper
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_conj_proper : ∀ i, ((f i)⋆ : E → WithBotTop 𝕜).IsProper) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hconj_ne_bot : ∀ i x, ((f i)⋆ : E → WithBotTop 𝕜) x ≠ ⊥ := by
    intro i x
    exact (hf_conj_proper i).ne_bot x
  simpa using
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution
      (f := f) hf_convex hconj_ne_bot

/-- Properness-form companion of Theorem 16.4.2. This adds no new mathematics: it only recovers
the primitive conjugate-side `⊥`-exclusion hypothesis from
`Function.IsConvex.convexConjugate_isProper_iff`. -/
theorem
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_proper_convex
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper) :
    ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  have hconj_proper : ∀ i, ((f i)⋆ : E → WithBotTop 𝕜).IsProper := by
    intro i
    exact ((hf_convex i).convexConjugate_isProper_iff).2 (hf_proper i)
  simpa using
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_conjugate_proper
      (f := f) hf_convex hconj_proper

end

/-! ### Text_16_4_3 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar PolarCone

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
variable [Module 𝕜 E] [PosSMulMono 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
  [PosSMulMono 𝕜 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module 𝕜 E] [PosSMulMono 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜] in
private theorem indicatorFunction_isProper_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) :
    (δ[𝕜](· | C) : E → WithBotTop 𝕜).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨?_, ?_⟩
  · rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_effectiveDomain]
    simpa [indicator_def, hx] using (WithBotTop.coe_lt_top (0 : 𝕜))
  · intro x
    by_cases hx : x ∈ C <;> simp [hx]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.3 restricts a closed proper convex function `h` to the ambient
  nonnegative cone by assigning the value `+∞` outside `E≥0`, then identifies the Fenchel
  conjugate of that restriction.
- `core/canonical`: the project owners already present are `indicator` for the orthant
  restriction, `convexConjugate` for Fenchel duality, `lowerSemicontinuousHull` for the closure
  `cl`, and the chapter source-facing owner `orthantInfimumMinorant` for the profile
  `x⋆ ↦ inf {h*(z⋆) | z⋆ ≥ x⋆}`.
- `bridge/view`: the primal function is written in the owner form
  `h + δ[𝕜](· | E≥0)`, and the dual profile is expressed through
  `orthantInfimumMinorant h⋆` rather than reintroducing a parallel subtype-`iInf` encoding.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from Text 12.3.6;
- `convexConjugate` from Definition 12.2;
- `lowerSemicontinuousHull` from Text 7.0.4;
- `orthantInfimumMinorant` from Example 9.2.2.3.

Primitive data vs derived API:
- primitive input: a closed proper convex function `h : E → WithBotTop 𝕜`;
- source-facing derived datum: the orthant-restricted function
  `h + δ[𝕜](· | E≥0)`;
- source-facing dual profile owner: `orthantInfimumMinorant h⋆`;
- derived conclusion: the conjugate of the orthant restriction is the lower-semicontinuous hull of
  that dual profile.

Layer target: `source-facing`; the item keeps the textbook orthant restriction and reuses the
chapter's existing owner for the orthant-filtered infimum instead of restating the same notion with
new coordinate-level syntax. The current closure-conjugacy bridge used below (Theorem 16.4.2) is
still authored on a self-pairing ambient owner, so this source item inherits that `E`-to-`E`
duality interface pending an upstream pairing-side generalization.
-/

-- Proof sketch: specialize Theorem 16.4.2 to the two-function family
-- `(δ[𝕜](· | E≥0), h)`. Rewrite the left side using `cl(δ[𝕜](· | E≥0)) = δ[𝕜](· | E≥0)` and
-- `cl(h) = h`. Rewrite the dual indicator summand by Theorem 14.1 plus the orthant polar bridge
-- hypothesis `E≥0ᵒ[𝕜] = -E≥0`, then use the `Fin 2` infimal-convolution bridge and
-- `orthantInfimumMinorant_eq_infimal_convolution_indicator_neg`.
/-- Text 16.4.3: if `h` is a closed proper convex function on an ordered module, then the Fenchel
conjugate of the function equal to `h` on `E≥0` and `+∞` outside it is the closure of the
profile `x⋆ ↦ inf {h*(z⋆) | z⋆ ≥ x⋆}`, reused here through the existing chapter owner
`orthantInfimumMinorant h⋆`.

This source-facing form is stated under two geometric bridge hypotheses used in the proof:
`E≥0` is closed and its polar cone is the nonpositive orthant `-E≥0`. -/
theorem convexConjugate_orthantRestriction_eq_lowerSemicontinuousHull_conjugate_infimum_above
    (h : E → WithBotTop 𝕜) (hh : IsClosedProperConvex[𝕜] h)
    (hE_closed : IsClosed (E≥0 : Set E))
    (hpolar : (E≥0 : Set E)ᵒ[𝕜] = -E≥0) :
    (h + (δ[𝕜](· | E≥0) : E → WithBotTop 𝕜))⋆ =
      cl(orthantInfimumMinorant (h⋆ : E → WithBotTop 𝕜)) := by
  let f : Fin 2 → E → WithBotTop 𝕜 := fun i ↦ if i = 0 then (δ[𝕜](· | E≥0)) else h
  have hconv_pos : Convex 𝕜 (E≥0 : Set E) :=
    ConvexCone.convex (ConvexCone.positive 𝕜 E)
  have hnonempty_pos : (E≥0 : Set E).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  have hf_convex : ∀ i, (f i).IsConvex 𝕜 := by
    intro i
    by_cases hi : i = 0
    · simpa [f, hi] using
        ((indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) (E≥0 : Set E)).2 hconv_pos)
    · simpa [f, hi] using hh.convex
  have hf_proper : ∀ i, (f i).IsProper := by
    intro i
    by_cases hi : i = 0
    · simpa [f, hi] using
        indicatorFunction_isProper_of_nonempty (C := (E≥0 : Set E)) hnonempty_pos
    · simpa [f, hi] using hh.proper
  have hsum :=
    convexConjugate_sum_cl_eq_cl_finiteInfimalConvolution_of_proper_convex
      (f := f) hf_convex hf_proper
  have hcl_h : cl(h) = h := by
    exact lowerSemicontinuousHull_eq_self (f := h) hh.closed
  have hcl_indicator :
      cl((δ[𝕜](· | E≥0) : E → WithBotTop 𝕜)) = (δ[𝕜](· | E≥0) : E → WithBotTop 𝕜) := by
    calc
      cl((δ[𝕜](· | E≥0) : E → WithBotTop 𝕜)) =
          (δ[𝕜](· | closure (E≥0 : Set E)) : E → WithBotTop 𝕜) :=
        lowerSemicontinuousHull_indicator_eq_indicator_closure (X := E) (𝕜 := 𝕜)
          (C := (E≥0 : Set E))
      _ = (δ[𝕜](· | E≥0) : E → WithBotTop 𝕜) := by rw [hE_closed.closure_eq]
  have hsum_left : (∑ i, cl(f i)) = h + (δ[𝕜](· | E≥0)) := by
    classical
    calc
      (∑ i, cl(f i)) = cl(f 0) + cl(f 1) := by
        exact Fin.sum_univ_two (f := fun i ↦ cl(f i))
      _ = cl((δ[𝕜](· | E≥0))) + cl(h) := by simp [f]
      _ = (δ[𝕜](· | E≥0)) + h := by rw [hcl_indicator, hcl_h]
      _ = h + (δ[𝕜](· | E≥0)) := by rw [add_comm]
  have hconj_proper : (h⋆ : E → WithBotTop 𝕜).IsProper :=
    ((hh.convex.convexConjugate_isProper_iff).2 hh.proper)
  have hhstar_bot : ∀ y : E, ⊥ < (h⋆ : E → WithBotTop 𝕜) y := fun y ↦ hconj_proper.bot_lt y
  have horthant : orthantInfimumMinorant (h⋆ : E → WithBotTop 𝕜) =
      infimal_convolution (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) (h⋆ : E → WithBotTop 𝕜) := by
    simpa [infimal_convolution] using
      (orthantInfimumMinorant_eq_infimal_convolution_indicator_neg
        (𝕜 := 𝕜) (E := E) (f := (h⋆ : E → WithBotTop 𝕜)) hhstar_bot)
  have hcone_pos : Set.IsCone 𝕜 (E≥0 : Set E) := by
    simpa using (ConvexCone.isCone (C := ConvexCone.positive 𝕜 E))
  have hindicator_conj :
      (((δ[𝕜](· | E≥0))⋆ : E → WithBotTop 𝕜)) =
        (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) := by
    calc
      (((δ[𝕜](· | E≥0))⋆ : E → WithBotTop 𝕜)) =
          (δ[𝕜](· | (E≥0 : Set E)ᵒ[𝕜]) : E → WithBotTop 𝕜) :=
        convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
          (𝕜 := 𝕜) (K := (E≥0 : Set E)) hnonempty_pos hcone_pos
      _ = (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) := by rw [hpolar]
  have hfin2' :
      finiteInfimalConvolution (fun i : Fin 2 ↦ (f i)⋆) =
        infimal_convolution ((((fun i : Fin 2 ↦ (f i)⋆) 0) : E → WithBotTop 𝕜))
          ((((fun i : Fin 2 ↦ (f i)⋆) 1) : E → WithBotTop 𝕜)) := by
    simpa [infimal_convolution] using finiteInfimalConvolution_two_eq_infimal_convolution
      (f := fun i : Fin 2 ↦ (f i)⋆)
  have hfin2 :
      finiteInfimalConvolution (fun i : Fin 2 ↦ (f i)⋆) =
        infimal_convolution (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) (h⋆ : E → WithBotTop 𝕜) := by
    calc
      finiteInfimalConvolution (fun i : Fin 2 ↦ (f i)⋆) =
          infimal_convolution ((((fun i : Fin 2 ↦ (f i)⋆) 0) : E → WithBotTop 𝕜))
            ((((fun i : Fin 2 ↦ (f i)⋆) 1) : E → WithBotTop 𝕜)) := hfin2'
      _ = infimal_convolution (((δ[𝕜](· | E≥0))⋆ : E → WithBotTop 𝕜))
            (h⋆ : E → WithBotTop 𝕜) := by simp [f]
      _ = infimal_convolution (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) (h⋆ : E → WithBotTop 𝕜) := by
        rw [hindicator_conj]
  calc
    (h + (δ[𝕜](· | E≥0) : E → WithBotTop 𝕜))⋆ = ((∑ i, cl(f i))⋆ : E → WithBotTop 𝕜) := by
      rw [hsum_left]
    _ = cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := hsum
    _ = cl(infimal_convolution (δ[𝕜](· | -E≥0) : E → WithBotTop 𝕜) (h⋆ : E → WithBotTop 𝕜)) := by
      rw [hfin2]
    _ = cl(orthantInfimumMinorant (h⋆ : E → WithBotTop 𝕜)) := by
      simp [horthant]

end

/-! ### Theorem_16_4_3 (from Chap03) -/
open scoped BigOperators
open scoped Rockafellar

noncomputable section

section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.4.3 is the closure-free refinement of Theorem 16.4.2 for a finite
  nonempty family of proper convex functions on a finite-dimensional pairing space.
  Under a common relative-interior point of the effective domains, it removes both outer closure
  operators and adds attainment of the defining infimum.
- `core/canonical`: the owner abstractions already present are `convexConjugate` for Fenchel
  conjugation, `finiteInfimalConvolution` for the finite infimal convolution, and
  `riDom[𝕜](f)` for `ri (dom f)`.
- `bridge/view`: the source formula is rendered directly by those owners, so no surrogate package
  or auxiliary wrapper is introduced.

Domain-style sampling used here:
- the closure-level conjugacy theorem from `Theorem_16_4_2`;
- `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom`
  from `Theorem_9_3`;
- `common_riDom_nonempty_iff_no_zero_sum_asymmetric_conjugate_recession`
  from `Corollary_16_2_2`;
- `exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession`
  from `Corollary_9_2_1`.

Primitive data vs derived API:
- primitive inputs: the finite nonempty family `f`;
- owner hypotheses: convexity and properness of each `f i`, together with a common point of the
  relative interiors `riDom[𝕜](f i)`;
- derived API: the closure-free conjugacy identity and the attainment statement for the defining
  infimum of the conjugate-side finite infimal convolution.

Layer target: `source-facing`, expressed directly in the canonical finite-family conjugacy API.
-/

-- Proof sketch: start from Theorem 16.4.2, which identifies the conjugate of the sum of the
-- lower-semicontinuous hulls with the lower-semicontinuous hull of the finite infimal convolution
-- of the conjugates. The common-relative-interior hypothesis removes the closure on the primal
-- sum by
-- `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom`,
-- and Corollary 16.2.2 plus
-- Corollary 9.2.1 remove the closure on the dual infimal convolution.
/-- Theorem 16.4.3: if a finite nonempty family of proper convex functions on a
finite-dimensional pairing space has a common relative-interior point in the effective domains
`ri (dom f_i)`, then the closure operations in Theorem 16.4.2 are unnecessary:
`(f₁ + ··· + f_m)⋆ = f₁⋆ □ ··· □ f_m⋆`, rendered by `convexConjugate` and
`finiteInfimalConvolution`. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior
    (f : ι → E → WithBotTop 𝕜)
    (_ : ∀ i, (f i).IsConvex 𝕜)
    (_ : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty) :
    convexConjugate (fun x ↦ ∑ i, f i x) =
      finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) := sorry

-- Proof sketch: once the dual function is identified with
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i))`, apply the attainment clause of
-- Corollary 9.2.1 to the conjugate family. Corollary 16.2.2 supplies exactly the recession
-- hypothesis needed for that attainment statement under the same common-relative-interior
-- assumption.
/-- Under the common-relative-interior hypothesis of Theorem 16.4.3, the infimum defining the
dual finite infimal convolution `f₁⋆ □ ··· □ f_m⋆` is attained at every `x⋆`. -/
theorem exists_sum_eq_finiteInfimalConvolution_conjugates_of_common_intrinsicInterior
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty)
    (xStar : E) :
    ∃ xs : ι → E,
      (∑ i, xs i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) xStar =
          ∑ i, ((f i)⋆ : E → WithBotTop 𝕜) (xs i) := sorry

end

/-! ### Text_16_4_4 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {ι : Type*} [Fintype ι]

local notation "E" => ι → ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.4 computes the Fenchel conjugate of the negative entropy
  `∑ i ξᵢ log ξᵢ` on the simplex `{ξ | ξᵢ ≥ 0, ∑ i ξᵢ = 1}`, extended by `+∞` outside that
  simplex.
- `core/canonical`: the owner abstraction is the chapter Fenchel conjugate `convexConjugate` on
  `WithBotTop ℝ`-valued functions on a finite coordinate owner.
- `bridge/view`: the simplex constraint is represented by the canonical mathlib owner
  `stdSimplex ℝ ι`, and the conjugate value is stated directly by the canonical log-sum-exp
  formula `log (∑ i exp x⋆ᵢ)`.

Domain-style sampling used here:
- `convexConjugate` from Defn. 12.2;
- `stdSimplex`;
- `δ[ℝ](· | ·)` from Defintion 4.8.1 as the canonical `+∞`-outside restriction owner;
- the concrete conjugate-computation pattern of Text 12.2.4;
- the closure-free sum-conjugate owner theorem
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_common_intrinsicInterior`
  from Theorem 16.4.3.

Primitive data vs derived API:
- primitive source-facing data: the coordinate entropy sum `∑ i, ξᵢ log ξᵢ`;
- owner-derived restriction data: `δ[ℝ](· | stdSimplex ℝ ι)`;
- derived API: its pointwise Fenchel-conjugate formula.

Layer target: `source-facing`, expressed directly through `convexConjugate` and the existing
simplex owner, without introducing a surrogate package.
-/

/-- The function `ξ ↦ ∑ i ξᵢ log ξᵢ` on the standard simplex, extended by `+∞` outside the
simplex. Because `Real.log 0 = 0`, this agrees with the convention `0 log 0 = 0`. -/
def standardSimplexNegativeEntropyFunction : E → WithBotTop ℝ :=
  fun x ↦
    (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ) +
      δ[ℝ](x | stdSimplex ℝ ι)

-- Proof sketch: unfold `standardSimplexNegativeEntropyFunction` as the entropy sum plus the
-- canonical indicator `δ[ℝ](· | stdSimplex ℝ ι)`, then split on membership in the
-- simplex. On the simplex the indicator term is `0`; off the simplex it is `⊤`.
/-- Evaluating `standardSimplexNegativeEntropyFunction` gives the entropy sum on the simplex and
`+∞` away from the simplex. -/
theorem standardSimplexNegativeEntropyFunction_apply (x : E) :
    standardSimplexNegativeEntropyFunction x =
      if _hx : x ∈ stdSimplex ℝ ι then
        (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ)
      else
        ⊤ := by
  by_cases hx : x ∈ stdSimplex ℝ ι
  · simp [standardSimplexNegativeEntropyFunction, hx]
  · have htop :
      (((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ) : WithBotTop ℝ) + ⊤ = (⊤ : WithBotTop ℝ) :=
      WithBotTop.coe_add_top ((∑ i, (x i : ℝ) * Real.log (x i)) : ℝ)
    simpa [standardSimplexNegativeEntropyFunction, hx] using htop

section

variable [Nonempty ι]

-- Proof sketch: write the source function as the sum of the separable scalar function
-- `k(t) = t log t` on `t ≥ 0` with the indicator of the affine simplex constraint
-- `∑ i ξᵢ = 1`, then apply Theorem 16.4.3 to remove the closure in the conjugate-of-sum formula.
-- The scalar conjugate is `k⋆(s) = exp (s - 1)`, while the simplex indicator contributes a single
-- Lagrange multiplier `λ`; minimizing `λ + ∑ i exp (x⋆ᵢ - λ - 1)` in `λ` gives
-- `log (∑ i exp x⋆ᵢ)`.
/-- Text 16.4.4: if `f(ξ) = ∑ i ξᵢ log ξᵢ` on the standard simplex
`{ξ | ξᵢ ≥ 0, ∑ i ξᵢ = 1}` and `f(ξ) = +∞` off that simplex, then the Fenchel conjugate of `f`
is the log-sum-exp function `x⋆ ↦ log (∑ i exp x⋆ᵢ)`. -/
theorem convexConjugate_standardSimplexNegativeEntropyFunction_eq_logSumExp
    (xStar : E) :
    (standardSimplexNegativeEntropyFunction (ι := ι))⋆ xStar =
      ((Real.log (∑ i, Real.exp (xStar i)) : ℝ) : WithBotTop ℝ) := sorry

end

end
