import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Example_9_2_2_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

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
