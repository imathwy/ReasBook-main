import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_62 (from Items/Chap21) -/
open MeasureTheory

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/- Remark 21.62 splits into:
* the `core/canonical` owner-level closure statement that `𝒞_qv` is stable under `C¹`
  composition;
* a `bridge/view` witness-level Stieltjes formula for a chosen continuous square-variation path.

Domain-style sampling:
* `HasSquareVariationAlong` is the witness-level dyadic square-variation predicate from
  Definition 21.58.
* `HasContinuousSquareVariation` is the owner property for continuous paths with continuous square
  variation.
* `𝒞_qv` is the source-facing set-level view of that owner property.

Primitive data versus derived API:
* primitive data: the path `G` and the owner hypothesis `HasContinuousSquareVariation G`;
* derived API: closure under `C¹` composition, the set-level `𝒞_qv` bridge, and the chosen
  Stieltjes-measure identity for a particular continuous square-variation realization `VG`. -/

variable {G VG : PathSpace}

-- Proof sketch: choose a continuous square-variation path `VG` for `G`; Remark 21.62 identifies
-- the square variation of `f ∘ G` with the continuous increasing path obtained by integrating
-- `(f'(G_s))²` against `d⟨G⟩_s`, which in particular yields a continuous square-variation
-- realization of `f ∘ G`.
/-- Remark 21.62: if `f ∈ C¹(ℝ)` and `G` has continuous square variation along the dyadic
partitions, then the composed path `t ↦ f (G t)` again has continuous square variation. -/
theorem hasContinuousSquareVariation_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hG : HasContinuousSquareVariation G) :
    HasContinuousSquareVariation ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) := sorry

-- Proof sketch: this is the owner-level closure theorem above, rewritten through the source-facing
-- identification `𝒞_qv = {G | HasContinuousSquareVariation G}` from Definition 21.58.
/-- Source-facing `𝒞_qv` form of Remark 21.62. -/
theorem mem_𝒞_qv_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hG : G ∈ 𝒞_qv) :
    ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) ∈ 𝒞_qv := by
  simpa [mem_𝒞_qv_iff] using
    hasContinuousSquareVariation_comp f hf ((mem_𝒞_qv_iff G).1 hG)

-- Proof sketch: with a chosen continuous square-variation path `VG = ⟨G⟩` and a chosen
-- Stieltjes-measure realization `μG` of `VG`, the chain rule identifies the square variation of
-- `f ∘ G` with the path `T ↦ ∫_[0,T] (f'(G_s))² dμG(s)`. The theorem records this as an
-- existential witness statement, leaving the owner-level closure theorem as the main public entry.
/-- Witness-level bridge for Remark 21.62: if `VG` is a chosen continuous square-variation path of
`G` and `μG` is a Stieltjes-measure realization of `VG`, then `f ∘ G` admits a continuous square-
variation path whose value at time `T` is `∫_[0,T] (f'(G_s))² dμG(s)`. -/
theorem exists_squareVariation_comp_eq_lebesgueStieltjesIntegral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hVG : HasSquareVariationAlong G VG)
    (μG : Measure NNReal)
    (hμG :
      ∀ T : NNReal,
        VG T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μG) :
    ∃ VfG : PathSpace,
      HasSquareVariationAlong ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) VfG ∧
        ∀ T : NNReal,
          VfG T = ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂μG := sorry
