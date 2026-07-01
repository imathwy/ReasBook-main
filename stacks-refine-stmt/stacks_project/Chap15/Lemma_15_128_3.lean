import Mathlib
import stacks_project.Chap15.Situation_15_128_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open Ideal TensorProduct
open scoped ClosedPointFiber

/-
Domain-style sampling:
- primary domain: visible quotient classes `V(x)` of closed-point fibres and the Chinese remainder
  lifting used to realize prescribed visible values by a global section;
- inspected owner-style declarations:
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`,
  `Submodule.mkQ_surjective`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `Ideal.pi_tensorProductMk_quotient_surjective`,
  `Ideal.isCoprime_of_isMaximal`;
- best owner abstraction: the source-facing owner for this lemma is the chapter visible quotient
  `V(x)`, with visible classes `closedPointFiberVisibleClass x s`; the full fibre `M﹙x﹚` is only
  an internal bridge used to invoke the CRT surjectivity statement for the ideal family
  `i ↦ (pts i).1.asIdeal`;
- layer triage: `source-facing` for the prescribed visible-value theorem, `core/canonical` for the
  pairwise-coprime ideal family and quotient/tensor equivalence, `bridge/view` for the quotient
  map `M﹙x﹚ → V(x)`;
- primitive data: the finite family of closed points `pts` and the prescribed visible classes `v`;
- derived API: maximality of each closed-point ideal, the surjectivity of the simultaneous
  quotient map on fibres, and the quotient projection `M﹙x﹚ → V(x)`.
-/
local notation "Ω" => closedPoints (PrimeSpectrum R)

-- Proof sketch: choose representatives of the prescribed visible classes in the full fibres
-- `M(xᵢ)`, use the Chinese remainder theorem on the pairwise comaximal closed-point ideals to lift
-- those representatives simultaneously to a global section, and then pass to the visible
-- quotients via the canonical maps `M(xᵢ) → V(xᵢ)`.
/-- Lemma 15.128.3: for pairwise distinct closed points `x₁, ..., xₙ ∈ Ω` and prescribed visible
classes `vᵢ ∈ V(xᵢ)`, there exists a section `s : M` whose fibre image `s(xᵢ)` maps to `vᵢ` in the
visible quotient `V(xᵢ)`. -/
lemma exists_section_with_prescribed_values_at_pairwise_distinct_closed_points
    {n : ℕ} (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (v : ∀ i, V((pts i))) :
    ∃ s : M, ∀ i, closedPointFiberVisibleClass (pts i) s = v i := by
  have hcoprime : Pairwise (fun i j ↦ IsCoprime ((pts i).1.asIdeal) ((pts j).1.asIdeal)) := by
    intro i j hij
    exact isCoprime_of_isMaximal fun hEq ↦
      hpts hij <| Subtype.ext <| PrimeSpectrum.ext hEq
  classical
  have hw' : ∀ i, ∃ s : M, closedPointFiberVisibleClass (pts i) s = v i := fun i ↦
    closedPointFiberVisibleClass_surjective M (pts i) (v i)
  choose w hw using hw'
  obtain ⟨s, hs⟩ :=
    pi_tensorProductMk_quotient_surjective M
      (fun i ↦ (pts i).1.asIdeal)
      hcoprime
      (fun i ↦ (quotTensorEquivQuotSMul M ((pts i).1.asIdeal)).symm ((w i)⟮(pts i)⟯))
  refine ⟨s, fun i ↦ ?_⟩
  have hs' : s⟮(pts i)⟯ = (w i)⟮(pts i)⟯ := by
    have hs'' :=
      congrArg (quotTensorEquivQuotSMul M ((pts i).1.asIdeal)) (congrFun hs i)
    simpa [closedPointFiber] using hs''
  calc
    closedPointFiberVisibleClass (pts i) s =
        closedPointFiberVisibleClass (pts i) (w i) := by
          simpa [closedPointFiberVisibleClass] using congrArg ((B((pts i))).mkQ) hs'
    _ = v i := hw i

end
