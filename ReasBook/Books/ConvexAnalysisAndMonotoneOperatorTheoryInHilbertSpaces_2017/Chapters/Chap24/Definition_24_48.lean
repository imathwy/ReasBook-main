import Mathlib
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap24.Proposition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace

universe u

namespace Function

section ProximalThresholding

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Definition 24.48: a self-map `T : H → H` is a proximal thresholder on a nonempty closed convex
set `Ω` when `T` is the proximity operator of some `f ∈ Γ₀(H)` and the canonical zero set
`T.toSetValuedOperator.zeros` is exactly `Ω`. -/
def IsProximalThresholderOn (T : H → H) (Ω : Set H) : Prop :=
  Ω.Nonempty ∧
    ∃ (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)),
      T = Prox[f, hf] ∧ T.toSetValuedOperator.zeros = Ω

/-- A proximal thresholder on `Ω` has nonempty zero set `Ω`. -/
theorem IsProximalThresholderOn.nonempty
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    Ω.Nonempty :=
  hT.1

/-- A proximal thresholder on `Ω` admits a `Γ₀(H)` representation with zero set `Ω`. -/
theorem IsProximalThresholderOn.exists_eq_prox_and_zeros
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    ∃ (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)),
      T = Prox[f, hf] ∧ T.toSetValuedOperator.zeros = Ω :=
  hT.2

/-- A proximal thresholder on `Ω` has zero set exactly `Ω`. -/
theorem IsProximalThresholderOn.zeros_eq
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    T.toSetValuedOperator.zeros = Ω := by
  rcases hT.exists_eq_prox_and_zeros with ⟨f, hf, rfl, hzeros⟩
  exact hzeros

/-- A proximal thresholder on `Ω` has singleton preimage `T ⁻¹' {0} = Ω`. -/
theorem IsProximalThresholderOn.zero_preimage_eq
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    T ⁻¹' ({0} : Set H) = Ω := by
  rw [← hT.zeros_eq]
  ext x
  rw [Set.mem_preimage, Set.mem_singleton_iff, SetValuedOperator.mem_zeros_iff,
    Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  simp [eq_comm]

/-- A proximal thresholder on `Ω` admits a `Γ₀(H)` representation whose subdifferential at `0`
is exactly `Ω`. -/
theorem IsProximalThresholderOn.exists_eq_prox_and_subdifferential_zero_eq
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    ∃ (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)),
      T = Prox[f, hf] ∧ (∂ f) 0 = Ω := by
  rcases hT.exists_eq_prox_and_zeros with ⟨f, hf, hprox, hzeros⟩
  subst hprox
  refine ⟨f, hf, rfl, ?_⟩
  calc
    (∂ f) 0 = (Prox[f, hf]).toSetValuedOperator.zeros := by
      ext x
      rw [SetValuedOperator.mem_zeros_iff, Function.toSetValuedOperator_apply,
        Set.mem_singleton_iff]
      simpa [sub_zero, eq_comm] using
        (eq_proximityOperator_iff_sub_mem_subdifferential f hf :
          0 = Prox[f, hf] x ↔ x - 0 ∈ (∂ f) 0).symm
    _ = Ω := hzeros

/-- The zero set of a proximal thresholder is closed. -/
theorem IsProximalThresholderOn.isClosed
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    IsClosed Ω := by
  rcases hT.exists_eq_prox_and_subdifferential_zero_eq with ⟨f, hf, _, hsub⟩
  rw [← hsub]
  exact isClosed_subdifferential f 0

/-- The zero set of a proximal thresholder is convex. -/
theorem IsProximalThresholderOn.convex
    {Ω : Set H} {T : H → H} (hT : T.IsProximalThresholderOn Ω) :
    Convex ℝ Ω := by
  rcases hT.exists_eq_prox_and_subdifferential_zero_eq with ⟨f, hf, _, hsub⟩
  rw [← hsub]
  exact convex_subdifferential f 0

end ProximalThresholding

end Function
