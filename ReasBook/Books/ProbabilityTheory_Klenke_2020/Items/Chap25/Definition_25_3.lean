import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-
Definition 25.3 is `source-facing`: it defines the elementary Brownian Itô integral on the
canonical owner `PredictableSimpleProcess ℱ` from Definition 25.2. The namespace
`PredictableStepRepresentation` is only the `bridge/view` layer that records the explicit finite
increment sum for a chosen predictable-step presentation and proves that this formula depends only
on the underlying owner process.
-/

namespace PredictableStepRepresentation

variable {ℱ : ContinuousFiltration}

/-- The stopped Itô sum attached to a predictable-step representation. This is the
representation-level formula underlying Definition 25.3. -/
def brownianElementaryIntegral (H : PredictableStepRepresentation ℱ) (W : Process) : Process :=
  fun t ω ↦
    ∑ i : Fin H.n,
      H.coeff i ω *
        (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω)

/-- The terminal Itô sum attached to a predictable-step representation, obtained by evaluating
the stopped integral at the final partition time. -/
def brownianElementaryIntegralAtInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process) : Ω → ℝ :=
  PredictableStepRepresentation.brownianElementaryIntegral H W (H.times (Fin.last H.n))

/-- The stopped Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegral_congr
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegral H W =
      PredictableStepRepresentation.brownianElementaryIntegral K W := by
  sorry

/-- The terminal Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegralAtInfinity_congr
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity K W := by
  sorry

/-- Evaluating the stopped elementary Brownian integral gives the defining truncated increment
sum. -/
@[simp] theorem brownianElementaryIntegral_apply {ℱ : ContinuousFiltration}
    (H : PredictableStepRepresentation ℱ) (W : Process) (t : NNReal) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t ω =
      ∑ i : Fin H.n,
        H.coeff i ω *
          (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω) :=
  rfl

/-- Evaluating the terminal elementary Brownian integral gives the full increment sum over the
partition of `H`. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_apply
    (H : PredictableStepRepresentation ℱ) (W : Process) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W ω =
      ∑ i : Fin H.n,
        H.coeff i ω * (W (H.times i.succ) ω - W (H.times i.castSucc) ω) := by
  sorry

/- For times at or beyond the last partition point of `H`, all truncations in
`H.brownianElementaryIntegral W t` disappear, so the stopped Itô sum has stabilized at its
terminal value. -/
theorem brownianElementaryIntegral_eq_atInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process)
    {t : NNReal} (ht : H.times (Fin.last H.n) ≤ t) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W := by
  sorry

end PredictableStepRepresentation

/-- Definition 25.3: for an elementary integrand `H ∈ 𝓔` and a real process `W`, the stopped Itô
integral `brownianElementaryIntegral W H t` is obtained from a finite predictable-step
representation of `H` by the usual truncated increment sum. The representation-level formula is
recorded separately by `PredictableStepRepresentation.brownianElementaryIntegral`. -/
noncomputable def brownianElementaryIntegral {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Process :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegral representation W

/-- The terminal Itô integral `I_∞^W(H)` from Definition 25.3 for an elementary integrand
`H ∈ 𝓔`. -/
noncomputable def brownianElementaryIntegralAtInfinity {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Ω → ℝ :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W

/-- Any predictable-step representation of `H` computes the stopped Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegral_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegral W H =
      PredictableStepRepresentation.brownianElementaryIntegral representation W := by
  sorry

/-- Any predictable-step representation of `H` computes the terminal Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinity_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegralAtInfinity W H =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W := by
  sorry

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level stopped increment sum. -/
@[simp] theorem brownianElementaryIntegral_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegral W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegral representation W :=
  brownianElementaryIntegral_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level terminal increment sum. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegralAtInfinity W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W :=
  brownianElementaryIntegralAtInfinity_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

end MeasureTheory

end
