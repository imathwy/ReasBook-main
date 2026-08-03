import Mathlib
import BauschkeLean.Chap14.Proposition_14_11
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section PositivelyHomogeneous

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.24 identifies a positively homogeneous member of `Γ₀(H)` with
  the support function of its subdifferential at `0`.
- `core/canonical`: the Chapter 14 owner theorem
  `eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero` already gives the
  support-function formula in terms of the source-defined set `linearMinorantSet f`.
- `bridge/view`: this file only identifies `linearMinorantSet f` with `(∂ f) 0` when `f 0 = 0`
  and rewrites the Chapter 14 owner theorem toward the Chapter 16 subdifferential owner. -/
/-- If `f 0 = 0`, then the subdifferential at `0` agrees with the Chapter 14 linear-minorant
set. -/
@[simp] theorem linearMinorantSet_eq_subdifferential_zero
    {f : H → Set.Ioi (⊥ : EReal)} (h0 : (f 0 : EReal) = 0) :
    linearMinorantSet f = (∂ f) 0 := by
  -- At `x = 0`, the subdifferential inequality is exactly the Chapter 14 linear-minorant
  -- inequality once the affine offset `f 0` is rewritten to `0`.
  ext u
  rw [mem_linearMinorantSet_iff, mem_subdifferential_iff]
  have h0' : CoeTC.coe (f 0) = (0 : EReal) := h0
  constructor
  · intro hu y
    rw [h0']
    simpa using hu y
  · intro hu y
    rw [h0'] at hu
    simpa using hu y

/-- Helper for Proposition 16.24: a support-function representation over a nonempty set forces the
value at the origin to be `0`. -/
theorem value_zero_eq_zero_of_eq_supportFunction_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hsupport : f.asEReal = σ[C]) (hC_nonempty : C.Nonempty) :
    (f 0 : EReal) = 0 := by
  -- Evaluate the support-function formula at the origin, where every support function over a
  -- nonempty set vanishes.
  have hvalue : (f.asEReal) 0 = σ[C] 0 := congrArg (fun g : H → EReal ↦ g 0) hsupport
  rw [show (f.asEReal) 0 = (f 0 : EReal) by rfl] at hvalue
  rw [hvalue]
  exact supportFunction_zero_eq_zero_of_nonempty C hC_nonempty

/-- Proposition 16.24: if `f ∈ Γ₀(H)` is positively homogeneous, then `f` is the support
function of its subdifferential at `0`. Equivalently, `f = σ[C]` with `C = ∂ f(0)`. -/
theorem eq_supportFunction_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) :
    f.asEReal = σ[(∂ f) 0] := by
  -- Use the Chapter 14 owner theorem to get the support-function formula with the source-defined
  -- linear-minorant set.
  obtain ⟨hsupport, _, _, _⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hph hf
  -- The source proof now needs only the zero-value fact to identify that set with `(∂ f) 0`.
  have h0 : (f 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hf
  -- Rewrite the Chapter 14 support set as the Chapter 16 subdifferential at the origin.
  simpa [linearMinorantSet_eq_subdifferential_zero h0] using hsupport

end PositivelyHomogeneous

end

end ERealFunction
