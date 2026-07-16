import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.SymmetricExterior
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.BaseChangeAndExteriorBasics

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

-- `SymmetricPower R ι M` (and hence `nthSymmetricPower`, indexed by `Fin n : Type 0`) forces the
-- base field `k` and the index type to share a universe, so we pin `k : Type 0`.  Every consumer of
-- this file instantiates `k` at `Type 0` (e.g. `AlgebraicClosure (ZMod p)`), so no generality is
-- lost.
variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- Source/core/bridge triage:
-- * source-facing: the generating series `σ_T(ρ)` and `λ_T(ρ)` together with their Chapter 9
--   determinant identities.
-- * core/canonical: `Representation.nthSymmetricPower`, `Representation.nthExteriorPower`, and
--   the canonical character owner `Representation.character`.
-- * bridge/view: `PowerSeries.map (Pi.evalRingHom _ s)` and `PowerSeries.exp`/`subst`, which
--   connect the source-facing series to determinant and Adams-operator formulas.

-- `SymmetricPower R ι M` (and hence `nthSymmetricPower`, indexed by `Fin n : Type 0`) forces the
-- base field `k` and the index type to share a universe, so we pin `k : Type 0`.  Every consumer of
-- this file instantiates `k` at `Type 0` (e.g. `AlgebraicClosure (ZMod p)`), so no generality is
-- lost.
variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The generating series `σ_T(χ) = ∑ χ_σ^n T^n` of symmetric-power characters. -/
def symmetricPowerCharacterSeries (ρ : Representation k G V) : PowerSeries (G → k) :=
  PowerSeries.mk fun n ↦ (ρ.nthSymmetricPower n).character

scoped notation:max "σ_T(" ρ ")" => symmetricPowerCharacterSeries ρ

omit [FiniteDimensional k V] in
@[simp] theorem coeff_symmetricPowerCharacterSeries (ρ : Representation k G V) (n : ℕ) :
    PowerSeries.coeff n σ_T(ρ) = (ρ.nthSymmetricPower n).character := by
  simp [symmetricPowerCharacterSeries]

/-- The generating series `λ_T(χ) = ∑ χ_λ^n T^n` of exterior-power characters. -/
def exteriorPowerCharacterSeries (ρ : Representation k G V) : PowerSeries (G → k) :=
  PowerSeries.mk fun n ↦ (ρ.nthExteriorPower n).character

scoped notation:max "λ_T(" ρ ")" => exteriorPowerCharacterSeries ρ

omit [FiniteDimensional k V] in
@[simp] theorem coeff_exteriorPowerCharacterSeries (ρ : Representation k G V) (n : ℕ) :
    PowerSeries.coeff n λ_T(ρ) = (ρ.nthExteriorPower n).character := by
  simp [exteriorPowerCharacterSeries]

/-- Helper for Exercise 9-9.1-3: after evaluating at `s`, the coefficient of the symmetric-power
series is the trace of the induced endomorphism on the `n`th symmetric power of `V`. -/
theorem coeff_map_symmetricPowerCharacterSeries_eval
    (ρ : Representation k G V) (s : G) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ)) =
      LinearMap.trace k (SymmetricPower k (Fin n) V) (SymmetricPower.map n (ρ s)) := by
  -- Unfold the coefficient of the generating series, then rewrite the character as a trace.
  rw [PowerSeries.coeff_map, coeff_symmetricPowerCharacterSeries]
  simp [Representation.character, Representation.nthSymmetricPower]

/-- Helper for Exercise 9-9.1-3: after evaluating at `s`, the coefficient of the exterior-power
series is the trace of the induced endomorphism on the `n`th exterior power of `V`. -/
theorem coeff_map_exteriorPowerCharacterSeries_eval
    (ρ : Representation k G V) (s : G) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ)) =
      LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (ρ s)) := by
  -- The exterior case is the same coefficient-to-character reduction, with the exterior-power
  -- representation in place of the symmetric one.
  rw [PowerSeries.coeff_map, coeff_exteriorPowerCharacterSeries]
  simp [Representation.character, Representation.nthExteriorPower]

end

end Representation
