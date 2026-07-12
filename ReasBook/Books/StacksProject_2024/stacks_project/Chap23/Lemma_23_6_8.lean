import Mathlib.LinearAlgebra.DirectSum.Finsupp
import StacksProject_2024.Chap23.Definition_23_6_5

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uA uB

open DifferentialGradedAlgebra

section

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/- Source/core/bridge triage:
- `source-facing`: Lemma 23.6.8 itself, in its odd-variable and even-variable forms.
- `core/canonical`: the differential/divided-power compatibility owner
  `DifferentialGradedAlgebra.CompatibleDividedPowers` from Definition 23.6.5.
- `bridge/view`: Examples 23.6.2 and 23.6.3 already own the canonical adjoin-variable grading and
  divided-power APIs. The theorem headers below therefore expose only the extra ring-level
  realization data needed for a chosen `R`-algebra `B`; they do not introduce a second public
  owner for the odd/even adjoin-variable objects or their divided powers.
-/

/-- A derivation on a chosen `R`-algebra realization `B` of `A⟨T⟩` is admissible for
Lemma 23.6.8 when it extends the base differential, sends the adjoined variable to the prescribed
closed element, lowers degree by one, squares to zero, and is compatible with the chosen divided
powers on `B` in the sense of Definition 23.6.5. -/
def IsAdjoinVariableDifferential
    (gradingB : ℕ → Submodule R B) (dA : Derivation R A A) (gammaB : ℕ → B → B)
    (includeBase : A →ₐ[R] B) (variableT : B) (closedElement : A)
    (D : Derivation R B B) : Prop :=
  (∀ a : A, D (includeBase a) = includeBase (dA a)) ∧
    D variableT = includeBase closedElement ∧
    (∀ ⦃n : ℕ⦄ ⦃x : B⦄, x ∈ gradingB n → D x ∈ gradingB (n - 1)) ∧
    (∀ x : B, D (D x) = 0) ∧
    CompatibleDividedPowers gradingB D gammaB

namespace IsAdjoinVariableDifferential

variable {gradingB : ℕ → Submodule R B} {dA : Derivation R A A} {gammaB : ℕ → B → B}
variable {includeBase : A →ₐ[R] B} {variableT : B} {closedElement : A}
variable {D : Derivation R B B}

/-- An admissible differential extends the base differential along `A → A⟨T⟩`. -/
theorem comm_includeBase
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT closedElement D)
    (a : A) :
    D (includeBase a) = includeBase (dA a) :=
  hD.1 a

/-- An admissible differential sends the adjoined variable to the prescribed closed element. -/
theorem map_variableT
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT closedElement D) :
    D variableT = includeBase closedElement :=
  hD.2.1

/-- An admissible differential lowers homogeneous degree by one. -/
theorem map_mem_grading_pred
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT closedElement D)
    {n : ℕ} {x : B} (hx : x ∈ gradingB n) :
    D x ∈ gradingB (n - 1) :=
  hD.2.2.1 hx

/-- An admissible differential squares to zero. -/
theorem sq_eq_zero
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT closedElement D)
    (x : B) :
    D (D x) = 0 :=
  hD.2.2.2.1 x

/-- An admissible differential is compatible with the chosen divided powers on `A⟨T⟩`. -/
theorem compatibleDividedPowers
    (hD : IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT closedElement D) :
    CompatibleDividedPowers gradingB D gammaB :=
  hD.2.2.2.2

end IsAdjoinVariableDifferential

/-- Lemma 23.6.8, odd-variable case: let `(A, d, γ)` be as in Definition 23.6.5, let `B` be an
odd-variable extension `A⟨T⟩` as in Example 23.6.2 with `deg(T) = d` and `d` odd, and let
`f ∈ A_{d - 1}` satisfy `d(f) = 0`. Then there exists a unique differential on `B` extending
`d`, sending `T` to `f`, and compatible with the divided powers on `B`. Since `d : ℕ` is odd, the
source positivity condition `0 < d` is automatic and is not repeated as a separate hypothesis.

The odd-variable grading and divided-power formulas are owned canonically by
`ParitySplitGradedAlgebra.adjoinOddVariableGrading` and
`DividedPowerStructure.IsAdjoinOddVariableDividedPower`; the hypotheses below record only the
extra realization data on the chosen ring `B`, restricted to the positive even part where the
source odd-variable divided powers are defined. -/
@[stacks 09PM]
theorem existsUniqueAdjoinOddVariableDifferential
    (gradingA : ℕ → Submodule R A) (gradingB : ℕ → Submodule R B)
    (dA : Derivation R A A) (gammaA : ℕ → A → A) (gammaB : ℕ → B → B)
    (includeBase : A →ₐ[R] B) (variableT : B) (d : ℕ)
    (hdOdd : Odd d)
    (hincludeBase_mem :
      ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ gradingA n → includeBase x ∈ gradingB n)
    (hvariable_mem : variableT ∈ gradingB d)
    (hvariable_sq : variableT * variableT = 0)
    (hgrading :
      ∀ m : ℕ, gradingB m ≃ₗ[R] (gradingA m × gradingA (m - d)))
    [CompatibleDividedPowers gradingA dA gammaA]
    (hgamma_zero : ∀ z : evenPositivePart gradingB, gammaB 0 z = 1)
    (hgamma_succ :
      ∀ (n : ℕ) (m : ℕ+) (x : gradingA (2 * (m : ℕ))) (y : gradingA (2 * (m : ℕ) - d)),
        gammaB (n + 1) ((hgrading (2 * (m : ℕ))).symm (x, y)) =
          includeBase (gammaA (n + 1) x) + includeBase (gammaA n x * y) * variableT)
    (f : A) (hf : f ∈ gradingA (d - 1)) (hdf : dA f = 0) :
    ∃! D : Derivation R B B,
      IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT f D := sorry

/-- Lemma 23.6.8, even-variable case: let `(A, d, γ)` be as in Definition 23.6.5, let `B` be an
even-variable extension `A⟨T⟩` as in Example 23.6.3 with `deg(T) = d > 0`, and let
`f ∈ A_{d - 1}` satisfy `d(f) = 0`. Then there exists a unique differential on `B` extending
`d`, sending `T` to `f`, and compatible with the divided powers on `B`.

The even-variable grading and divided-power formulas are owned canonically by
`ParitySplitGradedAlgebra.adjoinEvenVariableGrading`,
`ParitySplitGradedAlgebra.AdjoinEvenVariableDividedPowerStructure`, and
`DividedPowerStructure.IsAdjoinEvenVariableDividedPower`; the hypotheses below record only the
extra realization data on the chosen ring `B`, restricted to the embedded positive even part of
`A` and the positive divided-power monomials `T^(i)`. -/
@[stacks 09PM]
theorem existsUniqueAdjoinEvenVariableDifferential
    (gradingA : ℕ → Submodule R A) (gradingB : ℕ → Submodule R B)
    (dA : Derivation R A A) (gammaA : ℕ → A → A) (gammaB : ℕ → B → B)
    (includeBase : A →ₐ[R] B) (variableT : B) (d : ℕ)
    (hd : 0 < d) (hdEven : Even d)
    (hincludeBase_mem :
      ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ gradingA n → includeBase x ∈ gradingB n)
    (hvariable_mem : variableT ∈ gradingB d)
    (tDividedPower : ℕ → B)
    (htDividedPower_zero : tDividedPower 0 = 1)
    (htDividedPower_one : tDividedPower 1 = variableT)
    (htDividedPower_mem : ∀ i : ℕ, tDividedPower i ∈ gradingB (i * d))
    (hgrading :
      ∀ m : ℕ, gradingB m ≃ₗ[R] (Π₀ i : ℕ, gradingA (m - i * d)))
    [CompatibleDividedPowers gradingA dA gammaA]
    (hgamma_includeBase :
      ∀ (n : ℕ) (a : evenPositivePart gradingA),
        gammaB n (includeBase a) = includeBase (gammaA n a))
    (hgamma_tDividedPower :
      ∀ (n : ℕ) (i : ℕ+), gammaB n (tDividedPower i) = tDividedPower (n * (i : ℕ)))
    (f : A) (hf : f ∈ gradingA (d - 1)) (hdf : dA f = 0) :
    ∃! D : Derivation R B B,
      IsAdjoinVariableDifferential gradingB dA gammaB includeBase variableT f D := sorry

end
