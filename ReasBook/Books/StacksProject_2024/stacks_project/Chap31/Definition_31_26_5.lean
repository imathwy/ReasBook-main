import Mathlib
import StacksProject_2024.Chap31.Definition_31_26_2
import StacksProject_2024.Chap31.Definition_31_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

-- Semantic recall: `lean_leansearch` surfaced only analytic meromorphic-divisor owners, while
-- local Chapter 31 provides the scheme-side owners `PrimeDivisor`, `WeilDivisor`, and
-- `Scheme.primeDivisorOrder`. The principal divisor is therefore exposed first by its explicit
-- coefficient function; the locally-finite support condition is kept as the proof-side statement
-- supplied by Lemma 31.26.4.

/-- The generic-point stalks along prime divisors of `X` are discrete valuation rings. This is the
ambient hypothesis used by the Chapter 31 principal-divisor owners. -/
class PrimeDivisorDiscreteValuationRings : Prop where
  /-- The stalk at the generic point of each prime divisor is a discrete valuation ring. -/
  isDiscreteValuationRing (Z : PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)

/-- The DVR hypothesis needed to form principal Weil divisors. -/
abbrev primeDivisorDiscreteValuationRing [h : PrimeDivisorDiscreteValuationRings X]
    (Z : PrimeDivisor X) :
    IsDiscreteValuationRing Z.genericPointStalk :=
  h.isDiscreteValuationRing Z

/-- Under the Chapter 31 DVR hypothesis, the generic-point stalk of each prime divisor is a DVR. -/
instance instIsDiscreteValuationRingGenericPointStalk (Z : PrimeDivisor X)
    [PrimeDivisorDiscreteValuationRings X] :
    IsDiscreteValuationRing Z.genericPointStalk :=
  primeDivisorDiscreteValuationRing X Z

/-- Definition 31.26.5: let `X` be a locally Noetherian integral scheme and let
`f ∈ R(X)ˣ`. Given the generic-point DVR hypotheses required by the current Chapter 31 order
owner, the principal Weil divisor associated to `f` has coefficient
`\operatorname{ord}_Z(f)` at each prime divisor `Z`; this is the order of vanishing in the
generic-point stalk of `Z`. -/
@[stacks 0BE3]
def principalWeilDivisorCoeff
    (hDVR :
      ∀ Z : PrimeDivisor X,
        IsDiscreteValuationRing Z.genericPointStalk)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) : ℤ :=
  letI := hDVR Z
  X.primeDivisorOrder Z f

/-- The coefficient formula for the principal Weil divisor associated to a function-field unit. -/
theorem principalWeilDivisorCoeff_def
    (hDVR :
      ∀ Z : PrimeDivisor X,
        IsDiscreteValuationRing Z.genericPointStalk)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalWeilDivisorCoeff X hDVR f Z =
      letI := hDVR Z
      X.primeDivisorOrder Z f :=
  rfl

/-- The nonzero coefficients of the principal Weil divisor associated to a function-field unit are
locally finite, so the coefficient function determines a Weil divisor on `X`. -/
theorem locallyFinite_principalWeilDivisorCoeff_ne_zero
    (hDVR :
      ∀ Z : PrimeDivisor X,
        IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint))
    (f : X.functionFieldˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if principalWeilDivisorCoeff X hDVR f Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- The principal Weil divisor associated to a function-field unit. -/
noncomputable def principalWeilDivisor
    [PrimeDivisorDiscreteValuationRings X] (f : X.functionFieldˣ) : Div(X) where
  coeff := principalWeilDivisorCoeff X (primeDivisorDiscreteValuationRing X) f
  locallyFinite_nonzeroCoefficients := by
    simpa using
      locallyFinite_principalWeilDivisorCoeff_ne_zero X
        (primeDivisorDiscreteValuationRing X) f

@[simp] theorem principalWeilDivisor_coeff
    [PrimeDivisorDiscreteValuationRings X] (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    (principalWeilDivisor X f).coeff Z =
      principalWeilDivisorCoeff X (primeDivisorDiscreteValuationRing X) f Z :=
  rfl

end AlgebraicGeometry.Scheme
