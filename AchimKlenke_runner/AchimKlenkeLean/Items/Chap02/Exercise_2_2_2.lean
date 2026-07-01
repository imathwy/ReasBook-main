import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → ℝ}

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The Box-Muller map sends a pair of real parameters `(u, v)` to the corresponding pair of
Gaussian coordinates. -/
noncomputable
def boxMullerPair (u v : ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v),
    Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v))

variable (hU : HasLaw U unitIntervalVolume P)
variable (hV : HasLaw V unitIntervalVolume P)
variable (hUV : U ⟂ᵢ[P] V)

-- Proof sketch: compute the law of the radius `R = sqrt (-2 log U)` from the uniform law of `U`,
-- combine it with the uniform angular variable `2πV`, and apply the transformation formula in
-- polar coordinates to identify the pushforward measure with the product of two standard Gaussian
-- laws.
/-- Exercise 2.2.2: If `U` and `V` are independent and both uniformly distributed on `[0,1]`,
then the Box-Muller transform has joint law equal to the product of two standard Gaussian laws. -/
theorem boxMullerPair_hasLaw
    :
    HasLaw (fun ω ↦ boxMullerPair (U ω) (V ω))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) P := sorry

-- Proof sketch: rewrite independence in terms of the pushforward law of the pair
-- `(boxMullerPair (U ω) (V ω)).1, (boxMullerPair (U ω) (V ω)).2`, then use
-- `boxMullerPair_hasLaw` to identify this law with the product of the two marginal Gaussian laws.
/-- The two coordinates produced by the Box-Muller transform are independent. -/
theorem boxMuller_fst_indepFun_snd
    :
    (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) ⟂ᵢ[P]
      (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) := sorry

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the first-coordinate
-- projection and use that the first marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The first Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_fst_hasLaw
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) (gaussianReal 0 1) P := sorry

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the second-coordinate
-- projection and use that the second marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The second Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_snd_hasLaw
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) (gaussianReal 0 1) P := sorry
