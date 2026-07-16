import DifferentialForms_Cartan_1970.cartan.VII.section27.«0003_Definition_VII_1_extra_1»
import Mathlib

open scoped BigOperators MvPowerSeries PowerSeries
open PowerSeries

universe u

section FormalRecursiveImplicitSystem

variable {𝕜 : Type u} [CommRing 𝕜]
variable {n p : ℕ}

/-- The parameter variables `(y, z)` occurring in the formal solution series `(4)`. -/
abbrev ParamIndex (n p : ℕ) := Fin n ⊕ Fin p

/-- The variables `(x, y, z)` occurring in the recursive system `(3)`. -/
abbrev SystemIndex (n p : ℕ) := Fin n ⊕ ParamIndex n p

/-- The total `x`-degree of a monomial in the nonlinear remainder variables `(x, z)`. -/
def xDegree (d : (Fin n ⊕ Fin p) →₀ ℕ) : ℕ :=
  ∑ j : Fin n, d (Sum.inl j)

/-- The total `(y, z)`-degree of a monomial in the formal solution series `(4)`. -/
def paramDegree (d : ParamIndex n p →₀ ℕ) : ℕ :=
  ∑ u : ParamIndex n p, d u

/-- The coefficient variables used to encode the polynomial recursion for the coefficients of a
formal solution: the left summands index the primitive coefficients of the recursive system `(3)`,
while the right summands index lower-order coefficients of the candidate solution `(4)`. -/
abbrev SystemCoeffVar (n p : ℕ) :=
  (Fin n × Fin n × (Fin p →₀ ℕ)) ⊕ (Fin n × ((Fin n ⊕ Fin p) →₀ ℕ))

/-- The coefficient variables used to encode the polynomial recursion for the coefficients of a
formal solution. -/
abbrev RecursiveCoeffVar (n p : ℕ) :=
  SystemCoeffVar n p ⊕ (Fin n × (ParamIndex n p →₀ ℕ))

/-- A recursive implicit system of the form `(3)`: linear in the `y`-variables with `z`-series
coefficients, and with nonlinear remainder of `x`-degree at least `2`. -/
structure RecursiveImplicitSystem (𝕜 : Type u) [CommRing 𝕜] (n p : ℕ) where
  linearCoeff : Fin n → Fin n → MvPowerSeries (Fin p) 𝕜
  higher : Fin n → MvPowerSeries (Fin n ⊕ Fin p) 𝕜
  higher_xDegree_ge_two (j : Fin n) (d : (Fin n ⊕ Fin p) →₀ ℕ) (hd : xDegree d ≤ 1) :
    MvPowerSeries.coeff d (higher j) = 0

/-- Embed the `z`-variables into the full recursive-system variables `(x, y, z)`. -/
def zToSystem : Fin p → SystemIndex n p :=
  Sum.inr ∘ Sum.inr

/-- Embed the nonlinear-remainder variables `(x, z)` into the full recursive-system variables
`(x, y, z)`. -/
def higherToSystem : Fin n ⊕ Fin p → SystemIndex n p :=
  Sum.elim Sum.inl zToSystem

/-- The right-hand side family `x ↦ Γ(z) y + H(x, z)` associated to a recursive implicit system. -/
noncomputable def RecursiveImplicitSystem.toSeries
    (S : RecursiveImplicitSystem 𝕜 n p) :
    Fin n → MvPowerSeries (SystemIndex n p) 𝕜 :=
  fun j ↦
    (∑ i : Fin n,
        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
          MvPowerSeries.X (Sum.inr (Sum.inl i))) +
      MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j)

/-- The right-hand side family `x ↦ Γ(z) y + H(x, z)` attached to a recursive implicit system. -/
noncomputable instance : CoeFun (RecursiveImplicitSystem 𝕜 n p)
    (fun _ ↦ Fin n → MvPowerSeries (SystemIndex n p) 𝕜) where
  coe := RecursiveImplicitSystem.toSeries

/-- Substitute a candidate formal solution `x(y, z)` for the placeholder variables `x` in `(3)`,
while keeping the parameter variables `(y, z)` fixed. -/
noncomputable def solutionSubst
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    SystemIndex n p → MvPowerSeries (ParamIndex n p) 𝕜 :=
  Sum.elim x MvPowerSeries.X

/-- The substitution attached to a formal candidate solution is admissible as soon as all its
constant coefficients vanish. -/
theorem solutionSubst_hasSubst
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) :
    MvPowerSeries.HasSubst (solutionSubst x) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | u)
  · exact hx j
  · simp [solutionSubst]

/-- A family of formal series `x₁, ..., xₙ` solving the recursive system `(3)`. -/
structure FormalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) : Prop where
  constantCoeff_eq_zero (j : Fin n) : MvPowerSeries.constantCoeff (x j) = 0
  eq_subst (j : Fin n) : x j = MvPowerSeries.subst (solutionSubst x) (S j)

namespace FormalImplicitSolution

/-- A formal solution yields the admissible substitution needed to evaluate the recursive system on
that solution. This is derived from the vanishing constant coefficients and the finiteness of the
variable set. -/
theorem hasSubst
    {S : RecursiveImplicitSystem 𝕜 n p}
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (h : FormalImplicitSolution S x) :
    MvPowerSeries.HasSubst (solutionSubst x) :=
  solutionSubst_hasSubst x h.constantCoeff_eq_zero

end FormalImplicitSolution

/-- Evaluate the coefficient variables for the system coefficients and the coefficients of a
candidate formal solution. -/
noncomputable def recursiveCoeffAssignment
    (S : RecursiveImplicitSystem 𝕜 n p)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    RecursiveCoeffVar n p → 𝕜
  | Sum.inl (Sum.inl ⟨j, i, d⟩) => MvPowerSeries.coeff d (S.linearCoeff j i)
  | Sum.inl (Sum.inr ⟨j, d⟩) => MvPowerSeries.coeff d (S.higher j)
  | Sum.inr ⟨j, d⟩ => MvPowerSeries.coeff d (x j)

/-- A candidate formal solution satisfies the coefficient recursion encoded by a polynomial family
`Q`. -/
structure RecursiveCoefficientRecurrence
    (S : RecursiveImplicitSystem 𝕜 n p)
    (Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ)
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) : Prop where
  constantCoeff_eq_zero (j : Fin n) : MvPowerSeries.constantCoeff (x j) = 0
  coeff_eq_eval (j : Fin n) (d : ParamIndex n p →₀ ℕ) (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d (x j) =
      MvPolynomial.eval₂ (Int.castRingHom 𝕜)
        (recursiveCoeffAssignment S x) (Q j d)

end FormalRecursiveImplicitSystem
