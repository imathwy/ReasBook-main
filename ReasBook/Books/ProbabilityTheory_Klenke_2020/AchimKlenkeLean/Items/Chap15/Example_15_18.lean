import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Theorem_15_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/- Example 15.18 uses the triangular characteristic-function formula from Theorem 15.12 at
`a = π / 2`. -/
local notation "φΔ" => charFun (triangularCharacteristicMeasure (Real.pi / 2))
local notation "IΔ" => Set.Icc (-Real.pi / 2) (Real.pi / 2)

-- Proof sketch: use the canonical owner `φΔ = charFun (triangularCharacteristicMeasure (π / 2))`.
-- If `t ∈ IΔ`, use `hψ_eq`; if `t ∉ IΔ`, the owner characteristic function vanishes,
-- since `charFun_triangularCharacteristicMeasure` specializes to the tent function there.
/-- If a characteristic function agrees on `[-π / 2, π / 2]` with the triangular characteristic
function from Example 15.15 at `a = π / 2`, then their products with that characteristic function
agree everywhere. -/
theorem example1518TriangularCharFun_mul_eq_of_agreesOn
    {ψ : ℝ → ℂ}
    (hψ_eq : Set.EqOn ψ φΔ IΔ) :
    φΔ * φΔ = φΔ * ψ := sorry

-- Proof sketch: use independence to identify the characteristic functions of `X + Y` and `X + Z`
-- for the measurable random variables `X`, `Y`, and `Z` with the products `φ_X φ_Y` and
-- `φ_X φ_Z`. Rewrite these using the hypotheses
-- `φ_X = φ_Y = φΔ` and `φ_Z = ψ`, apply
-- `example1518TriangularCharFun_mul_eq_of_agreesOn`, and then use uniqueness of characteristic
-- functions for probability measures. If `Y` and `Z` were identically distributed, their pushforward
-- laws would have the same characteristic function, contradicting `hψ_ne`.
/-- Example 15.18: if `X`, `Y`, and `Z` are independent measurable real random variables with
`φ_X = φ_Y = charFun (triangularCharacteristicMeasure (π / 2))`, with `φ_Z = ψ`, and if `ψ`
agrees with this characteristic function on `[-π / 2, π / 2]` but is not equal to it, then
`X + Y` and `X + Z` are identically distributed although `Y` and `Z` are not. -/
theorem same_sum_not_identDistrib_of_triangular_charFun
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y Z : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hZ_meas : Measurable Z)
    (h_indep : iIndepFun (![X, Y, Z] : Fin 3 → Ω → ℝ) P)
    {ψ : ℝ → ℂ}
    (hψ_eq : Set.EqOn ψ φΔ IΔ)
    (hψ_ne : ψ ≠ φΔ)
    (hφX : charFun (P.map X) = φΔ)
    (hφY : charFun (P.map Y) = φΔ)
    (hφZ : charFun (P.map Z) = ψ) :
    IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X ω + Z ω) P P ∧
      ¬ IdentDistrib Y Z P P := sorry
