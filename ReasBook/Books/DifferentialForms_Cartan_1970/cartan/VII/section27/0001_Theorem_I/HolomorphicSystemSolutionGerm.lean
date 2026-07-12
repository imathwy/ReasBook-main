import Mathlib

open Filter
open Set
open scoped Topology

/-- A local holomorphic solution of a first-order system on an open set `U`, with graph contained
in the coefficient domain `Ω` and prescribed initial value `b` at `x₀`. -/
structure IsHolomorphicSystemSolutionOn {n : ℕ}
    (Ω : Set (ℂ × (Fin n → ℂ))) (f : ℂ → (Fin n → ℂ) → Fin n → ℂ)
    (x₀ : ℂ) (b : Fin n → ℂ) (U : Set ℂ) (φ : ℂ → Fin n → ℂ) : Prop where
  isOpen : IsOpen U
  mem : x₀ ∈ U
  analytic : AnalyticOnNhd ℂ φ U
  mapsTo : MapsTo (fun z ↦ (z, φ z)) U Ω
  initial : φ x₀ = b
  deriv_eq {z} (hz : z ∈ U) : HasDerivAt φ (f z (φ z)) z

/-- A local holomorphic solution germ of the first-order system `φ' = f (x, φ)` with initial
value `b` at `x₀`, given by an open-neighborhood representative satisfying the open-set solution
predicate. -/
def IsHolomorphicSystemSolution {n : ℕ}
    (Ω : Set (ℂ × (Fin n → ℂ))) (f : ℂ → (Fin n → ℂ) → Fin n → ℂ)
    (x₀ : ℂ) (b : Fin n → ℂ) (φ : Germ (𝓝 x₀) (Fin n → ℂ)) : Prop :=
  ∃ U : Set ℂ, ∃ ψ : ℂ → Fin n → ℂ,
    IsHolomorphicSystemSolutionOn Ω f x₀ b U ψ ∧
    (ψ : Germ (𝓝 x₀) (Fin n → ℂ)) = φ

/-- The open-set solution predicate induces the corresponding local solution germ. -/
theorem IsHolomorphicSystemSolutionOn.isHolomorphicSystemSolution {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ}
    {x₀ : ℂ} {b : Fin n → ℂ} {U : Set ℂ} {φ : ℂ → Fin n → ℂ}
    (h : IsHolomorphicSystemSolutionOn Ω f x₀ b U φ) :
    IsHolomorphicSystemSolution Ω f x₀ b (φ : Germ (𝓝 x₀) (Fin n → ℂ)) := by
  exact ⟨U, φ, h, rfl⟩
