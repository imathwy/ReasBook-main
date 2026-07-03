import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable {f : ℕ → ℂ → ℂ} {D A : Set ℂ}

/-- Definition V.2-extra-1 (1): a series of meromorphic functions on an open set `D` converges
uniformly on `A ⊆ D` if, after removing finitely many initial terms, the remaining terms have no
pole on `A` and form a uniformly convergent series on `A`. -/
def meromorphic_series_uniformly_convergent_on
    (f : ℕ → ℂ → ℂ) (D A : Set ℂ) : Prop :=
  IsOpen D ∧
    A ⊆ D ∧
    (∀ n, MeromorphicOn (f n) D) ∧
    ∃ N : ℕ,
      (∀ n z, z ∈ A → AnalyticAt ℂ (f (n + N)) z) ∧
      SummableUniformlyOn (fun n ↦ f (n + N)) A

namespace meromorphic_series_uniformly_convergent_on

/-- A uniformly convergent meromorphic series is defined on an open ambient domain. -/
theorem isOpen_domain (h : meromorphic_series_uniformly_convergent_on f D A) : IsOpen D := by
  rcases h with ⟨hD, -, -, -⟩
  exact hD

/-- The set of convergence is contained in the ambient domain. -/
theorem subset_domain (h : meromorphic_series_uniformly_convergent_on f D A) : A ⊆ D := by
  rcases h with ⟨-, hA, -, -⟩
  exact hA

/-- Every term of a uniformly convergent meromorphic series is meromorphic on the ambient domain. -/
theorem meromorphic_terms
    (h : meromorphic_series_uniformly_convergent_on f D A) :
    ∀ n, MeromorphicOn (f n) D := by
  rcases h with ⟨-, -, hf, -⟩
  exact hf

/-- A uniformly convergent meromorphic series on `A` admits a tail with no poles on `A` whose
series is uniformly summable on `A`. -/
theorem exists_tail
    (h : meromorphic_series_uniformly_convergent_on f D A) :
    ∃ N : ℕ,
      (∀ n z, z ∈ A → AnalyticAt ℂ (f (n + N)) z) ∧
      SummableUniformlyOn (fun n ↦ f (n + N)) A := by
  rcases h with ⟨-, -, -, htail⟩
  exact htail

end meromorphic_series_uniformly_convergent_on

/-- Definition V.2-extra-1 (2): a series of meromorphic functions on an open set `D` converges
normally on `A ⊆ D` if, after removing finitely many initial terms, the remaining terms have no
pole on `A` and are uniformly bounded on `A` by a summable sequence of real numbers. -/
def meromorphic_series_normally_convergent_on
    (f : ℕ → ℂ → ℂ) (D A : Set ℂ) : Prop :=
  IsOpen D ∧
    A ⊆ D ∧
    (∀ n, MeromorphicOn (f n) D) ∧
    ∃ N : ℕ,
      (∀ n z, z ∈ A → AnalyticAt ℂ (f (n + N)) z) ∧
      ∃ u : ℕ → ℝ,
        Summable u ∧
        ∀ n z, z ∈ A → ‖f (n + N) z‖ ≤ u n

namespace meromorphic_series_normally_convergent_on

/-- A normally convergent meromorphic series is defined on an open ambient domain. -/
theorem isOpen_domain (h : meromorphic_series_normally_convergent_on f D A) : IsOpen D := by
  rcases h with ⟨hD, -, -, -⟩
  exact hD

/-- The set of convergence is contained in the ambient domain. -/
theorem subset_domain (h : meromorphic_series_normally_convergent_on f D A) : A ⊆ D := by
  rcases h with ⟨-, hA, -, -⟩
  exact hA

/-- Every term of a normally convergent meromorphic series is meromorphic on the ambient domain. -/
theorem meromorphic_terms
    (h : meromorphic_series_normally_convergent_on f D A) :
    ∀ n, MeromorphicOn (f n) D := by
  rcases h with ⟨-, -, hf, -⟩
  exact hf

/-- A normally convergent meromorphic series on `A` admits a pole-free tail on `A` with a summable
uniform norm bound. -/
theorem exists_bounded_tail
    (h : meromorphic_series_normally_convergent_on f D A) :
    ∃ N : ℕ,
      (∀ n z, z ∈ A → AnalyticAt ℂ (f (n + N)) z) ∧
      ∃ u : ℕ → ℝ,
        Summable u ∧
        ∀ n z, z ∈ A → ‖f (n + N) z‖ ≤ u n := by
  rcases h with ⟨-, -, -, htail⟩
  exact htail

end meromorphic_series_normally_convergent_on
