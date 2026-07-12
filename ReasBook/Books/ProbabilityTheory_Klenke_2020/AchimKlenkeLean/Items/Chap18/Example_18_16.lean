import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- An Ising spin is a sign that is constrained to take only the values `-1` and `1`. -/
abbrev ising_spin : Type :=
  { s : SignType // s ≠ 0 }

/-- An Ising configuration assigns a spin to every site of the finite lattice `Λ`. -/
abbrev ising_configuration (Λ : Type u) : Type u :=
  Λ → ising_spin

-- Proof sketch: `σ.1` is a nonzero sign, and negation on `SignType` preserves nonzeroness on the
-- two-point subset `{ -1, 1 }`.
private theorem ising_spin_neg_ne_zero (σ : ising_spin) : (-σ.1 : SignType) ≠ 0 := sorry

/-- Reversing an Ising spin exchanges `1` and `-1`. -/
def flip_spin (σ : ising_spin) : ising_spin :=
  ⟨-σ.1, ising_spin_neg_ne_zero σ⟩

/-- The configuration obtained from `x` by reversing the spin at the site `i`. -/
def flip_at (x : ising_configuration Λ) (i : Λ) : ising_configuration Λ :=
  Function.update x i (flip_spin (x i))

variable (G : SimpleGraph Λ) [DecidableRel G.Adj]

/-- The local Ising energy at the site `i` is half the number of neighboring spins that disagree
with the spin at `i`. -/
def local_energy (x : ising_configuration Λ) (i : Λ) : ℝ :=
  ∑ j, if G.Adj i j ∧ x i ≠ x j then (1 / 2 : ℝ) else 0

/-- The Hamiltonian of a finite Ising configuration is the sum of all local energies. -/
def hamiltonian (x : ising_configuration Λ) : ℝ :=
  ∑ i, local_energy G x i

/-- The unnormalized Boltzmann weight of the Ising configuration `x` at inverse temperature `β`. -/
def ising_boltzmann_weight (β : ℝ) (x : ising_configuration Λ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * hamiltonian G x))

variable [Nonempty Λ]

/-- The single-spin-flip proposal matrix chooses a site uniformly and proposes the configuration
obtained by reversing the spin at that site. -/
def ising_proposal_matrix (x y : ising_configuration Λ) : ℝ≥0∞ :=
  ∑ i, if y = flip_at x i then (Fintype.card Λ : ℝ≥0∞)⁻¹ else 0

section Metropolis

variable (β : ℝ)

/- Example 18.16: the finite Ising-model Metropolis matrix is the specialization of the general
Metropolis matrix to the single-spin-flip proposal and the Boltzmann weight
`x ↦ exp (-β H(x))`. -/
#check (metropolisMatrix (ising_boltzmann_weight G β) ising_proposal_matrix :
  ising_configuration Λ → ising_configuration Λ → ℝ≥0∞)

end Metropolis

-- Proof sketch: only the energy contributions involving the flipped site and its neighbors change;
-- expanding those local terms yields the stated signed sum over neighboring disagreements.
/-- Flipping the spin at a site changes the Hamiltonian by the signed sum over its neighboring
disagreements. -/
theorem hamiltonian_flip_difference_eq
    (x : ising_configuration Λ) (i : Λ) :
    hamiltonian G (flip_at x i) - hamiltonian G x =
      -2 *
        ∑ j, if G.Adj j i then (if x j ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ) else 0 := sorry

end ProbabilityTheory
