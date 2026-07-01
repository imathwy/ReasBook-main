import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AffineSubspace

section AffineDimension

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-- The affine dimension of an affine subspace whose direction is finite-dimensional, with the
empty affine subspace assigned dimension `-1`. -/
def AffineSubspace.affineDim (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : ℤ :=
  if s = ⊥ then -1 else Module.finrank 𝕜 s.direction

namespace AffineSubspace

/-- A point is an affine subspace of affine dimension `0`. -/
abbrev is_point (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : Prop :=
  s.affineDim = 0

/-- A line is an affine subspace of affine dimension `1`. -/
abbrev is_line (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : Prop :=
  s.affineDim = 1

/-- A plane is an affine subspace of affine dimension `2`. -/
abbrev is_plane (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : Prop :=
  s.affineDim = 2

/-- A hyperplane is a nonempty affine subspace of codimension one. -/
abbrev is_hyperplane (s : AffineSubspace 𝕜 P) : Prop :=
  s ≠ ⊥ ∧ Module.finrank 𝕜 (V ⧸ s.direction) = 1

/-- In a nontrivial finite-dimensional affine space, codimension one is equivalent to the affine
dimension equation `dim V - 1`. -/
theorem is_hyperplane_iff_affineDim_eq [FiniteDimensional 𝕜 V] [Nontrivial V]
    {s : AffineSubspace 𝕜 P} :
    s.is_hyperplane ↔ s.affineDim = (Module.finrank 𝕜 V : ℤ) - 1 := by
  constructor
  · rintro ⟨hsne, hcodim⟩
    rw [affineDim, if_neg hsne]
    have hrank :
        (Module.finrank 𝕜 (V ⧸ s.direction) : ℤ) + Module.finrank 𝕜 s.direction =
          Module.finrank 𝕜 V := by
      exact_mod_cast Submodule.finrank_quotient_add_finrank s.direction
    have hcodim' : (Module.finrank 𝕜 (V ⧸ s.direction) : ℤ) = 1 := by
      exact_mod_cast hcodim
    linarith
  · intro hs
    have hsne : s ≠ ⊥ := by
      intro hsbot
      rw [affineDim, if_pos hsbot] at hs
      have hfinrank_pos : 0 < (Module.finrank 𝕜 V : ℤ) := by
        have hfinrank_pos_nat : 0 < Module.finrank 𝕜 V := Module.finrank_pos
        exact_mod_cast hfinrank_pos_nat
      linarith
    refine ⟨hsne, ?_⟩
    rw [affineDim, if_neg hsne] at hs
    have hrank :
        (Module.finrank 𝕜 (V ⧸ s.direction) : ℤ) + Module.finrank 𝕜 s.direction =
          Module.finrank 𝕜 V := by
      exact_mod_cast Submodule.finrank_quotient_add_finrank s.direction
    have hcodim : (Module.finrank 𝕜 (V ⧸ s.direction) : ℤ) = 1 := by
      linarith
    exact_mod_cast hcodim

end AffineSubspace

end AffineDimension
