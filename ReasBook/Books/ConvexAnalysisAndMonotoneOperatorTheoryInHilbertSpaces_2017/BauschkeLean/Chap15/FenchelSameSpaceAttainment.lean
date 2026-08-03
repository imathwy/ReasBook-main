import Mathlib
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap15.Definition_15_10

-- Declarations for shared same-space Fenchel attainment helpers.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: this module isolates the same-space Fenchel-attainment owner behind the
  textbook regularity hypothesis `0 ∈ sri (effectiveDomain f - effectiveDomain g)`.
- `core/canonical`: the owner objects are `fenchelDualObjective`, `primalOptimalValue`,
  `Argmin`, and the zero-slice value of `f^* □ g^*`.
- `bridge/view`: downstream files should consume the shared owner theorem here instead of pulling
  the later composite-duality development into the Chapter 15 same-space chain.
-/

/-- Helper for Proposition 15 13 and Theorem 15 23: the zero slice of `f^* □ g^*` is the infimum
of the Fenchel dual objective `u ↦ f^*(-u) + g^*(u)`. -/
lemma sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero_shared
    (f g : H → Set.Ioi (⊥ : EReal)) :
    sInf (Set.range (fenchelDualObjective f g)) =
      (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
  -- Rewrite the range infimum as an indexed infimum of the dual objective.
  rw [sInf_range, infimalConvolution_apply]
  calc
    (⨅ u : H, fenchelDualObjective f g u) =
        ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (-y) := by
          -- Reindex the dual variable by the involution `u = -y`.
          exact (Equiv.neg H).iInf_congr fun y ↦ by
            simp [fenchelDualObjective_apply]
    _ = ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (0 - y) := by
          -- Normalize the infimal-convolution slice at the origin.
          refine iInf_congr fun y ↦ ?_
          simp

/-- Helper for Proposition 15 13 and Theorem 15 23: an exact zero slice of `f^* □ g^*` already
produces a minimizing Fenchel dual vector after the sign normalization `u = -y`. -/
lemma argmin_fenchelDualObjective_of_exactAt_zero_shared
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H))
    (hexact0 :
      infimalConvolution.ExactAt
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (0 : H)) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      (f.asEReal∗ □ g.asEReal∗) (0 : H) = fenchelDualObjective f g u := by
  rcases hexact0 with ⟨y, hy⟩
  refine ⟨-y, ?_, ?_⟩
  · -- The exact zero-slice equality identifies `u = -y` with the infimum of the dual range.
    rw [mem_argmin_iff_eq_sInf]
    calc
      fenchelDualObjective f g (-y) = (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
        simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy.symm
      _ = sInf (Set.range (fenchelDualObjective f g)) := by
        symm
        exact
          sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero_shared
            (f := f) (g := g)
  · -- Reuse the same sign-normalized zero-slice equality for the downstream value identity.
    simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy

/-- Helper for Proposition 15 13 and Theorem 15 23: evaluating the conjugate of the primal
pointwise sum at the origin rewrites it as the negative primal optimal value. -/
lemma pointwiseAdd_conjugate_zero_eq_neg_primalOptimalValue_shared
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f + g).asEReal∗ (0 : H) = -primalOptimalValue f g := by
  -- At the origin, the primal sum conjugate is the negative infimum of the primal objective.
  rw [conjugate_zero_eq_neg_iInf]
  simp [primalOptimalValue_eq_iInf_primalObjective]

/-- Helper for Proposition 15 13 and Theorem 15 23: once the zero slice of `f^* □ g^*` is known
to equal `- primalOptimalValue f g`, exactness at `0` already yields an attained Fenchel dual
vector with the source-facing value identity. -/
lemma exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_slice_shared
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H))
    (hexact0 :
      infimalConvolution.ExactAt
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (0 : H))
    (hzero :
      (f.asEReal∗ □ g.asEReal∗) (0 : H) = -primalOptimalValue f g) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      primalOptimalValue f g = -(fenchelDualObjective f g u) := by
  -- First extract the minimizing dual vector from exactness at the zero slice.
  obtain ⟨u, huArg, huValue⟩ :=
    argmin_fenchelDualObjective_of_exactAt_zero_shared f hf g hg hexact0
  refine ⟨u, huArg, ?_⟩
  -- Then rewrite the zero-slice value through `hzero` and the attained equality `huValue`.
  calc
    primalOptimalValue f g = -((f.asEReal∗ □ g.asEReal∗) (0 : H)) := by
      rw [hzero]
      simp
    _ = -(fenchelDualObjective f g u) := by rw [huValue]

/-- Shared owner for Proposition 15 13 and Theorem 15 23: under the same-space Attouch--Brézis
regularity hypothesis, the Fenchel dual objective attains `- primalOptimalValue`. -/
theorem exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain_shared
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      primalOptimalValue f g = -(fenchelDualObjective f g u) := by
  -- Route correction: the remaining blocker is now isolated to this upstream same-space owner.
  -- TODO: import an upstream owner for the two zero-slice inputs below.
  -- `hexact0` should come from the same-space exactness theorem at `0`, and `hzero` should come
  -- from the same-space conjugacy identity combined with
  -- `pointwiseAdd_conjugate_zero_eq_neg_primalOptimalValue_shared`.
  have hexact0 :
      infimalConvolution.ExactAt
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (0 : H) := by
    sorry
  have hzero :
      (f.asEReal∗ □ g.asEReal∗) (0 : H) = -primalOptimalValue f g := by
    sorry
  -- Once the zero-slice exactness and value identity are supplied, the owner theorem is now a
  -- direct application of the local bridge.
  exact
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_slice_shared
      f hf g hg hexact0 hzero

end FenchelDuality

end ERealFunction
