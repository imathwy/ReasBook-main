import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

section

variable {𝕜 : Type w} [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {X : Type u} {Y : Type v}
variable [Zero X] [Zero Y]
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]

namespace Function

/-- `f` is zero-normalized when both its global infimum and its value at the origin are `0`. -/
def IsZeroNormalized (f : X → WithTopBot 𝕜) : Prop :=
  (⨅ x : X, f x) = 0 ∧ f 0 = 0

namespace IsZeroNormalized

variable (f : X → WithTopBot 𝕜)

-- Proof sketch: evaluate `convexConjugate_eq_iSup_pairing_sub` at `0` to rewrite `f⋆ 0` as the
-- supremum of `-f x`, then use `WithBotTop.negOrderIso.map_iInf` to identify that supremum with
-- `- (⨅ x, f x)`. Applying the same origin formula to `f⋆` on the dual side rewrites the infimum
-- of the conjugate in terms of `(f⋆)⋆` at `0`; the owner equation
-- `(f⋆)⋆ = f` then turns each pair of normalization
-- equalities into the other.
/-- Core normalization bridge on dual pairings: if `f` equals its dual Fenchel biconjugate, then
`inf_x f(x) = f(0) = 0` is equivalent to `inf_y f*(y) = f*(0) = 0`. -/
theorem iff_conjugate_of_eq_dual_biconjugate
    (hf_biconj : (f⋆)⋆ = f)
    [HasPairingZeroRight X Y 𝕜] [HasPairingZeroRight Y X 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  have hneg_iInf_X (g : X → WithTopBot 𝕜) : - (⨅ x : X, g x) = ⨆ x : X, -g x := by
    exact congrArg OrderDual.ofDual (WithBotTop.negOrderIso.map_iInf fun x ↦ g x)
  have hneg_iInf_Y (g : Y → WithTopBot 𝕜) : - (⨅ y : Y, g y) = ⨆ y : Y, -g y := by
    exact congrArg OrderDual.ofDual (WithBotTop.negOrderIso.map_iInf fun y ↦ g y)
  have hconj_zero : f⋆ (0 : Y) = - (⨅ x : X, f x) := by
    calc
      f⋆ (0 : Y) = ⨆ x : X, ⟪x, (0 : Y)⟫ₚ - f x := by
        rw [convexConjugate_eq_iSup_pairing_sub]
      _ = ⨆ x : X, (((⟪x, (0 : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) := by
        rfl
      _ = ⨆ x : X, -f x := by
        refine iSup_congr ?_
        intro x
        simp
      _ = - (⨅ x : X, f x) := by
        exact (hneg_iInf_X f).symm
  have hconj_conj_zero : (f⋆)⋆ 0 = - (⨅ y : Y, f⋆ y) := by
    calc
      (f⋆)⋆ 0 = ⨆ y : Y, ⟪y, (0 : X)⟫ₚ - f⋆ y := by
        simpa using convexConjugate_convexConjugate_eq_iSup_pairing_sub (f := f) (x := (0 : X))
      _ = ⨆ y : Y, (((⟪y, (0 : X)⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y) := by
        rfl
      _ = ⨆ y : Y, -f⋆ y := by
        refine iSup_congr ?_
        intro y
        simp
      _ = - (⨅ y : Y, f⋆ y) := by
        exact (hneg_iInf_Y f⋆).symm
  constructor
  · rintro ⟨hinf, hzero⟩
    refine ⟨?_, ?_⟩
    · have hneg : -f 0 = ⨅ y : Y, f⋆ y := by
        simpa [hf_biconj] using congrArg Neg.neg hconj_conj_zero
      simpa [hzero] using hneg.symm
    · simpa [hinf] using hconj_zero
  · rintro ⟨hinf_conj, hzero_conj⟩
    refine ⟨?_, ?_⟩
    · have hneg : -f⋆ (0 : Y) = ⨅ x : X, f x := by
        simpa using congrArg Neg.neg hconj_zero
      simpa [hzero_conj] using hneg.symm
    · have hzero : f 0 = - (⨅ y : Y, f⋆ y) := by
        simpa [hf_biconj] using hconj_conj_zero
      simpa [hinf_conj] using hzero

end IsZeroNormalized

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.4 states that for a closed convex function on `R^n`, the
  normalization condition `inf_x f(x) = f(0) = 0` is equivalent to the same normalization
  condition for the conjugate `f*`. The source's separate properness hypothesis is redundant here,
  because either normalization clause already forces properness.
- `core/canonical`: the chapter owner for conjugation is `convexConjugate`, and the canonical Lean
  form of the global infimum is the complete-lattice expression `⨅ x, f x` on each pairing side.
- `bridge/view`: the textbook proof uses the chapter bridge
  `convexConjugate_eq_iSup_pairing_sub` at `0`, together with the order-isomorphism identity
  `WithBotTop.negOrderIso.map_iInf`; concrete closed-convex self-pairing specializations are
  obtained upstream from the dual biconjugacy owner equation.

Domain-style sampling used here:
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- the dual pairing owners `HasPairing X Y 𝕜` and `HasPairing Y X 𝕜`;
- the primitive zero-pairing owner assumptions on both pairing orientations;
- the dual biconjugacy owner hypothesis `(f⋆)⋆ = f`.

Primitive data vs derived API:
- primitive input: a function `f : X → WithTopBot 𝕜`;
- primitive owner hypothesis for the core theorem:
  `(f⋆)⋆ = f`;
- primitive pairing bridges used at the theorem surface:
  `[HasPairingZeroRight X Y 𝕜]` and `[HasPairingZeroRight Y X 𝕜]`;
- source-facing normalization owner:
  `f.IsZeroNormalized` and `(f⋆).IsZeroNormalized`;
- derived API: the chapter-facing long-name restatement on the self-pairing specialization.

Layer target: `core/canonical` and `source-facing` aligned: the core theorem is now on the
primitive dual-biconjugate owner layer, and concrete closed-convex self-pairing hypotheses are
handled upstream.
-/

variable {E : Type u} [Zero E] [HasPairing E E 𝕜]

/-- Self-pairing specialization of the dual normalization bridge under `f⋆⋆ = f`. -/
theorem
    Function.IsZeroNormalized.iff_conjugate_of_eq_biconjugate
    (f : E → WithTopBot 𝕜) (hf_biconj : f⋆⋆ = f)
    [HasPairingZeroRight E E 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  have hf_biconj' : (f⋆)⋆ = f := by
    simpa [convexBiconjugate] using hf_biconj
  simpa using
    (Function.IsZeroNormalized.iff_conjugate_of_eq_dual_biconjugate
      (f := f) hf_biconj')

/-- Chapter-facing normalization equivalence under the canonical biconjugacy owner equation.
This keeps the historical theorem name while exposing the abstraction layer directly. -/
theorem infimum_and_origin_value_eq_zero_iff_conjugate_infimum_and_origin_value_eq_zero
    (f : E → WithTopBot 𝕜) (hf_biconj : f⋆⋆ = f)
    [HasPairingZeroRight E E 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  simpa using
    (Function.IsZeroNormalized.iff_conjugate_of_eq_biconjugate
      f hf_biconj)

end
