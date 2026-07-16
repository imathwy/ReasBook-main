import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_4_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ]
variable [((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)).IsContPerfPair]

local notation:max C "ᵒ[ℝ]" => (Set.polar (X := E) (Y := E) (α := ℝ) C)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 14.6.1 states the dimension, lineality, and rank relations between a
  convex set `C` with `0 ∈ closure C` and its polar `Cᵒ[ℝ]`, after discharging the textbook
  closedness hypothesis through closure-invariance of the owner constructions.
- `core/canonical`: the owner abstractions already present in the project are the set polar
  `Set.polar`, the set invariants `Set.affineDim`, `Set.lineality`, and `Set.rank`, and the
  finite-dimensional pairing-orthogonality owner layer.
- `bridge/view`: the textbook notation `Cᵒ` is rendered by the scalar-explicit owner surface
  `Cᵒ[ℝ]`; the textbook
  word “dimension” is rendered by the chapter owner `Set.affineDim`.

Domain-style sampling used here:
- `Set.polar` from `Text_14_0_5`;
- `supportFunction_closure` from `Text_13_0_5` together with `Set.polar_polar_eq` from
  `Theorem_14_5`, supplying closure-invariance and the needed bipolar bridge;
- `closure_span_polar_eq_orthogonal_span_lineal` from `Theorem_14_6`, which is the owner
  orthogonality statement behind the numerical formulas;
- `Set.lineality` from `Definition_8_4_4` together with `Set.rank` from `Definiton_8_4_6`, the
  Chapter 8 owner numerics used in the source-facing conclusions.

The item is kept `source-facing`: it states the three numerical identities directly for
`Set.polar (X := E) (Y := E) (α := ℝ) C`, rendered as `Cᵒ[ℝ]`, without introducing any wrapper
around the existing set invariants. The ambient type is lifted from the coordinate model `ℝ^n` to
the finite-dimensional real pairing owner layer (with a continuous perfect pairing), preserving the
source meaning while deleting unnecessary concrete-model ownership from the public surface.
-/

section

variable {C : Set E}
variable (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ closure C)

-- Proof sketch: use `supportFunction_closure` to replace `C` by `closure C`, so `Cᵒ[ℝ]` is the polar
-- of a closed convex set containing `0`. Theorem 14.5 then gives the mutual-polar relation
-- `(Cᵒ[ℝ])ᵒ[ℝ] = closure C`, and Theorem 14.6 identifies the closed span of `Cᵒ[ℝ]` with the orthogonal
-- complement of the lineality space of `closure C`. In the finite-dimensional ambient space `E`,
-- every subspace is closed, so this is the same as the ordinary span. Because `0 ∈ Cᵒ[ℝ]`, the
-- affine hull of the polar agrees with its linear span, and lineality is unchanged by passing
-- from `C` to `closure C`, yielding the ambient-dimension subtraction formula.
/-- Corollary 14.6.1 (1): on a finite-dimensional real pairing space with continuous perfect
pairing, if `C` is convex and `0 ∈ closure C`, then the affine dimension of `Cᵒ[ℝ]` is the ambient
dimension minus the lineality of `C`. Specializing to `E = ℝ^n` with the canonical inner-product
pairing recovers the textbook formula `dim Cᵒ = n - lin C`. -/
theorem affineDim_polar_eq_ambientDim_sub_lineality :
    dim[ℝ](Cᵒ[ℝ]) = (Module.finrank ℝ E : ℤ) - lineality[ℝ](C) := sorry

-- Proof sketch: the same closed replacement `closure C` and bipolar bridge from Theorem 14.5
-- reduce the statement to the orthogonality clause of Theorem 14.6 for the polar pair
-- `(closure C, Cᵒ[ℝ])`. Since `0 ∈ closure C`, the affine span of `closure C` is the same
-- as its linear span, and `Set.affineDim` is closure-invariant, so the orthogonal-complement
-- dimension formula becomes the stated identity for the lineality of `Cᵒ[ℝ]`.
/-- Corollary 14.6.1 (2): on a finite-dimensional real pairing space with continuous perfect
pairing, the lineality of `Cᵒ[ℝ]` is the ambient dimension minus the affine dimension of `C`
whenever `C` is convex and `0 ∈ closure C`. In `ℝ^n` with the canonical inner-product pairing,
this is `lin Cᵒ = n - dim C`. -/
theorem lineality_polar_eq_ambientDim_sub_affineDim :
    lineality[ℝ](Cᵒ[ℝ]) = (Module.finrank ℝ E : ℤ) - dim[ℝ](C) := sorry

-- Proof sketch: unfold `Set.rank` on both `C` and `Cᵒ[ℝ]`, then combine the first two
-- clauses of this corollary under the shared hypotheses `Convex ℝ C` and `0 ∈ closure C`. The
-- two complementary subtraction formulas cancel to give equality of ranks.
/-- Corollary 14.6.1 (3): `Cᵒ[ℝ]` has the same rank as `C` for a convex set whose closure contains
the origin. In particular, this specializes to Rockafellar's `ℝ^n` statement. -/
theorem rank_polar_eq_rank :
    rank[ℝ](Cᵒ[ℝ]) = rank[ℝ](C) := sorry

end
