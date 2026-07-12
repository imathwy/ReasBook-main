import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_1
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Affine

variable {𝕜 : Type*} {V : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.0.5 says every affine subset, including `∅` and `Set.univ`,
  is convex. The formal statement is the coordinate-free ordered-ring module version.
- `core/canonical`: the owner abstraction is `AffineSubspace 𝕜 V`, with canonical convexity fact
  `AffineSubspace.convex`, and the source-facing set owner is `affine[𝕜] C`.
- `bridge/view`: the fixed-point criterion `C = affineSpan 𝕜 C` and the explicit carrier witness
  form `∃ S : AffineSubspace 𝕜 V, C = S` are retained as derived bridge corollaries.
- Domain-style sampling used here: `AffineSubspace.convex`, `affineSpan`,
  `Set.IsAffine`, `affine[𝕜]`, `isAffine_iff_affineSpan_eq_self`.
- Primitive data vs derived API: `AffineSubspace` and `AffineSubspace.convex` are primitive owner
  API; `Set.IsAffine` is the canonical set-level owner; affine-span and existential carrier forms
  are derived views.
- Layer target: `source-facing` owner form `affine[𝕜]`, with bridge lemmas for nearby set-level
  criteria.
-/

namespace Set

/- Proposition 2.0.5 is governed by the owner theorem `AffineSubspace.convex`; the primary
source-facing theorem below is the canonical set-owner notation `affine[𝕜]`. -/
recall AffineSubspace.convex

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no extended-codomain object appears; this item is a set-level convexity
  statement in a module.
- Scalar/ambient structure check: keep the canonical `Convex`/`AffineSubspace.convex` layer
  assumptions `[Ring 𝕜] [PartialOrder 𝕜]`.
- Owner check: keep `affine[𝕜]` as the source-facing owner and derive convexity from the
  canonical owner theorem `AffineSubspace.convex`.
- Topology check: no topological operator is part of this statement.
- Owner-name check: no additional owner synonym is introduced.
- Notation check: no new notation is needed for this item.
-/

/-- The affine span of any set is convex. This is the direct set-level bridge of
`AffineSubspace.convex`. -/
theorem convex_affineSpan (C : Set V) :
    Convex 𝕜 (affineSpan 𝕜 C : Set V) := by
  simpa using (affineSpan 𝕜 C).convex

namespace IsAffine

variable {C : Set V}

/-- Proposition 2.0.5 in owner-method form: every affine set is convex. -/
theorem convex (hC : affine[𝕜] C) : Convex 𝕜 C := by
  -- Route correction: use the source proof directly by specializing affine-combination
  -- closure to coefficients in `[0, 1]`, instead of switching to the affine-subspace owner.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  -- The affine hypothesis gives membership for the same binary affine combination at scalar `b`.
  have hline : AffineMap.lineMap x y b ∈ C := hC.lineMap_mem hx hy b
  -- Rewriting the affine combination with `a + b = 1` yields the required convex combination.
  have ha' : a = 1 - b := by
    rw [← hab]
    abel
  simpa [AffineMap.lineMap_apply_module, ha'] using hline

end IsAffine

/-- Proposition 2.0.5 in notation-first owner form: every affine set is convex. -/
theorem convex_of_affine {C : Set V} :
    (affine[𝕜] C) → Convex 𝕜 C :=
  IsAffine.convex

/-- Proposition 2.0.5 in affine-span fixed-point form: if `affineSpan 𝕜 C = C`, then `C` is
convex. This is a bridge corollary of `IsAffine.convex`. -/
theorem convex_of_affineSpan_eq {C : Set V} (hC : affineSpan 𝕜 C = C) :
    Convex 𝕜 C := by
  have hAffine : affine[𝕜] C := IsAffine.of_affineSpan_eq hC
  exact hAffine.convex

/-- Proposition 2.0.5 in existential owner form: if `C` is the carrier of an affine subspace,
then `C` is convex. This is a bridge corollary of `IsAffine.convex`. -/
theorem convex_of_exists_affineSubspace {C : Set V}
    (hC : ∃ S : AffineSubspace 𝕜 V, C = S) :
    Convex 𝕜 C := by
  have hAffine : affine[𝕜] C := IsAffine.of_exists_affineSubspace_eq hC
  exact hAffine.convex

end Set
