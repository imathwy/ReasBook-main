import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
  [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.2 is the separation statement that a nonempty relatively open convex
  set and a disjoint nonempty affine set can be separated by a hyperplane containing the affine
  set.
- `core/canonical`: the primitive relative-openness owner data is the equation `ri[𝕜](·) = ·`,
  together with `Convex 𝕜`, `AffineSubspace 𝕜 V`, and the Chapter 11 separation relation
  `AffineSubspace.Separates`. The source-facing predicate `IsRelativelyOpen 𝕜` is kept as a thin
  bridge.
- `bridge/view`: the textbook phrase “one of the open half-spaces associated with `H` contains
  `C`” is represented owner-theoretically by `H.Separates C M` together with
  `Disjoint C H`; unpacking `H.Separates` recovers the normal equation
  `H = affineHyperplane b β` and the open half-space alternative.
- Primitive data vs derived API: the primitive inputs are the owner equality
  `ri[𝕜](C) = C`, convexity and nonemptiness of `C`, the
  affine-set owner `M`, its intrinsic nonemptiness as `∃ x, x ∈ M`, and the disjointness
  assumption. The containing hyperplane
  and its separation-side properties are theorem-level content and should not be packaged into a
  new structure.
- Domain-style sampling used here: `ri[𝕜](·)`, `AffineSubspace`, the owner relation
  `AffineSubspace.Separates`, and its canonical witness presentation through `affineHyperplane`.
- Layer target: this item stays `source-facing`, but its main public conclusion is refined to the
  affine-subspace owner `H` rather than a raw `∃ b, ∃ β` witness shell.
- Ambient refinement: although Rockafellar states the theorem in `R^n`, the separation owner is
  already pairing-based in `Text_11_0_1`, and relative interior/convexity are scalar-polymorphic.
  So the public theorem surface is upgraded from real inner-product self-pairing to a finite-
  dimensional Hausdorff topological `𝕜`-vector space equipped with an explicit pairing owner.
-/

/-- Theorem 11.2 on the canonical owner layer: if `C` is a nonempty convex set with
`ri[𝕜](C) = C` in a finite-dimensional Hausdorff topological `𝕜`-vector space and `M` is a
nonempty affine set disjoint from `C`, then there is a hyperplane `H` containing `M` such that
`H` separates `C` from `M` and is disjoint from `C`. Unpacking `H.Separates C M` recovers the
textbook open-half-space form.
Specializing to `𝕜 = ℝ` and the inner-product pairing on `V` gives the source `R^n` model. -/
-- Proof sketch: if `M` is already a hyperplane, convexity and relative openness force `C` to lie
-- on one side of it. Otherwise, translate so that `M` becomes a linear subspace and enlarge `M`
-- inductively by one dimension inside a line through the origin that misses the projected convex
-- slice; after finitely many steps this produces a codimension-one affine set containing the
-- original `M` and still disjoint from `C`, whose associated open half-space contains `C`.
theorem exists_separating_hyperplane_containing_of_disjoint_ri_eq_self_convex
    (M : AffineSubspace 𝕜 V) {C : Set V} (hC_ri : ri[𝕜](C) = C) (hC_conv : Convex 𝕜 C)
    (hC_nonempty : C.Nonempty) (hM_nonempty : ∃ x, x ∈ M)
    (hdisj : Disjoint C M) :
    ∃ H : AffineSubspace 𝕜 V, M ≤ H ∧ H.Separates Y C M ∧ Disjoint C H := sorry

/-- Source-facing bridge form of Theorem 11.2: `IsRelativelyOpen 𝕜 C` rewrites to the canonical
owner equation `ri[𝕜](C) = C`. -/
theorem exists_separating_hyperplane_containing_of_disjoint_relativelyOpen_convex
    (M : AffineSubspace 𝕜 V) {C : Set V} (hC_open : IsRelativelyOpen 𝕜 C) (hC_conv : Convex 𝕜 C)
    (hC_nonempty : C.Nonempty) (hM_nonempty : ∃ x, x ∈ M)
    (hdisj : Disjoint C M) :
    ∃ H : AffineSubspace 𝕜 V, M ≤ H ∧ H.Separates Y C M ∧ Disjoint C H := by
  simpa [IsRelativelyOpen] using
    (exists_separating_hyperplane_containing_of_disjoint_ri_eq_self_convex
      M hC_open hC_conv hC_nonempty hM_nonempty hdisj)

end
