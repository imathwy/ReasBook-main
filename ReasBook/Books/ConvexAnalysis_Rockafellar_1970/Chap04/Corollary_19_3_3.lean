import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_3_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_11_4_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 19.3.3 asserts that two nonempty disjoint polyhedral convex sets in
  a finite-dimensional normed space with a linear pairing into `Y` admit a strongly separating
  hyperplane.
- `core/canonical`: the owner predicates already available in the project are
  `Set.IsPolyhedral` for the two sets and the strong-separation owner
  `H stronglySeparates[Y] C1 and C2` for the separating hyperplane.
- Domain-style sampling used here: `Set.IsPolyhedral`, `Set.IsPolyhedral.sub`,
  `Set.IsPolyhedral.isClosed_hasFiniteFaces`,
  `AffineSubspace.StronglySeparates` / `stronglySeparates[Y]`, and
  `exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub`.
- Primitive data vs derived API: the polyhedrality and nonemptiness hypotheses on `C1`, `C2`
  are the source-facing inputs, while existence of a strongly separating hyperplane is theorem-
  level output. The nonemptiness assumptions are semantically essential here: the statement fails
  for `C1 = ∅` and `C2 = Set.univ`, even though both are polyhedral convex and disjoint.
- Layer target: `source-facing`, stated directly with the chapter owners for polyhedrality and
  strong separation.
- Ambient refinement: the proof uses only the generic owner APIs from Corollary 19.3.2 and
  Corollary 11.4.1, so the public theorem stays on the common ordered normed-
  field plus pairing-codomain layer rather than collapsing to a concrete self-pairing model.
  The explicit scalar assumptions are kept minimal here: `IsStrictOrderedRing` and
  `OrderTopology` are inferred from the remaining ambient layer and therefore are not exposed on
  the theorem surface.
-/

namespace Set.IsPolyhedral

/-- Corollary 19.3.3: if `C1` and `C2` are nonempty disjoint polyhedral convex sets in a
finite-dimensional normed pairing space over an ordered normed field `𝕜`,
then some hyperplane strongly separates `C1` and `C2`. -/
-- Proof sketch: polyhedrality is stable under linear images and Minkowski sums, so
-- `C1 - C2 = C1 + (-1) • C2` is polyhedral and hence closed. Then apply the Chapter 11
-- primitive bridge from disjointness, convexity, nonemptiness, and closed difference.
theorem exists_hyperplane_strongly_separating_of_disjoint_nonempty
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜 Y) (hC1_nonempty : C1.Nonempty)
    (hC2 : C2.IsPolyhedral 𝕜 Y) (hC2_nonempty : C2.Nonempty)
    (hdisj : Disjoint C1 C2) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hsub_poly : (C1 - C2).IsPolyhedral 𝕜 Y := hC1.sub hC2
  have hsub_closed : IsClosed (C1 - C2) := hsub_poly.isClosed_hasFiniteFaces.1
  exact
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
      hC1_nonempty hC1.convex hC2_nonempty hC2.convex hdisj hsub_closed

end Set.IsPolyhedral

end
