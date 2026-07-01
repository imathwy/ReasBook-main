import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for the main item:

  finite-dimensional topological module over a linearly ordered topological field:
  polyhedrality, closedness with finitely many faces, and finite generation by points and
  directions.
- `core/canonical`: the owner predicates already present in the project are
  `Set.IsPolyhedral`, `Set.IsFace.faces` (notation `𝓕[𝕜](C)`),
  `Set.IsFinitelyGeneratedConvex`, and `List.TFAE`.
- `bridge/view`: no extra bridge owner is introduced for "finite faces"; the clause is stated
  directly as finiteness of the canonical face family `(𝓕[𝕜](C)).Finite`.

Domain-style sampling used here:
- `Set.IsPolyhedral`;
- `Set.IsFace`;
- `Set.IsFace.trans`;
- `Set.IsFinitelyGeneratedConvex`;
- `List.TFAE`.

Primitive data vs derived API:
- primitive input: the set `C`;
- derived API: the three equivalent structural descriptions of `C`, with convexity carried in the
  middle owner clause rather than as an external theorem argument.

Layer target: `source-facing`, stated directly in terms of the chapter's existing owner predicates
for polyhedrality, faces, and mixed finite generation.

Ambient refinement: the owner predicates `Set.IsPolyhedral`, `Set.IsFace`, and
`Set.IsFinitelyGeneratedConvex` are already coordinate-free, and the nearby Chapter 18 face theory
has already been lifted from `EuclideanSpace ℝ (Fin n)` to arbitrary finite-dimensional ambient
spaces. The source `R^n` model is therefore a presentation, not the owner level, so the public
theorem is stated directly on that finite-dimensional topological owner layer and uses the same
ordered topological field scalar assumptions as the Chapter 18 bridge surface rather than a
normed/completeness specialization.
-/

namespace Set.IsPolyhedral

/-- Theorem 19.1 in canonical owner form: for `C` in a finite-dimensional topological `𝕜`-module,
polyhedrality, convexity+closedness with finite face family `(𝓕[𝕜](C)).Finite`, and finite
generation by points and directions are equivalent. -/
-- Proof sketch: prove `(a) → (b)` by showing every face of a polyhedral set arises from one of
-- finitely many choices of ambient half-spaces versus boundary hyperplanes, so only finitely many
-- faces can occur. For `(b) → (c)`, first treat the pointed case using Theorem 18.5 to generate
-- `C` from its extreme points and extreme directions, both finite because there are only finitely
-- many faces; then split off the lineality space in the general case. For `(c) → (b)`, apply
-- Caratheodory's theorem to cover `C` by finitely many generalized simplices, obtaining
-- closedness and finiteness of faces from the finite generating family. Finally, `(b) → (a)`
-- follows because an `n`-dimensional closed convex set is the intersection of its tangent closed
-- half-spaces, and each tangent half-space corresponds to an exposed face; finitely many faces
-- therefore give finitely many tangent half-spaces.
theorem tfae {C : Set E} :
    List.TFAE
      [ C.IsPolyhedral 𝕜,
        Convex 𝕜 C ∧ IsClosed C ∧ (𝓕[𝕜](C)).Finite,
        C.IsFinitelyGeneratedConvex 𝕜 ] := sorry

/-- Polyhedrality is equivalent to convexity together with closedness and finiteness of faces. -/
theorem iff_convex_isClosed_finiteFaces {C : Set E} :
    C.IsPolyhedral 𝕜 ↔ Convex 𝕜 C ∧ IsClosed C ∧ (𝓕[𝕜](C)).Finite :=
  (tfae (C := C)).out 0 1

/-- Convex-input bridge: polyhedrality is equivalent to closedness and finiteness of faces. -/
theorem iff_isClosed_finiteFaces {C : Set E} (hC_convex : Convex 𝕜 C) :
    C.IsPolyhedral 𝕜 ↔ IsClosed C ∧ (𝓕[𝕜](C)).Finite := by
  constructor
  · intro hC_polyhedral
    exact (iff_convex_isClosed_finiteFaces (C := C)).1 hC_polyhedral |>.2
  · intro hC_closed_finiteFaces
    exact (iff_convex_isClosed_finiteFaces (C := C)).2
      ⟨hC_convex, hC_closed_finiteFaces⟩

/-- Polyhedrality is equivalent to finite generation by points and directions. -/
theorem iff_isFinitelyGeneratedConvex {C : Set E} :
    C.IsPolyhedral 𝕜 ↔ C.IsFinitelyGeneratedConvex 𝕜 := by
  constructor
  · intro hC_polyhedral
    exact ((tfae (C := C)).out 0 2).1
      hC_polyhedral
  · intro hC_finitely_generated
    exact ((tfae (C := C)).out 0 2).2
      hC_finitely_generated

/-- A polyhedral convex set is closed and has finitely many faces. -/
theorem isClosed_hasFiniteFaces {C : Set E} (hC : C.IsPolyhedral 𝕜) :
    IsClosed C ∧ (𝓕[𝕜](C)).Finite :=
  (iff_convex_isClosed_finiteFaces (C := C)).mp hC |>.2

/-- A polyhedral convex set is finitely
generated. -/
theorem isFinitelyGeneratedConvex {C : Set E} (hC : C.IsPolyhedral 𝕜) :
    C.IsFinitelyGeneratedConvex 𝕜 :=
  (iff_isFinitelyGeneratedConvex (C := C)).mp hC

end Set.IsPolyhedral

namespace Set.IsFinitelyGeneratedConvex

/-- A finitely generated convex set is
polyhedral convex. -/
theorem isPolyhedral {C : Set E} (hC : C.IsFinitelyGeneratedConvex 𝕜) :
    C.IsPolyhedral 𝕜 :=
  (Set.IsPolyhedral.iff_isFinitelyGeneratedConvex (C := C)).mpr hC

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolytope

/-- Every polytope is polyhedral convex. -/
theorem isPolyhedral {C : Set E} (hC : C.IsPolytope 𝕜) : C.IsPolyhedral 𝕜 :=
  hC.isFinitelyGeneratedConvex.isPolyhedral

end Set.IsPolytope

end
