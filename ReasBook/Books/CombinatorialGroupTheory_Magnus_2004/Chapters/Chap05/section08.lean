import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_8_1 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

/-- The source-facing knot data used by Section `5.8`: a type of projections, the standard and
alternating predicates on those projections, the ambient alternating-knot predicate, and for each
projection the canonical finite presentation of the attached knot group. -/
structure Knot where
  /-- The type of projections of this knot. -/
  Projection : Type u
  /-- A projection is standard when it has the textbook regularity properties used in Section
  `5.8`. -/
  IsStandardProjection : Projection → Prop
  /-- A projection is alternating when crossings alternate over and under along each component. -/
  IsAlternatingProjection : Projection → Prop
  /-- The ambient knot is alternating. -/
  IsAlternating : Prop
  /-- The canonical knot group attached to this knot. -/
  knotGroup : Type v
  /-- The natural group structure on the knot group. -/
  instGroupKnotGroup : Group knotGroup
  /-- The canonical number of generators in the presentation attached to a projection. -/
  presentationRank : Projection → ℕ
  /-- The canonical relator set in the presentation attached to a projection. -/
  presentationRelators (P : Projection) : Set (FreeGroup (Fin (presentationRank P)))
  /-- The canonical presentation equivalence attached to a projection. -/
  presentationEquiv (P : Projection) :
    PresentedGroup (presentationRelators P) ≃* knotGroup

attribute [instance] Knot.instGroupKnotGroup

noncomputable section

open FreeGroupBasis

namespace Knot

section

/-!
Primary domain: finite small-cancellation presentations coming from standard alternating knot
projections.

Layer triage:
- `source-facing`: a knot `K : Knot`, a chosen projection `P : K.Projection`, and the predicates
  saying that `P` is standard and alternating, together with the canonical presentation data
  already attached to `P`.
- `core/canonical`: `K.presentationRelators P` and `K.presentationEquiv P` reuse the project owner
  `PresentedGroup R ≃* K.knotGroup` for the canonical presentation of the knot group determined by
  `P`, while `C(4)[ofFreeGroup (Fin n), R]` and `T(4)[ofFreeGroup (Fin n), R]` are the Chapter `5`
  owner predicates expressing the small-cancellation conclusion on that relator set.
- `bridge/view`: this file is exactly the bridge from standard/alternating projection hypotheses
  to the Chapter `5` small-cancellation properties of the canonical presentation attached to that
  projection.

Domain sampling:
1. `Knot` in this file is the source-facing owner for a knot, its projections, and the canonical
   presentation attached to each projection.
2. `PresentedGroup R ≃* K.knotGroup` from Definition `2-1-1` is the project's canonical owner for
   a finite presentation of the knot group, and it is recorded here as `K.presentationEquiv P`.
3. `FreeGroupBasis.condition_c`, written `C(4)[FreeGroupBasis.ofFreeGroup (Fin n), R]`, from
   Definition `5-2-2` is the owner predicate for the `C(4)` conclusion.
4. `FreeGroupBasis.condition_t`, written `T(4)[FreeGroupBasis.ofFreeGroup (Fin n), R]`, from
   Definition `5-2-3` is the owner predicate for the `T(4)` conclusion.

Primitive vs. derived:
- primitive public data: the knot `K`, the projection `P : K.Projection`, and the predicates
  `K.IsStandardProjection` and `K.IsAlternatingProjection`, together with the canonical
  projection-attached presentation data `K.presentationRank P`, `K.presentationRelators P`, and
  `K.presentationEquiv P`;
- derived API: finiteness and the canonical `C(4)` and `T(4)` owner predicates for that attached
  relator set.
-/

-- Proof sketch: for a standard alternating projection, its canonical Wirtinger-type presentation
-- is finite. The relators of that canonical presentation have the combinatorial form needed for
-- the Chapter `5` small-cancellation analysis, giving `C(4)` and `T(4)` on the canonical
-- free-group basis.
/-- Lemma 5-8-1: the canonical presentation attached to a standard alternating projection of a
knot is finite and satisfies `C(4)` and `T(4)`. -/
theorem presentation_of_standard_alternating_projection
    (K : Knot.{u, v}) {P : K.Projection} (hP_standard : K.IsStandardProjection P)
    (hP_alternating : K.IsAlternatingProjection P) :
    (K.presentationRelators P).Finite ∧
      C(4)[ofFreeGroup (Fin (K.presentationRank P)), K.presentationRelators P] ∧
      T(4)[ofFreeGroup (Fin (K.presentationRank P)), K.presentationRelators P] := sorry

end

end Knot

/-! ### Lemma_5_8_3 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

namespace Knot

section

/-!
Primary domain: existence of standard and alternating projections of knots.

Layer triage:
- `source-facing`: a knot `K : Knot`, its projections, and the predicates saying that a projection
  is standard or alternating and that `K` itself is alternating.
- `core/canonical`: `Knot` is the owner abstraction for that primitive knot-projection data,
  including the canonical presentation attached to each projection and the canonically attached
  knot group.
- `bridge/view`: `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the
  downstream bridge from a standard alternating projection to the presentation-theoretic Chapter
  `5` API.

Domain sampling:
1. `Knot` from Lemma `5-8-1` is the source-facing owner for a knot, its projections, and the
   canonical presentation attached to each projection.
2. `K.Projection` is the owner type for the projections of `K`.
3. `K.IsStandardProjection`, `K.IsAlternatingProjection`, and `K.IsAlternating` are the owner
   predicates for the standard and alternating hypotheses used here.
4. `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the canonical
   downstream bridge that consumes the data produced by part `(2)` of this lemma.

Primitive vs. derived:
- primitive public data: the knot `K`, its projection type `K.Projection`, and the source-facing
  predicates `K.IsStandardProjection`, `K.IsAlternatingProjection`, and `K.IsAlternating`,
  together with the canonical presentation attached to each projection by the `Knot` owner;
- derived API: the two existence statements of Lemma `5-8-3`.
-/

/-- Lemma 5-8-3 (1): every knot admits a projection that is standard. -/
-- Proof sketch: start from any diagram of the knot and apply the standard normalization process
-- for knot projections to obtain a standard projection representing the same knot.
theorem exists_standard_projection (K : Knot.{u, v}) :
    ∃ P : K.Projection, K.IsStandardProjection P := sorry

/-- Lemma 5-8-3 (2): an alternating knot admits a standard projection that is alternating. -/
-- Proof sketch: begin with an alternating diagram of the knot and run the standardization
-- procedure in a way that preserves the alternating crossing pattern, producing an alternating
-- standard projection.
theorem exists_alternating_standard_projection (K : Knot.{u, v}) (hK : K.IsAlternating) :
    ∃ P : K.Projection, K.IsStandardProjection P ∧ K.IsAlternatingProjection P := sorry

end

end Knot

/-! ### Lemma_5_8_4 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis

section

variable {X : Type u}

local instance instDecidableEqX_5_8_4 : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

namespace GroupPresentation

/-!
Primary domain: decision problems for small-cancellation quotients of finitely generated free
groups.

Layer triage:
- `source-facing`: a finite relator set `R` in a free group, together with the Chapter `5`
  small-cancellation hypotheses `C(4)` and `T(4)`.
- `core/canonical`: `hasSolvableWordProblem_of_finite_smallCancellation` and
  `hasSolvableConjugacyProblem_of_finite_smallCancellation` are the existing Chapter `5` owner
  theorems for the word and conjugacy conclusions, while `HasSolvableWordProblem R`,
  `HasSolvableConjugacyProblem R`, `C(4)[basis, R]`, and `T(4)[basis, R]` are the underlying
  owner predicates.
- `bridge/view`: this file is only the `(C(4), T(4))` specialization of those upstream
  small-cancellation theorems, expressed using the canonical basis
  `basis = FreeGroupBasis.ofFreeGroup X`.

Domain sampling:
1. `GroupPresentation.hasSolvableWordProblem_of_finite_smallCancellation` from Theorem `5-6-3`
   is the canonical Chapter `5` theorem for solvable word problem under the three standard
   small-cancellation alternatives.
2. `GroupPresentation.hasSolvableConjugacyProblem_of_finite_smallCancellation` from Theorem
   `5-7-6` is the matching canonical theorem for solvable conjugacy problem.
3. `FreeGroupBasis.condition_c`, written `C(4)[basis, R]`, is the owner predicate for the `C(4)`
   hypothesis.
4. `FreeGroupBasis.condition_t`, written `T(4)[basis, R]`, is the owner predicate for the `T(4)`
   hypothesis.

Primitive vs. derived:
- primitive public data: the relator set `R`, finiteness of the generator type and relator set,
  and the Chapter `5` small-cancellation hypotheses;
- derived API: the two `(C(4), T(4))` corollaries, obtained by specializing the canonical
  small-cancellation owner theorems to the middle disjunct.
-/

variable (R : Set (FreeGroup X)) [Finite X] [Primcodable X]

-- Proof sketch: specialize the Chapter `5` small-cancellation word-problem theorem to the
-- `(C(4), T(4))` case. The source knot-group assumptions that `R` is symmetrized and all relators
-- have length four are bookkeeping for this application, while the decision-problem conclusion is
-- expressed directly through the canonical owner predicates `C(4)[basis, R]` and `T(4)[basis, R]`.
/-- Lemma 5-8-4 (1): if `R` is a finite relator set in the finitely generated free group
`FreeGroup X` and `R` satisfies `C(4)` and `T(4)`, then the quotient by the normal closure of `R`
has solvable word problem. The source phrase “`T(4)` for minimal sequences” is recorded here
through the Chapter `5` owner predicate `T(4)[basis, R]`. -/
theorem hasSolvableWordProblem_of_finite_C4_T4
    (hR : R.Finite) (hC4 : C(4)[basis, R]) (hT4 : T(4)[basis, R]) :
    HasSolvableWordProblem R := by
  simpa using
    hasSolvableWordProblem_of_finite_smallCancellation R hR <| Or.inr <| Or.inl ⟨hC4, hT4⟩

-- Proof sketch: specialize the Chapter `5` small-cancellation conjugacy theorem to the
-- `(C(4), T(4))` case. The textbook length-four and symmetrized hypotheses belong to the
-- surrounding knot-group setup, while the canonical owner conclusion is the predicate
-- `HasSolvableConjugacyProblem R`.
/-- Lemma 5-8-4 (2): under the same finite `C(4)` and `T(4)` small-cancellation hypotheses, the
quotient by the normal closure of `R` has solvable conjugacy problem. -/
theorem hasSolvableConjugacyProblem_of_finite_C4_T4
    (hR : R.Finite) (hC4 : C(4)[basis, R]) (hT4 : T(4)[basis, R]) :
    HasSolvableConjugacyProblem R := by
  exact hasSolvableConjugacyProblem_of_finite_smallCancellation R hR <|
    Or.inr <| Or.inl ⟨hC4, hT4⟩

end GroupPresentation

end

/-! ### Theorem_5_8_5 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

section

namespace Group

open Knot

/-!
Primary domain: solvable conjugacy problem for groups of alternating knots.

Layer triage:
- `source-facing`: an alternating knot `K : Knot`, its standard alternating projections, and the
  presentation data extracted from such a projection.
- `core/canonical`: `K.knotGroup` is the canonical group attached to `K`,
  `Group.HasSolvableConjugacyProblem` is the abstract group-level owner for the conclusion, and
  `K.presentationRelators P` and `K.presentationEquiv P` reuse the project's canonical
  presentation owner for the relator set attached to a projection, while
  `GroupPresentation.HasSolvableConjugacyProblem R` together with the Chapter `5` predicates
  `C(4)[basis, R]` and `T(4)[basis, R]` are the owner abstractions for the presentation-level
  input.
- `bridge/view`: Lemma `5-8-3` supplies a standard alternating projection of an alternating knot,
  and Lemma `5-8-1` converts such a projection, via the source-facing `Knot` owner abstraction,
  into finiteness and `(C(4), T(4))` for the canonical presentation already attached to that
  projection.

Domain sampling:
1. `Knot` from Lemma `5-8-1` is the source-facing owner abstraction for knots, projections, and
   the canonical presentation attached to each projection.
2. `exists_alternating_standard_projection` from Lemma `5-8-3` is the source-facing theorem for
   obtaining a standard alternating projection from an alternating knot.
3. `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the chapter bridge from
   explicit standard and alternating projection hypotheses to the canonical finite `(C(4), T(4))`
   properties of the projection-attached presentation data.
4. `GroupPresentation.hasSolvableConjugacyProblem_of_finite_C4_T4` from Lemma `5-8-4` and
   `Group.hasSolvableConjugacyProblem_of_presentation` from Theorem `4-4-8` are the canonical
   presentation-level and abstract group-level owner theorems used in the final upgrade step.

Primitive vs. derived:
- primitive public data: the knot `K` together with its canonically attached group `K.knotGroup`
  and the canonical presentation attached to each projection;
- derived API: the abstract group-level conclusion
  `Group.HasSolvableConjugacyProblem K.knotGroup`.
-/

-- Proof sketch: choose a standard alternating projection of `K` using Lemma `5-8-3`. The bridge
-- theorem `presentation_of_standard_alternating_projection` shows that the canonical presentation
-- attached to that projection is finite and satisfies `C(4)` and `T(4)`.
-- Lemma `5-8-4` gives solvability of the conjugacy problem for that presentation, and the
-- canonical group-level presentation bridge upgrades the conclusion to the knot group itself.
/-- Theorem 5-8-5: if `K` is an alternating knot, then the group of `K` has solvable conjugacy
problem. -/
theorem hasSolvableConjugacyProblem_of_alternatingKnot
    {K : Knot.{u, v}} (hK : K.IsAlternating) :
    HasSolvableConjugacyProblem K.knotGroup := by
  obtain ⟨P, hP_standard, hP_alternating⟩ := K.exists_alternating_standard_projection hK
  obtain ⟨hR, hC4, hT4⟩ :=
    K.presentation_of_standard_alternating_projection hP_standard hP_alternating
  have hPresentation :
      GroupPresentation.HasSolvableConjugacyProblem (K.presentationRelators P) := by
    simpa using
      GroupPresentation.hasSolvableConjugacyProblem_of_finite_C4_T4 (K.presentationRelators P)
        hR hC4 hT4
  exact hasSolvableConjugacyProblem_of_presentation
    (K.presentationRank P) (K.presentationRelators P) (K.presentationEquiv P) hPresentation

end Group

end
