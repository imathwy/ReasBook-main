

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_8_1 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

open MulAction TwoComplex

/-!
Primary domain: NEC groups, Fuchsian complexes, and regular actions on geometric faces.

Layer triage:
- `source-facing`: a group `G` together with a planar simply connected connected Fuchsian complex
  on which `G` acts regularly on geometric faces.
- `core/canonical`: `FuchsianComplex` is the chapter owner for the actual `2`-complex together
  with the action by automorphisms, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`,
  `TwoComplex.EmbedsInPlane`, and `TwoComplex.AutAction.geometricFaceMulAction` are the owner
  predicates and constructions for the geometric hypotheses and the induced action on geometric
  faces; `MulAction.IsPretransitive` and `IsCancelSMul` are the standard owners for transitivity
  and freeness of that action.
- `bridge/view`: `TwoComplex.AutAction.IsRegularOnGeometricFaces` below packages the textbook
  phrase “regular on geometric faces” in terms of those canonical group-action owners.

Domain sampling:
1. `TwoComplex.AutAction` from Proposition `3-7-1` is the chapter owner for an action of `G` on
   a `2`-complex by automorphisms.
2. `FuchsianComplex` from Proposition `3-7-1` is the owner for the underlying complex together
   with that action.
3. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
   `TwoComplex.EmbedsInPlane` are the direct owner predicates for the connected, simply connected,
   and planar hypotheses used in Proposition `3-7-3`.
4. `MulAction.IsPretransitive`, `IsCancelSMul`, and
   `isCancelSMul_iff_stabilizer_eq_bot` are the canonical owner notions for a transitive free
   action and its stabilizer reformulation.

Primitive vs. derived:
- primitive data: the actual Fuchsian complex;
- derived API: the induced geometric-face action and the regularity property of that action.
-/

namespace TwoComplex.AutAction

variable {G : Type u} [Group G] {C : TwoComplex}

/-- The induced action on geometric faces is regular when the geometric-face set is nonempty and
the action is transitive with trivial stabilizers, equivalently transitive and free. -/
def IsRegularOnGeometricFaces (ρ : TwoComplex.AutAction G C) : Prop :=
  letI := ρ.geometricFaceMulAction
  Nonempty (GeometricFace C) ∧ IsPretransitive G (GeometricFace C) ∧
    IsCancelSMul G (GeometricFace C)

/-- The stabilizer formulation of regularity on geometric faces is a companion to the canonical
`Nonempty ∧ IsPretransitive ∧ IsCancelSMul` owner shape. -/
theorem isRegularOnGeometricFaces_iff_pretransitive_and_stabilizer_eq_bot
    (ρ : TwoComplex.AutAction G C) :
    letI := ρ.geometricFaceMulAction
    ρ.IsRegularOnGeometricFaces ↔
      Nonempty (GeometricFace C) ∧
      IsPretransitive G (GeometricFace C) ∧
        ∀ D : GeometricFace C, stabilizer G D = ⊥ := by
  letI := ρ.geometricFaceMulAction
  constructor
  · rintro ⟨hfaces, htrans, hfree⟩
    exact ⟨hfaces, htrans, fun D ↦ IsCancelSMul.stabilizer_eq_bot D⟩
  · rintro ⟨hfaces, htrans, hstab⟩
    exact ⟨hfaces, htrans, (isCancelSMul_iff_stabilizer_eq_bot).2 hstab⟩

/-- Unfolding `IsRegularOnGeometricFaces` gives transitivity on geometric faces together with
pointwise triviality of geometric-face stabilizers, and in particular a nonempty face set. -/
theorem isRegularOnGeometricFaces_iff (ρ : TwoComplex.AutAction G C) :
    letI := ρ.geometricFaceMulAction
    ρ.IsRegularOnGeometricFaces ↔
      Nonempty (GeometricFace C) ∧
      (∀ D E : GeometricFace C, ∃ g : G, g • D = E) ∧
        ∀ ⦃g : G⦄, g ≠ 1 → ∀ D : GeometricFace C, g • D ≠ D := by
  letI := ρ.geometricFaceMulAction
  constructor
  · rintro ⟨hfaces, htrans, hfree⟩
    refine ⟨hfaces, ?_, ?_⟩
    · intro D E
      simpa using (exists_smul_eq G D E)
    · intro g hg D hD
      have : g = 1 := by
        exact IsCancelSMul.eq_one_of_smul (by simpa using hD)
      exact hg this
  · rintro ⟨hfaces, htrans, hfix⟩
    refine ⟨hfaces, ⟨fun D E ↦ by simpa using htrans D E⟩, ?_⟩
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro g D hD
    by_contra hg
    exact hfix hg D (by simpa using hD)

end TwoComplex.AutAction

/-- Definition 3-8-1: an NEC group is a group admitting a connected simply connected planar
Fuchsian complex whose action is regular on a nonempty set of geometric faces. -/
class IsNECGroup (G : Type u) [Group G] : Prop where
  /-- An NEC group admits a planar simply connected connected Fuchsian complex with a regular
  geometric-face action of `G`. -/
  exists_fuchsianComplex :
    ∃ K : FuchsianComplex.{u, v} G,
      Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton) ∧
        TwoComplex.IsSimplyConnected K.complex ∧
        K.complex.EmbedsInPlane ∧
        K.action.IsRegularOnGeometricFaces

/-! ### Definition_3_8_2 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

/-
Primary domain: Fuchsian complexes, geometric-edge actions, and reflections.

Layer triage:
- `source-facing`: a nontrivial element acting as a reflection in a geometric edge of a Fuchsian
  complex.
- `core/canonical`: `OneComplex.GeometricEdge` is the owner for geometric edges,
  `TwoComplex.AutAction.geometricEdgePerm` is the owner for the induced action on those edges, and
  `FuchsianComplex.WithoutReflections`,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
  `TwoComplex.EmbedsInPlane` are the owner predicates asserting the geometric-edge freeness and
  ambient connected/simply connected/planar hypotheses used below.
- `bridge/view`: the oriented-edge phrase “the geometric edge represented by `e`” is a companion
  representative-level view of the intrinsic fixed-geometric-edge condition.

Domain sampling:
1. `OneComplex.GeometricEdge` from Definition `3-2-1` is the canonical carrier for geometric
   edges, so a reflection should be phrased by fixing one of these quotient edges rather than by
   primitive case-splitting on an oriented representative.
2. `TwoComplex.AutAction.geometricEdgePerm` from Proposition `3-7-1` is the canonical induced
   action on geometric edges and already packages the “send `e` to `e` or `e⁻¹`” quotient
   relation.
3. `FuchsianComplex.WithoutReflections` from Proposition `3-7-1` is the project owner predicate
   for the absence of nontrivial fixed geometric edges.
4. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
   `TwoComplex.EmbedsInPlane` are the direct owner predicates for the geometric hypotheses imported
   from Proposition `3-7-3`.

Primitive vs. derived:
- primitive public data here: none beyond the existing `FuchsianComplex` action;
- derived API here: the reflection predicates and the representative-level equivalence for an
  oriented edge.
-/

namespace FuchsianComplex

variable {G : Type u} [Group G]
variable (K : FuchsianComplex G)

local notation "Edge" => OneComplex.Edge K.complex.skeleton
local notation "GeometricEdge" => OneComplex.GeometricEdge K.complex.skeleton

/-- Definition 3-8-2: a nontrivial element is a reflection in a geometric edge when the action
fixes that geometric edge. -/
def IsReflectionIn (g : G) (e : GeometricEdge) : Prop :=
  g ≠ 1 ∧ (K.action g).geometricEdgePerm e = e

/-- The owner-level geometric-edge formulation is equivalent to the representative-level condition
that the oriented edge is sent to itself or to its reverse. -/
theorem isReflectionIn_iff (g : G) (e : Edge) :
    K.IsReflectionIn g ⟦e⟧ ↔
      g ≠ 1 ∧ ((K.action g).edgePerm e = e ∨ (K.action g).edgePerm e = e⁻¹) := by
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    exact Quotient.exact hfix
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, Quotient.sound hfix⟩

/-- An element is a reflection for the action when it preserves some geometric edge. -/
def IsReflection (g : G) : Prop :=
  ∃ e : GeometricEdge, K.IsReflectionIn g e

/-- The chapter owner predicate `WithoutReflections` is exactly the statement that no element is a
reflection in any geometric edge. -/
theorem withoutReflections_iff_forall_not_isReflectionIn :
    K.WithoutReflections ↔ ∀ g : G, ∀ e : GeometricEdge, ¬ K.IsReflectionIn g e := by
  constructor
  · intro h g e
    rintro ⟨hg, hfix⟩
    exact h hg e hfix
  · intro h g hg e hfix
    exact h g e ⟨hg, hfix⟩

/-- The intrinsic geometric-edge definition of a reflection is equivalent to the source-level
existence of an oriented edge sent to itself or to its reverse. -/
theorem isReflection_iff (g : G) :
    K.IsReflection g ↔
      ∃ e : Edge, g ≠ 1 ∧ ((K.action g).edgePerm e = e ∨ (K.action g).edgePerm e = e⁻¹) := by
  constructor
  · rintro ⟨e, he⟩
    rcases Quotient.exists_rep e with ⟨e, rfl⟩
    exact ⟨e, (K.isReflectionIn_iff g e).1 he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟦e⟧, (K.isReflectionIn_iff g e).2 he⟩

/-- The owner predicate `WithoutReflections` is equivalent to the absence of reflections. -/
theorem withoutReflections_iff_forall_not_isReflection :
    K.WithoutReflections ↔ ∀ g : G, ¬ K.IsReflection g := by
  simpa [IsReflection] using K.withoutReflections_iff_forall_not_isReflectionIn

/-- A Fuchsian complex fails to be without reflections exactly when some group element is a
reflection. -/
theorem not_withoutReflections_iff_exists_isReflection :
    ¬ K.WithoutReflections ↔ ∃ g : G, K.IsReflection g := by
  rw [K.withoutReflections_iff_forall_not_isReflection]
  simp

/-- A reflection in an edge is necessarily an involution. -/
-- Proof sketch: an element fixing a geometric edge of the planar complex reverses the two local
-- sides of that edge, so its square fixes the adjacent geometric faces. Regularity on geometric
-- faces then forces that square to be the identity element.
theorem sq_eq_one_of_isReflectionIn
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton))
    (hsimply : TwoComplex.IsSimplyConnected K.complex)
    (hplanar : K.complex.EmbedsInPlane)
    (hreg : K.action.IsRegularOnGeometricFaces)
    {g : G} {e : GeometricEdge}
    (hg : K.IsReflectionIn g e) :
    g ^ 2 = 1 := sorry

end FuchsianComplex

/-! ### Proposition_3_8_3 (from Items/Chap03) -/
universe u v w x

set_option autoImplicit false

noncomputable section

/-!
Primary domain: NEC groups and presentations with reflection cycles.

Layer triage:
- `source-facing`: a chosen finite presentation of an NEC group with finitely many ordinary
  generators `X`, reflection generators indexed by a disjoint union of cyclically ordered
  boundary blocks `J_j`, and relators of the three forms described in Proposition `3-8-3`.
- `core/canonical`: `PresentedGroup R` is the owner for the group defined by a specified relator
  set, `Finite X` is the canonical finite-generator owner for the ordinary generator type, and
  `IsStrictlyQuadraticSet` is the chapter owner for the final “each generator of `X` occurs
  exactly twice” condition on the auxiliary words `a_{jh}` and `s_k`.
- `bridge/view`: the helper definitions below turn the source formulas for the relators
  `x_{jh}²`, `t_{jh}^{m_{jh}}`, and `s_k^{m_k}` into a single canonical relator set for
  `PresentedGroup`.

Domain sampling:
1. `IsNECGroup` from Definition `3-8-1` is the owner predicate for the ambient NEC-group
   hypothesis.
2. `PresentedGroup R` from Chapter `2` is the canonical owner for a concrete presentation.
3. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the established chapter owner for the
   “exactly twice” incidence condition on a finite word system.

Primitive vs. derived:
- primitive public data: the finite ordinary generator type `X`, the boundary-component index
  type, the positive lengths `n_j`, the words `a_{jh}` and `s_k`, the multiplicities `m_{jh}` and
  `m_k`, and the presentation equivalence to `G`;
- derived API: the canonical sigma-type reflection index `J = ⨿_j J_j`, the relator set
  `R₀ ∪ R₁ ∪ R₂`, and the combined strict-quadratic auxiliary word system.
-/

/-- The cyclic successor on one boundary block `J_j`. -/
private def necBoundaryNext {B : Type w} (boundaryLength : B → ℕ+) (j : B) :
    Fin (boundaryLength j : ℕ) → Fin (boundaryLength j : ℕ)
  | h => Fin.ofNat (boundaryLength j : ℕ) (h.1 + 1)

/-- Regard a word on the ordinary generators `X` as a word on the enlarged alphabet
`X ⊕ J`. -/
private def necOrdinaryWordInclusion {X : Type v} {B : Type w} (boundaryLength : B → ℕ+) :
    FreeGroup X → FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  FreeGroup.map Sum.inl

/-- The reflection generator corresponding to one index in the disjoint union `J = ⨿_j J_j`. -/
private def necReflectionGenerator {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    (r : Σ j : B, Fin (boundaryLength j : ℕ)) :
    FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  FreeGroup.of (.inr r)

/-- The textbook word `t_{jh} = x_{jh} a_{jh} x_{j,h+1} a_{jh}^{-1}` attached to one boundary
reflection. -/
private def necBoundaryElement {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (j : B) (h : Fin (boundaryLength j : ℕ)) :
    FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  necReflectionGenerator boundaryLength ⟨j, h⟩ *
    necOrdinaryWordInclusion boundaryLength (connectorWord j h) *
    necReflectionGenerator boundaryLength ⟨j, necBoundaryNext boundaryLength j h⟩ *
    (necOrdinaryWordInclusion boundaryLength (connectorWord j h))⁻¹

/-- The auxiliary word system formed by all words `a_{jh}` together with all words `s_k`. -/
def necOrdinaryWordSystem {X : Type v} {B : Type w} [Finite B] (boundaryLength : B → ℕ+)
    {K : Type x} [Finite K]
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (interiorWord : K → FreeGroup X) : Finset (FreeGroup X) := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype K := Fintype.ofFinite K
  exact
    (Finset.univ.image fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦ connectorWord r.1 r.2) ∪
      Finset.univ.image interiorWord

/-- The relator set `R₀ ∪ R₁ ∪ R₂` of the NEC presentation determined by the given data. -/
def necRelatorSet {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    {K : Type x}
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (boundaryMultiplicity : (j : B) → Fin (boundaryLength j : ℕ) → ℕ+)
    (interiorWord : K → FreeGroup X)
    (interiorMultiplicity : K → ℕ+) :
    Set (FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ))) :=
  Set.range (fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦
      necReflectionGenerator boundaryLength r ^ (2 : ℕ)) ∪
    Set.range (fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦
      necBoundaryElement boundaryLength connectorWord r.1 r.2 ^
        (boundaryMultiplicity r.1 r.2 : ℕ)) ∪
    Set.range (fun k : K ↦
      necOrdinaryWordInclusion boundaryLength (interiorWord k) ^ (interiorMultiplicity k : ℕ))

variable {G : Type u} [Group G]

-- Proof sketch: start from the planar simply connected `2`-complex with regular face action given
-- by the NEC-group structure. Choose representatives for the boundary cycles of the quotient
-- orbifold, record the edge-reflection generators `x_{jh}`, read the conjugating words `a_{jh}`
-- from connecting paths between consecutive reflections, and collect the remaining elliptic
-- relators as the words `s_k^{m_k}`. The resulting relator family presents `G`, and the planar
-- incidence argument shows that the combined auxiliary word system is strictly quadratic.
/-- Proposition 3-8-3: every NEC group admits a finite presentation
`G = (X ∪ J; R₀ ∪ R₁ ∪ R₂)` in
which `J` is a disjoint union of ordered blocks `J_j = (x_{j1}, …, x_{jn_j})`, `R₀` consists of
the involution relators `x_{jh}²`, `R₁` consists of the power relators
`t_{jh}^{m_{jh}} = (x_{jh} a_{jh} x_{j,h+1} a_{jh}^{-1})^{m_{jh}}`, `R₂` consists of the power
relators `s_k^{m_k}` on words in `X`, and the combined family of words `a_{jh}` and `s_k` is
strictly quadratic over `X`. -/
theorem exists_necPresentation_of_isNECGroup (hG : IsNECGroup G) :
    ∃ (X : Type v) (_ : Finite X)
      (BoundaryComponent : Type w) (_ : Finite BoundaryComponent)
      (boundaryLength : BoundaryComponent → ℕ+)
      (InteriorRelator : Type x) (_ : Finite InteriorRelator)
      (connectorWord : (j : BoundaryComponent) → Fin (boundaryLength j : ℕ) → FreeGroup X)
      (boundaryMultiplicity : (j : BoundaryComponent) → Fin (boundaryLength j : ℕ) → ℕ+)
      (interiorWord : InteriorRelator → FreeGroup X)
      (interiorMultiplicity : InteriorRelator → ℕ+)
      (e :
        PresentedGroup
            (necRelatorSet boundaryLength connectorWord boundaryMultiplicity interiorWord
              interiorMultiplicity) ≃* G),
      IsStrictlyQuadraticSet (necOrdinaryWordSystem boundaryLength connectorWord interiorWord) :=
  sorry
