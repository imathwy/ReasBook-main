import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_11_1 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: asphericity of Cayley complexes attached to staggered relator families with a
distinguished ordered generator subset.

Layer triage:
- `source-facing`: the distinguished generator subset `X₀`, the indexed relator family `r`, and
  the staggeredness hypothesis `GroupPresentation.IsStaggeredPresentation X₀ r`.
- `core/canonical`: `CayleyComplex.Coordinates C (PresentedGroup.of : X → PresentedGroup (Set.range r))
  ↥(Set.range r)` is the chosen Cayley-model owner, and `CayleyComplex.Coordinates.IsAspherical`
  is the owner conclusion.
- `bridge/view`: Proposition `3-11-1` itself is the bridge from the source-facing staggeredness
  hypothesis to the canonical asphericity owner for the chosen presentation `P`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` from Proposition `3-9-5` is the chapter owner for
   staggeredness relative to the distinguished subset `X₀`, so the theorem should use it directly
   rather than falling back to the Chapter `2` indexed-generator proxy.
2. `CayleyComplex.Coordinates C (PresentedGroup.of : X → PresentedGroup (Set.range r))
   ↥(Set.range r)` from Proposition `3-4-1` is the owner abstraction for a chosen actual Cayley
   complex of `(X; Set.range r)`.
3. `CayleyComplex.Coordinates.SphericalDiagram`, its reduction API `SphericalDiagram.IsReduced`
   and `SphericalDiagram.ReductionStep`, and the resulting predicate
   `CayleyComplex.Coordinates.IsAspherical` from Definition `3-10-1` are the owner declarations on
   the asphericity side of the proposition.
4. Proposition `3-9-7` supplies the reduced spherical-diagram obstruction that the reduction API
   feeds into in the staggered setting.

Primitive vs. derived:
- primitive data: the distinguished generator subset `X₀`, the indexed relator family `r`, the
  staggeredness witness `hstaggered`, and the chosen standard Cayley presentation `P`;
- derived API: the asphericity conclusion for `P`.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

-- Proof sketch: start with `Δ : CayleyComplex.Coordinates.SphericalDiagram coords` and use the
-- reduction owner from Definition `3-10-1` to delete extremal two-face subdiscs. Once no further
-- reduction is possible, the resulting reduced spherical diagram would contradict Proposition
-- `3-9-7` in the staggered setting. Hence every spherical diagram reduces to the empty one, which
-- is exactly `coords.IsAspherical`.
/-- Proposition 3-11-1: every actual Cayley complex `C(X; Set.range r)` of a staggered
presentation `(X₀; r)` is aspherical. -/
theorem isAspherical_of_staggered_presentation
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates C (PresentedGroup.of : X → PresentedGroup (Set.range r))
      ↥(Set.range r)) :
    CayleyComplex.Coordinates.IsAspherical coords := sorry

end

end GroupPresentation

/-! ### Proposition_3_11_2 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

namespace GroupPresentation

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation style control of the normal closure of a relator family in a
free group.

Layer triage:
- `source-facing`: the normal closure `N` of the relators, the source symmetrized relator family
  `R*`, the “more than one half” segment condition on reduced words, and the conclusion that `N`
  has a basis consisting of conjugates of relators.
- `core/canonical`: `Subgroup.normalClosure R` is the owner for the subgroup `N`,
  `FreeGroupBasis` is the canonical owner for a chosen free basis of `N`, `CyclicWord X` is the
  chapter owner for reduced relators modulo cyclic permutation, `CyclicWord.toConjClasses` is the
  owner bridge from a cyclic word to the represented conjugacy class in the free group,
  `List.IsInfix` and `CyclicWord.HasPart` are the owner predicates for consecutive segments
  of canonical reduced and cyclically reduced words, and
  `IsConj` is the owner for conjugacy in the ambient free group.
- `bridge/view`: the source family `R*` is modeled as the set of cyclic words whose represented
  conjugacy class comes from a relator in `R` or its inverse, and the long-segment condition
  compares a linear segment of `w.toWord` with a cyclic segment of one of those symmetrized
  relators, using the chapter owner predicates for linear and cyclic occurrence.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the subgroup generated normally by the
   relators.
2. `FreeGroupBasis` is the canonical mathlib owner for a chosen free basis of a subgroup.
3. `List.IsInfix` from mathlib is the owner predicate for a segment of a reduced word.
4. `CyclicWord.HasPart` from Proposition `1-7-9` is the existing source-facing owner for a
   cyclic segment of a reduced cyclic word.
5. `CyclicWord.toConjClasses` from Definition `1-4-17` is the bridge from a reduced cyclic word
   to the represented conjugacy class.
6. `IsConj` is mathlib's owner predicate for conjugacy, so the conclusion should speak directly
   in that owner relation rather than through an explicit conjugator witness.

Primitive vs. derived:
- primitive data: the relator set `R`, a nontrivial element `w` of `Subgroup.normalClosure R`,
  and the existence of a segment in `w.toWord` longer than half the cyclic length of some
  symmetrized relator from `R*`, expressed through `List.IsInfix` and `CyclicWord.HasPart`;
- derived API: the existence of a basis of `Subgroup.normalClosure R` whose members are conjugates
  of relators from `R`.
-/

/-- The source symmetrized relator family `R*`, viewed as reduced cyclic words coming from a
relator in `R` or its inverse. -/
def symmetrizedRelatorFamily (R : Set (FreeGroup X)) : Set (CyclicWord X) :=
  { q | ∃ r : FreeGroup X, r ∈ R ∧
      (q.toConjClasses = ConjClasses.mk r ∨ q.toConjClasses = ConjClasses.mk r⁻¹) }

/-- A symmetrized relator from `R*` has the cyclic segment `part`, and its cyclic length is
strictly less than twice the length of `part`. -/
def HasLongSymmetrizedRelatorPart
    (R : Set (FreeGroup X)) (part : List (SignedLetter X)) : Prop :=
  ∃ q ∈ symmetrizedRelatorFamily R,
    q.HasPart part ∧ q.length < 2 * part.length

/-- A symmetrized relator from `R*` has the cyclic segment `part`, and `part` is longer than the
`numerator / denominator` fraction of that relator length. This is the natural fraction-parameter
bridge extending the half-relator owner `HasLongSymmetrizedRelatorPart`. -/
def HasLongSymmetrizedRelatorFractionPart
    (R : Set (FreeGroup X)) (numerator denominator : ℕ) (part : List (SignedLetter X)) : Prop :=
  ∃ q ∈ symmetrizedRelatorFamily R,
    q.HasPart part ∧ numerator * q.length < denominator * part.length

/-- The Chapter `3` half-relator owner is the `1 / 2` specialization of the general
fraction-parameter long-part predicate. -/
theorem hasLongSymmetrizedRelatorPart_iff_hasLongSymmetrizedRelatorFractionPart
    (R : Set (FreeGroup X)) (part : List (SignedLetter X)) :
    HasLongSymmetrizedRelatorPart R part ↔ HasLongSymmetrizedRelatorFractionPart R 1 2 part := by
  constructor
  · rintro ⟨q, hq, hpart, hlength⟩
    exact ⟨q, hq, hpart, by simpa using hlength⟩
  · rintro ⟨q, hq, hpart, hlength⟩
    exact ⟨q, hq, hpart, by simpa using hlength⟩

/-- The nontrivial element `w` of the relator subgroup has a segment longer than half the reduced
word of some symmetrized relator from the source family `R*`. -/
def HasLongRelatorSegment (R : Set (FreeGroup X)) (w : FreeGroup X) : Prop :=
  ∃ part : List (SignedLetter X), part <:+: w.toWord ∧ HasLongSymmetrizedRelatorPart R part

/-- Proposition 3-11-2: if every nontrivial element of the relator subgroup has a reduced-word
segment longer than half the cyclic length of some element of the source symmetrized relator
family `R*`, then the normal closure `N = Subgroup.normalClosure R` has a basis consisting of
conjugates of elements of `R`. -/
-- Proof sketch: use the half-overlap hypothesis to show that the collection of conjugates of
-- relators obtained by repeatedly shortening nontrivial elements of `N` is Nielsen reduced.
-- Then apply the Chapter `1` Nielsen basis criterion to that generating family inside
-- `Subgroup.normalClosure R`, yielding a basis whose elements remain conjugates of relators.
theorem exists_relator_conjugate_basis_of_normalClosure_of_long_relator_segments
    (R : Set (FreeGroup X))
    (hsegment : ∀ ⦃w : FreeGroup X⦄ (_ : w ∈ Subgroup.normalClosure R) (_ : w ≠ 1),
      HasLongRelatorSegment R w) :
    ∃ ι : Type v, ∃ basis : FreeGroupBasis ι (Subgroup.normalClosure R),
      ∀ i : ι, ∃ r : R, IsConj (basis i : FreeGroup X) r := sorry

end GroupPresentation

end

/-! ### Proposition_3_11_3 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: planar Cayley complexes, normal closures of relators, and free bases of those
normal closures.

Layer triage:
- `source-facing`: an actual Cayley complex `C(X; R)` whose geometric realization embeds in the
  plane and fills that plane, together with the conclusion that the relator subgroup `N` has a
  basis made of conjugates of relators.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for a chosen actual Cayley complex
  `C(X; R)`, `TwoComplex.TwoManifoldEmbedding` is the owner for the planar geometric realization,
  `Subgroup.normalClosure R` is the owner for the relator subgroup `N`, `FreeGroupBasis` is the
  canonical owner for a chosen free basis of that subgroup, and Proposition `3-11-2`
  `GroupPresentation.exists_relator_conjugate_basis_of_normalClosure_of_long_relator_segments` is
  the owner theorem for the basis conclusion once the abstract long-segment hypothesis has been
  produced.
- `bridge/view`: the source phrase “filling the plane” is expressed as a property of the chosen
  planar surface embedding, namely that the union of the face images is all of `ℝ²`; the theorem
  below is the bridge from that geometric hypothesis to the abstract owner theorem from
  Proposition `3-11-2`.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for the actual
   Cayley complex attached to `(X; R)`.
2. `TwoComplex.TwoManifoldEmbedding` and `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` are the
   chapter owners for planar realizations of a `2`-complex.
3. `Subgroup.normalClosure R` is the canonical owner for the normal subgroup generated by the
   relators.
4. `GroupPresentation.exists_relator_conjugate_basis_of_normalClosure_of_long_relator_segments`
   from Proposition `3-11-2` is the chapter owner theorem turning the abstract long-segment
   condition into the desired basis conclusion in `Subgroup.normalClosure R`.
5. `FreeGroupBasis` is mathlib's canonical owner for a chosen free basis of a free group.

Primitive vs. derived:
- primitive data: an actual Cayley-complex realization `coords` and the existence of a planar
  embedding of `C` whose face images fill the plane;
- derived API: the abstract long-segment hypothesis of Proposition `3-11-2`, and hence the
  resulting free basis of `Subgroup.normalClosure R` whose basis elements are conjugates of
  relators from `R`.
-/

namespace CayleyComplex.Coordinates

open GroupPresentation

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "N" => Subgroup.normalClosure R

-- Proof sketch: choose a plane-filling embedding from `hfill`, then use that geometric filling
-- hypothesis to show that every nontrivial element of `Subgroup.normalClosure R` has a reduced
-- word segment longer than half of some symmetrized relator. This is exactly the owner
-- hypothesis `HasLongRelatorSegment` required by Proposition `3-11-2`.
private theorem hasLongRelatorSegment_of_fillsPlane
    (coords : PresentationCoordinates C R)
    {embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²}
    (hfill : embedding.FillsPlane)
    {w : FreeGroup X} (hw : w ∈ N) (hw_ne : w ≠ 1) :
    HasLongRelatorSegment R w := by
  sorry

/-- Proposition 3-11-3: if the Cayley complex `C(X; R)` of an actual Cayley-complex realization
is equipped with a planar embedding whose face images fill the plane, then the relator subgroup
`N = Subgroup.normalClosure R` has a free basis consisting of conjugates of relators from `R`. -/
-- Proof sketch: the private bridge theorem above turns the geometric filling hypothesis into the
-- canonical long-segment hypothesis of Proposition `3-11-2`, so the conclusion follows by a
-- direct application of that owner theorem.
theorem normalClosure_has_basis_of_relatorConjugates_of_fillsPlane
    (coords : PresentationCoordinates C R)
    (embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²)
    (hfill : embedding.FillsPlane) :
    ∃ ι : Type v, ∃ basis : FreeGroupBasis ι N,
      ∀ i : ι, ∃ r : R, IsConj (basis i : FreeGroup X) r := by
  refine exists_relator_conjugate_basis_of_normalClosure_of_long_relator_segments R ?_
  intro w hw hw_ne
  exact hasLongRelatorSegment_of_fillsPlane coords hfill hw hw_ne

end CayleyComplex.Coordinates

/-! ### Proposition_3_11_4 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: staggered presentations, interval support, and Peiffer reductions of identities
among positive relator conjugates.

Layer triage:
- `source-facing`: a finite formal product of conjugates `u * r * u⁻¹` of relators in a staggered
  presentation, together with the proposition that if the total product only involves special
  generators from an interval `[xₐ, x_b]`, then Peiffer transformations can rewrite the formal
  product so that every relator term itself lies in that interval.
- `core/canonical`: `GroupPresentation.IsStaggeredPresentation` and
  `GroupPresentation.SupportedOnDistinguishedInterval` from Proposition `3-9-5`, the free-group
  list owner `List (FreeGroup X)`, `IsConj` as the owner for conjugacy in the free group, and
  `GroupPresentation.PeifferStep` with its reflexive transitive closure from Proposition `3-10-4`.
- `bridge/view`: the proof-support normal-closure consequence is phrased through the canonical
  owner set `relatorsSupportedOnDistinguishedInterval`, but the main proposition remains
  source-facing over the indexed relator family `r`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` is already the chapter owner for the source phrase
   “`(X; R)` is a staggered presentation, as in (9.5)”.
2. `GroupPresentation.SupportedOnDistinguishedInterval` is the owner for the statement that only
   distinguished generators in `[xₐ, x_b]` occur in a word or relator.
3. `IsConj` is mathlib's canonical owner for “is a conjugate of”, so the source-facing statement
   should quantify only the relator index `j` and assert `IsConj p (r j)` rather than introduce a
   bespoke witness package.
4. `GroupPresentation.PeifferStep` and `Relation.ReflTransGen` are the canonical owners for
   “carried into by Peiffer transformations”.
5. `Subgroup.normalClosure` remains the owner for the ambient relator subgroup consequence that the
   transformed product still lies in the interval-supported normal closure.

Primitive vs. derived:
- primitive data: the indexed relator family `r`, the list `π` of positive relator conjugates, and
  the interval `[xₐ, x_b]`;
- derived API: the termwise list conditions expressed through the list owner `List.Forall`, the
  Peiffer-chain product invariance, and the normal-closure consequence phrased via
  `relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b`.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

open Subgroup

-- Proof sketch: each elementary Peiffer step from Proposition `3-10-4` preserves the list
-- product; compose those equalities along the reflexive-transitive closure.
private theorem prod_eq_of_peifferTransformations
    {π π' : List (FreeGroup X)}
    (h : Relation.ReflTransGen PeifferStep π π') :
    π.prod = π'.prod := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl _ => rfl
  | @single π π' hstep =>
      rcases hstep with hswap | hswap | hdelete | hinsert
      · exact (List.prod_eq_of_isAdjacentConjugatingSwap hswap).symm
      · exact List.prod_eq_of_isAdjacentConjugatingSwap hswap
      · rcases hdelete with ⟨left, right, a, rfl, rfl⟩
        simp [List.prod_append]
      · rcases hinsert with ⟨left, right, a, rfl, rfl⟩
        simp [List.prod_append]
  | @trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem mem_normalClosure_of_intervalSupportedPositiveRelatorConjugate
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X)
    {p : FreeGroup X}
    (hp : ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j)) :
    p ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := by
  let N := normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b)
  rcases hp with ⟨j, hj, hpconj⟩
  have hrj : r j ∈ relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b := by
    exact ⟨⟨j, rfl⟩, hj⟩
  have hrj_mem : r j ∈ N := by
    exact Subgroup.subset_normalClosure hrj
  rcases isConj_iff.mp hpconj with ⟨c, hc⟩
  have hconj : c⁻¹ * r j * c ∈ N := by
    simpa [N, inv_inv] using
      ((Subgroup.normalClosure_normal
        (s := relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b)).conj_mem
          (n := r j) hrj_mem c⁻¹)
  have hp_eq : p = c⁻¹ * r j * c := by
    calc
      p = c⁻¹ * (c * p * c⁻¹) * c := by simp [mul_assoc]
      _ = c⁻¹ * r j * c := by rw [hc]
  simpa [hp_eq] using hconj

-- Proof sketch: each list entry is a conjugate of a relator already belonging to the
-- interval-restricted relator family, hence each term lies in its normal closure; then use
-- subgroup closure under multiplication to conclude that the full list product lies there as well.
private theorem prod_mem_normalClosure_of_intervalSupportedPositiveRelatorConjugates
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X)
    {π : List (FreeGroup X)}
    (hπ : π.Forall
      (fun p ↦ ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j))) :
    π.prod ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := by
  rw [List.forall_iff_forall_mem] at hπ
  induction π with
  | nil =>
      simp
  | cons p π ih =>
      have hp : ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j) :=
        hπ p (by simp)
      have hπ' :
          ∀ q ∈ π, ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj q (r j) := by
        intro q hq
        exact hπ q (by simp [hq])
      have hp_mem :
          p ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) :=
        mem_normalClosure_of_intervalSupportedPositiveRelatorConjugate X₀ r xₐ x_b hp
      simpa using
        Subgroup.mul_mem
          (normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b))
          hp_mem (ih hπ')

-- Proof sketch: use the interval-control statement from Proposition `3-9-5` on the total product
-- `π.prod`, then apply Peiffer reductions to rewrite the formal product until every relator term
-- itself is supported in `[xₐ, x_b]`. The parenthetical product-preservation claim follows from
-- `prod_eq_of_peifferTransformations`.
/-- Proposition 3-11-4: if `(X₀; r)` is staggered, every term of a formal product `π` is a
positive relator conjugate, and the total product `π.prod` contains distinguished generators only
from the interval `[xₐ, x_b]`, then Peiffer transformations carry `π` to a formal product all of
whose relator terms are supported in that same interval. -/
theorem exists_peiffer_reduction_to_interval_supported_positive_relators
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    (xₐ x_b : X) (π : List (FreeGroup X))
    (hπ : π.Forall (fun p ↦ ∃ j, IsConj p (r j)))
    (hsupp : SupportedOnDistinguishedInterval X₀ xₐ x_b π.prod) :
    ∃ π' : List (FreeGroup X),
      Relation.ReflTransGen PeifferStep π π' ∧
        π'.Forall
          (fun q ↦ ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj q (r j)) := sorry

end

end GroupPresentation
