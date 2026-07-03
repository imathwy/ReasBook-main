import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_7_1 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: recursive presentations of finitely generated groups and Higman-style embedding
theorems.

Layer triage:
- `source-facing`: a finitely generated group `G`, the textbook condition that `G` admit a
  recursive presentation, and the textbook conclusion that `G` embeds in some finitely presented
  group.
- `core/canonical`: `Group.FG G`, `Group.IsFinitelyPresented H`,
  `GroupPresentation.IsRecursive R`, the presentation bridge `PresentedGroup R ≃* G`, and
  injective homomorphisms `G →* H`.
- `bridge/view`: the textbook phrase “`G` can be recursively presented” is recorded by the group
  owner predicate `Group.IsRecursivelyPresented`, built directly from a finite-generator recursive
  presentation, while the embedding conclusion is stated in the chapter's direct existential style.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's owner predicate for finite presentability of an
   abstract group.
2. The surrounding chapter expresses embeddings source-faithfully as a homomorphism together with
   `Function.Injective`, so the group-level owner should package exactly that datum rather than a
   second wrapper object.
3. `GroupPresentation.IsRecursive R` is the project's owner predicate for recursive relator sets.
4. `PresentedGroup R ≃* G` from Definition `2-1-1` is the canonical bridge from a presentation to
   an abstract group.

Primitive vs. derived:
- primitive public data for recursive presentability: a finite generator count `n`, a relator set
  `R : Set (FreeGroup (Fin n))`, a presentation equivalence `PresentedGroup R ≃* G`, and a proof
  that `R` is recursive;
- derived API: the abstract group-level predicate `Group.IsRecursivelyPresented`, its direct
  constructor from an explicit presentation, the induced finite-generation instance
  `IsRecursivelyPresented.fg`, and the owner-side embedding consequence
  `IsRecursivelyPresented.exists_finitelyPresented_embedding`.
-/

/-- A group is recursively presented when it admits a presentation on finitely many generators
whose relator set is recursive. -/
def IsRecursivelyPresented (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Set (FreeGroup (Fin n))) (_ : PresentedGroup R ≃* G),
    GroupPresentation.IsRecursive R

variable {G : Type u} [Group G]

/-- An explicit recursive presentation on finitely many generators induces the abstract owner
predicate `IsRecursivelyPresented G`. -/
theorem isRecursivelyPresented_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.IsRecursive R) :
    IsRecursivelyPresented G := by
  exact ⟨n, R, P, hR⟩

namespace IsRecursivelyPresented

/-- A recursively presented group is finitely generated, because its chosen presentation has only
finitely many generators. -/
theorem fg (hG : IsRecursivelyPresented G) : FG G := by
  rcases hG with ⟨n, R, P, _⟩
  letI : FG (PresentedGroup R) := PresentedGroup.instFG R
  exact Group.fg_of_surjective P.surjective

end IsRecursivelyPresented

variable (G : Type u) [Group G] [FG G]

/-- Theorem 4-7-1 (Higman Embedding Theorem): a finitely generated group embeds in some finitely
presented group if and only if it is recursively presented. -/
-- Proof sketch: if `G` embeds in a finitely presented group `H`, choose a finite presentation of
-- `H` and recursively enumerate the words whose values lie in the embedded copy of `G`; pulling
-- those relators back through the embedding yields a recursive presentation of `G`. Conversely,
-- Higman's construction uses iterated HNN extensions and amalgamated products to embed any
-- finitely generated recursively presented group in a finitely presented group.
theorem exists_finitelyPresented_embedding_iff_isRecursivelyPresented :
    (∃ (H : Type u) (_ : Group H) (_ : IsFinitelyPresented H) (f : G →* H),
      Function.Injective f) ↔ IsRecursivelyPresented G := sorry

namespace IsRecursivelyPresented

/-- A recursively presented group embeds in some finitely presented group. The ambient finite
generation required by Theorem `4-7-1` is derived from the recursive presentation itself. -/
theorem exists_finitelyPresented_embedding {G : Type u} [Group G]
    (hG : IsRecursivelyPresented G) :
    ∃ (H : Type u) (_ : Group H) (_ : IsFinitelyPresented H) (f : G →* H),
      Function.Injective f := by
  letI : FG G := hG.fg
  exact (exists_finitelyPresented_embedding_iff_isRecursivelyPresented G).2 hG

end IsRecursivelyPresented

end Group

/-! ### Theorem_4_7_2 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algorithmic group theory in the Higman embedding section.

Layer triage:
- `source-facing`: the existence of a finitely presented group with unsolvable word problem.
- `core/canonical`: `Group.IsFinitelyPresented` is the abstract owner for finite presentability,
  and `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the chapter owner for solvability of
  the word problem.
- `bridge/view`: `Group.IsRecursivelyPresented` and its owner-side corollary
  `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` package
  Higman's embedding theorem, so the recursive-presentation construction in the textbook stays
  proof-level bridge data rather than becoming a second public wrapper here.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
2. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the chapter's abstract owner predicate
   for solvable word problem.
3. `Group.IsRecursivelyPresented` from Theorem `4-7-1` is the chapter owner abstraction for the
   recursive-presentation hypothesis used in Higman's theorem.
4. `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` is the
   owner-side bridge from recursive presentability to embedding in a finitely presented group.

Primitive vs. derived:
- primitive public data: only the ambient witness group `H`;
- derived owner-side properties: finite presentability of `H` and failure of
  `Group.HasSolvableWordProblem H`.
-/

/-- Theorem 4-7-2: there exists a finitely presented group with unsolvable word problem. -/
-- Proof sketch: choose a recursively enumerable nonrecursive set `S ⊆ ℕ+` and form the standard
-- recursively presented group whose relators force `a⁻ⁿ * b * aⁿ = c⁻ⁿ * d * cⁿ` exactly for
-- `n ∈ S`. Membership in `S` reduces to the word problem in that group, so the word problem is
-- unsolvable. Applying
-- `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` embeds
-- this finitely generated recursively presented group in a finitely presented group, and
-- solvability of the ambient word problem would restrict to the embedded subgroup, contradiction.
theorem exists_finitelyPresented_not_hasSolvableWordProblem :
    ∃ (H : Type u) (_ : Group H),
      IsFinitelyPresented H ∧ ¬ HasSolvableWordProblem H := sorry

end Group

/-! ### Theorem_4_7_3 (from Items/Chap04) -/
universe u v

set_option autoImplicit false

namespace Group

/-!
Primary domain: universal embedding theorems for recursively presented groups in the Higman
embedding section.

Layer triage:
- `source-facing`: the existence of a finitely presented group `H` into which every recursively
  presented group embeds.
- `core/canonical`: `IsRecursivelyPresented` from Theorem `4-7-1`, `IsFinitelyPresented`, and
  injective homomorphisms `G →* H`.
- `bridge/view`: the textbook proof passes through a countable free product of all finite
  presentations and then Higman's embedding theorem, but those presentation-level choices remain
  proof data rather than public API in this item.

Domain sampling:
1. `IsRecursivelyPresented` from Theorem `4-7-1` is the chapter's owner abstraction for the
   hypothesis “`G` is recursively presented”.
2. `IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` is the
   canonical per-group bridge from that owner predicate to embeddability in a finitely presented
   group.
3. `IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
4. Theorems `4-3-1` and `4-7-2` confirm the chapter's source-facing style for embedding theorems:
   quantify over an ambient witness group together with a homomorphism and `Function.Injective`,
   rather than introducing a separate public wrapper for embedding data.

Primitive vs. derived:
- primitive public data: only the ambient witness group `H`;
- derived owner-side data: finite presentability of `H` and, for each recursively presented group
  `G`, an embedding `G →* H`.
-/

/-- Theorem 4-7-3: there exists a finitely presented group containing an embedded copy of every
recursively presented group. -/
-- Proof sketch: enumerate all finite presentations and take their free product, obtaining a
-- recursively presented group that contains a copy of every finitely presented group. Apply the
-- two-generator embedding theorem to place that countable group inside a recursively presented
-- two-generator group, then apply Higman's embedding theorem to embed the latter in a finitely
-- presented group `H`. Every recursively presented group embeds in some finitely presented group
-- by Theorem `4-7-1`, and those finitely presented groups already embed in `H`.
theorem exists_finitelyPresented_group_embedding_all_recursivelyPresented_groups :
    ∃ (H : Type u) (_ : Group H),
      IsFinitelyPresented H ∧
        ∀ {G : Type v} [Group G], IsRecursivelyPresented G →
          ∃ (f : G →* H), Function.Injective f := sorry

end Group

/-! ### Definition_4_7_5 (from Items/Chap04) -/
universe u

set_option autoImplicit false

/-!
Primary domain: Diophantine subsets of integer lattices and their polynomial presentations.

Layer triage:
- `source-facing`: subsets `S ⊆ ℤⁿ` and the textbook definition that membership in `S` is
  equivalent to solvability of one integer polynomial equation.
- `core/canonical`: `MvPolynomial` and `MvPolynomial.eval` are mathlib's owner abstractions for
  multivariate integer polynomials and their evaluation on integer tuples.
- `bridge/view`: no extra public bridge is needed; the source-facing definition can speak directly
  in the language of the canonical polynomial owner.

Domain sampling:
1. `MvPolynomial` is the canonical owner for multivariate polynomials with coefficients in `ℤ`.
2. `MvPolynomial.eval` is the canonical evaluation map at a tuple of integer values.
3. `Dioph` from `Mathlib.NumberTheory.Dioph` is mathlib's owner notion for the natural-valued
   Diophantine predicate; since the textbook item is explicitly about subsets of `ℤⁿ`, the main
   declaration here stays source-facing rather than collapsing to that natural-coded owner.
4. `Dioph.reindex_dioph` shows the upstream API is organized around variable reindexing, so the
   polynomial witness should remain primitive data and the existential Diophantine property should
   be derived from it.

Primitive vs. derived:
- primitive source data: the subset `S ⊆ ℤⁿ` and a polynomial witness `P`;
- derived API: the existential predicate `S.IsDiophantine`;
- the solvability condition for `P` is stated directly via `MvPolynomial.eval`, rather than
  packaged as a second public owner.
-/

namespace Set

/-- Definition 4-7-5: a subset `S ⊆ ℤⁿ` is Diophantine when some integer polynomial enumerates
`S`. -/
def IsDiophantine {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∃ m : ℕ, ∃ p : MvPolynomial (Fin n ⊕ Fin m) ℤ,
    ∀ s : Fin n → ℤ, s ∈ S ↔ ∃ y : Fin m → ℤ, p.eval (Sum.elim s y) = 0

/-- A subset of `ℤⁿ` is Diophantine exactly when it is enumerated by some integer polynomial in
the displayed and auxiliary variables. -/
theorem isDiophantine_iff {n : ℕ} (S : Set (Fin n → ℤ)) :
    S.IsDiophantine ↔
      ∃ m : ℕ, ∃ p : MvPolynomial (Fin n ⊕ Fin m) ℤ,
        ∀ s : Fin n → ℤ, s ∈ S ↔ ∃ y : Fin m → ℤ, p.eval (Sum.elim s y) = 0 :=
  Iff.rfl

end Set

/-! ### Theorem_4_7_7 (from Items/Chap04) -/
set_option autoImplicit false

open Nat.Partrec (Code)

/-!
Primary domain: computability-theoretic subsets of the positive integers in the Higman embedding
section.

Layer triage:
- `source-facing`: a subset `S ⊆ ℕ+` that is recursively enumerable but not recursive.
- `core/canonical`: `REPred` and `ComputablePred` are mathlib's owner predicates for recursively
  enumerable and computable membership predicates, while
  `ComputablePred.halting_problem_re` / `ComputablePred.halting_problem` are the canonical
  existence and noncomputability theorems used here.
- `bridge/view`: `Denumerable.equiv₂ Code ℕ+` transports the halting predicate from
  `Nat.Partrec.Code` to a source-facing subset of positive integers.

Domain sampling:
1. `REPred` is mathlib's owner predicate for recursively enumerable subsets of a `Primcodable`
   type.
2. `ComputablePred` is the owner predicate for recursive/computable membership.
3. `ComputablePred.halting_problem_re` and `ComputablePred.halting_problem` provide the canonical
   r.e.-but-noncomputable predicate.
4. `Denumerable.equiv₂` together with `Computable.equiv₂` is the canonical bridge for moving that
   predicate from `Nat.Partrec.Code` to `ℕ+`.

Primitive vs. derived:
- primitive public data: only the witness subset `S : Set ℕ+`;
- derived owner-side properties: recursive enumerability and failure of computability of the
  membership predicate of `S`.
-/

/-- Theorem 4-7-7: there exists a recursively enumerable non-recursive set of positive integers.
In the canonical owner language, this is an r.e. but noncomputable subset of `ℕ+`. -/
theorem exists_recursivelyEnumerable_not_recursive_set_positiveIntegers :
    ∃ S : Set ℕ+, REPred (· ∈ S) ∧ ¬ ComputablePred (· ∈ S) := by
  let e : ℕ+ ≃ Code := Denumerable.equiv₂ _ _
  let P : Code → Prop := fun c ↦ (c.eval 0).Dom
  let S : Set ℕ+ := {n | P (e n)}
  have he : e.Computable := Computable.equiv₂ _ _
  have htransport : OneOneEquiv (P ∘ e) P := OneOneEquiv.of_equiv he
  refine ⟨S, ?_, ?_⟩
  · change REPred (P ∘ e)
    refine REPred.of_eq (((ComputablePred.halting_problem_re 0).comp he.1).dom_re) ?_
    intro n
    simp [P, Part.assert]
  · change ¬ ComputablePred (P ∘ e)
    intro hS
    exact ComputablePred.halting_problem 0 <|
      ComputablePred.computable_of_oneOneReducible htransport.2 hS

/-! ### Definition_4_7_8 (from Items/Chap04) -/
universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: benign subgroups in the Higman embedding theorem via HNN extensions.

Layer triage:
- `source-facing`: a subgroup `H ≤ G` together with the source condition that the HNN extension
  `G_H`, obtained by adjoining a stable letter centralizing `H`, embeds in a finitely presented
  group.
- `core/canonical`: `HNNExtension G H H (MulEquiv.refl H)` for the ambient HNN extension,
  `Group.IsFinitelyPresented K` for the ambient finite presentability condition, and injective
  homomorphisms from that HNN extension.
- `bridge/view`: the textbook notation `G_H` is the canonical special case of the HNN-extension
  owner where the associated subgroups are both `H` and the gluing isomorphism is `MulEquiv.refl`.

Domain sampling:
1. `HNNExtension G A B φ` is the chapter and mathlib owner abstraction for adjoining a stable
   letter that conjugates `A` onto `B`.
2. `HNNExtension.equiv_eq_conj` and `HNNExtension.equiv_symm_eq_conj` show that in the special
   case `φ = MulEquiv.refl H`, the stable letter centralizes the image of `H`.
3. `Group.IsFinitelyPresented` is mathlib's owner predicate for the finitely presented target.
4. The surrounding chapter states embeddings source-faithfully by quantifying over a homomorphism
   together with `Function.Injective`, rather than by introducing a second wrapper owner.

Primitive vs. derived:
- primitive public data: only the subgroup `H`;
- derived owner object: the source group `G_H`, used directly as the canonical HNN extension
  `HNNExtension G H H (MulEquiv.refl H)`;
- derived public property: existence of a finitely presented overgroup together with an injective
  homomorphism from `HNNExtension G H H (MulEquiv.refl H)`.

The textbook restricts to finitely generated ambient groups `G`, but that hypothesis does not
enter the canonical owner construction or the definition itself, so it is omitted from the public
API.
-/

namespace Subgroup

/-- Definition 4-7-8: a subgroup `H` of `G` is benign in `G` if the HNN extension `G_H`
adjoining one stable letter that centralizes `H` embeds in a finitely presented group. -/
def IsBenign (H : Subgroup G) : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
    (f : HNNExtension G H H (MulEquiv.refl H) →* K),
    Function.Injective f

/-- A benign subgroup admits an embedding of its associated HNN extension `G_H` into a finitely
presented group. -/
theorem IsBenign.exists_finitelyPresented_embedding {H : Subgroup G} (hH : H.IsBenign) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (f : HNNExtension G H H (MulEquiv.refl H) →* K),
      Function.Injective f := by
  simpa [IsBenign] using hH

end Subgroup

end
