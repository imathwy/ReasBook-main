import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_4_1 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: finitely presented group properties and Markov properties from decision-problem
theory.

Layer triage:
- `source-facing`: a property `P` of finitely presented groups, assumed invariant under
  isomorphism, together with the two textbook clauses that characterize when `P` is a Markov
  property.
- `core/canonical`: `Group.IsMarkovProperty` is the chapter owner for this abstract group-level
  notion, `IsFinitelyPresented` is mathlib's owner predicate for finite presentability,
  multiplicative equivalences `G ≃* H` are the canonical group isomorphisms, and monoid
  homomorphisms with `Function.Injective` are the source-faithful embedding data.
- `bridge/view`: the textbook phrase “`G₂` cannot be embedded in any finitely presented group with
  `P`” is expressed directly by the nonexistence of an injective homomorphism `G₂ →* H` into such
  a group `H`.

Domain sampling:
1. `Group.HasSolvableWordProblem` in Theorem `4-4-8` is the chapter's abstract group-level owner
   pattern for decision-theoretic properties, so this definition should also live in `namespace
   Group`.
2. `IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
3. `IsFinitelyPresented.equiv` transports finite presentability across a group isomorphism, so the
   invariance hypothesis should be stated using `G ≃* H`.
4. The surrounding chapter states embeddings source-faithfully as homomorphisms together with
   `Function.Injective`, rather than introducing a separate wrapper object.

Primitive vs. derived:
- ambient input: only the group property `P`;
- primitive class data: preservation of `P` along multiplicative equivalences out of a finitely
  presented group, plus the two existence clauses from the textbook definition;
- derived public API: the symmetric `iff` form of invariance under finitely presented
  isomorphisms.
-/

/-- Definition 4-4-1: a property `P` of finitely presented groups is a Markov property when it is
invariant under isomorphism of finitely presented groups, some finitely presented group has `P`,
and some finitely presented group embeds in no finitely presented group having `P`. -/
class IsMarkovProperty (P : (G : Type u) → [Group G] → Prop) : Prop where
  /-- The property is preserved along multiplicative equivalences out of a finitely presented
  group. -/
  of_mulEquiv {G H : Type u} [Group G] [Group H]
      (e : G ≃* H) (_ : IsFinitelyPresented G) :
      P G → P H
  /-- Some finitely presented group satisfies the property. -/
  exists_with_property :
    ∃ (G₁ : Type u) (_ : Group G₁) (_ : IsFinitelyPresented G₁), P G₁
  /-- Some finitely presented group cannot embed in any finitely presented group satisfying the
  property. -/
  exists_embedding_obstruction :
    ∃ (G₂ : Type u) (_ : Group G₂) (_ : IsFinitelyPresented G₂),
      ∀ {H : Type u} [Group H] (_ : IsFinitelyPresented H) (_ : P H) (f : G₂ →* H),
        ¬ Function.Injective f

namespace IsMarkovProperty

variable {P : (G : Type u) → [Group G] → Prop} [IsMarkovProperty P]

/-- A Markov property is invariant under multiplicative equivalence between finitely presented
groups. -/
theorem iff_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsFinitelyPresented G) :
    P G ↔ P H := by
  constructor
  · exact IsMarkovProperty.of_mulEquiv e hG
  · exact IsMarkovProperty.of_mulEquiv e.symm (IsFinitelyPresented.equiv e hG)

end IsMarkovProperty

end Group

/-! ### Theorem_4_4_2 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace GroupPresentation

/-!
Primary domain: decision problems for finite presentations and Markov properties.

Layer triage:
- `source-facing`: a property `P` of finitely presented groups and the textbook claim that there is
  no algorithm deciding from a finite presentation whether the presented group satisfies `P`.
- `core/canonical`: `Group.IsMarkovProperty P` is the chapter owner for the hypothesis,
  `PresentedGroup` is mathlib's owner for the group defined by generators and relators, and
  `ComputablePred` is the owner predicate for algorithmic decidability on coded inputs.
- `bridge/view`: a raw finite-presentation code consists of a generator count together with a
  finite list of relator words whose letters are natural-number labels; these labels are
  interpreted as generators of `ULift (Fin n)`, with malformed labels normalized modulo `n` so the
  coding remains total for `ComputablePred`.

Domain sampling:
1. `Group.IsMarkovProperty P` from Definition `4-4-1` is the source-facing owner abstraction.
2. `GroupPresentation.HasSolvableWordProblem R` from Definition `2-1-4` is the chapter's owner
   shape for decision problems posed on finite presentations.
3. `PresentedGroup R` is the canonical owner for the group presented by relators `R`.
4. `FreeGroup.mk` is the canonical evaluation map from finite signed words to free-group elements,
   while `ComputablePred` is mathlib's owner for solvability of a decision problem on coded input.

Primitive vs. derived:
- primitive public data: only the property `P`;
- derived bridge data: the raw code `(n, rels)`, its normalization to relator words on
  `ULift (Fin n)`, and the resulting relator set.
-/

private abbrev PresentationCode := ℕ × List (List (ℕ × Bool))

private def codedLetter : (n : ℕ) → ℕ × Bool → Option (ULift (Fin n) × Bool)
  | 0, _ => none
  | m + 1, (i, ε) => some (⟨⟨i % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩⟩, ε)

private def codedWord (n : ℕ) : List (ℕ × Bool) → List (ULift (Fin n) × Bool) :=
  List.filterMap (codedLetter n)

private def relatorSetOfCode (c : PresentationCode) : Set (FreeGroup (ULift.{u} (Fin c.1))) :=
  match c with
  | (n, rels) => FreeGroup.mk '' (codedWord n '' {w | w ∈ rels})

private abbrev presentedGroupOfCode (c : PresentationCode) : Type u :=
  PresentedGroup (relatorSetOfCode c)

/-- A property of finitely presented groups has solvable recognition problem when one can compute
from a finite presentation whether the presented group has that property. -/
def HasSolvableRecognitionProblem (P : (G : Type u) → [Group G] → Prop) : Prop :=
  ComputablePred fun c : PresentationCode ↦
    P (presentedGroupOfCode c)

variable (P : (G : Type u) → [Group G] → Prop)

-- Proof sketch: Adian-Rabin encodes the obstruction group from `IsMarkovProperty P` into a finite
-- presentation so that deciding whether the presented group has `P` would decide whether a given
-- word becomes trivial in an arbitrary finitely presented group. Since the latter is unsolvable,
-- the recognition problem for `P` cannot be computable.
/-- Theorem 4-4-2: every Markov property of finitely presented groups has unsolvable recognition
problem. -/
theorem not_hasSolvableRecognitionProblem [Group.IsMarkovProperty P] :
    ¬ HasSolvableRecognitionProblem P := sorry

end GroupPresentation

/-! ### Lemma_4_4_3 (from Items/Chap04) -/
universe u

set_option autoImplicit false

section

open MonoidHom

variable {X : Type u} (rels : Set (FreeGroup X))

-- Layer triage:
-- `source-facing`: the textbook subgroup `L_H ⊆ F(X) × F(X)` attached to
-- `H = PresentedGroup rels`, together with the criterion that `(u, v) ∈ L_H` exactly when `u`
-- and `v` represent the same element of `H`.
-- `core/canonical`: `PresentedGroup.mk rels` is the canonical quotient map
-- `FreeGroup X → PresentedGroup rels`, and `eqLocus` is the canonical subgroup equalizer of two
-- homomorphisms.
-- `bridge/view`: `L_H` is rendered directly by the equalizer of the two coordinate composites
-- into `PresentedGroup rels`, and membership in that equalizer is the textbook equality of the
-- two quotient images.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the chapter owner for the quotient by relators `rels`.
-- 2. `PresentedGroup.mk rels` is the canonical map sending a free-group word to its class in the
--    presented group.
-- 3. `eqLocus` is mathlib's owner subgroup of elements on which two homomorphisms agree.
-- 4. `fst` and `snd` are the canonical product projections used to compare the two coordinates
--    after applying `PresentedGroup.mk rels`.
-- Primitive vs. derived:
-- the primitive source data are the relator set `rels` and the words `u`, `v`; the textbook
-- subgroup `L_H` is a derived owner-side equalizer construction, so no separate public wrapper is
-- introduced for it.

local notation "F" => FreeGroup X
local notation "q" => PresentedGroup.mk rels
local notation "LH" =>
  eqLocus (comp (PresentedGroup.mk rels) (fst F F)) (comp (PresentedGroup.mk rels) (snd F F))

/-- Lemma 4-4-3: a pair of free-group words lies in the textbook subgroup `L_H` if and only if the
two words represent the same element of `H = PresentedGroup rels`. Here the local notation `LH`
is the owner-side rendering of the textbook subgroup `L_H` by the canonical equalizer subgroup
`eqLocus (q.comp (fst F F)) (q.comp (snd F F))`. -/
theorem mem_LH_iff (u v : F) : (u, v) ∈ LH ↔ q u = q v :=
  Iff.rfl

end

/-! ### Definition_4_4_5 (from Items/Chap04) -/
set_option autoImplicit false

namespace FreeGroupProduct

/-!
Primary domain: algorithmic group theory for direct products of finite-rank free groups.

Layer triage:
- `source-facing`: finite lists of pairs of words in the standard generators of `F_n × F_n`, and
  the question whether those elements generate the whole direct product.
- `core/canonical`: `FreeGroup (Fin n)` for the rank-`n` free group, `FreeGroup.mk` for
  evaluating finite signed words, `Subgroup.closure` for the subgroup generated by a displayed
  set, and `ComputablePred` for algorithmic solvability on coded inputs.
- `bridge/view`: a raw pair of signed words is evaluated coordinatewise by `FreeGroup.mk`, and the
  resulting displayed subset of `FreeGroup (Fin n) × FreeGroup (Fin n)` is closed under
  `Subgroup.closure`.

Domain sampling:
1. `FreeGroup (Fin n)` is the canonical owner for the textbook free group `F_n`.
2. `FreeGroup.mk` is the canonical evaluation map from finite signed words to free-group
   elements.
3. `Subgroup.closure` is the owner construction for the subgroup generated by a displayed set.
4. `ComputablePred` is the canonical owner predicate for algorithmic solvability on coded input.

Primitive vs. derived:
- primitive public data: the rank `n` and the raw finite family of pairs of words in the
  standard generators;
- derived owner-side API: the subgroup they generate in `F_n × F_n`, expressed directly through
  `Subgroup.closure`, so no parallel public wrapper is needed.
-/

section

variable (n : ℕ)

local notation "F" => FreeGroup (Fin n)
local notation "Word" => List (Fin n × Bool)
local notation "WordPair" => Word × Word

private abbrev wordPairValue : WordPair → F × F :=
  Prod.map FreeGroup.mk FreeGroup.mk

/-- Definition 4-4-5: the generating problem for `F_n × F_n` is solvable when one can compute
from a finite list of pairs of words whether their values generate the whole direct product. -/
def HasSolvableGeneratingProblem : Prop :=
  ComputablePred fun L : List WordPair ↦
    Subgroup.closure (wordPairValue n '' {w | w ∈ L}) = ⊤

/-- The generating problem is exactly computability of whether the canonical generated subgroup is
the whole direct product. -/
theorem hasSolvableGeneratingProblem_iff_computable_generatedSubgroup_eq_top :
    HasSolvableGeneratingProblem n ↔
      ComputablePred fun L : List WordPair ↦
        Subgroup.closure (wordPairValue n '' {w | w ∈ L}) = ⊤ :=
  Iff.rfl

end

end FreeGroupProduct

/-! ### Theorem_4_4_6 (from Items/Chap04) -/
set_option autoImplicit false

namespace FreeGroupProduct

/-!
Primary domain: algorithmic group theory for direct products of finite-rank free groups.

Layer triage:
- `source-facing`: the generating problem of Definition `4-4-5` for `F_n × F_n`.
- `core/canonical`: the owner predicate `HasSolvableGeneratingProblem` together with the canonical
  underlying free-group and subgroup constructions used in that definition.
- `bridge/view`: Mihailova's construction reduces an unsolvable subgroup-membership problem to the
  failure of this source-facing computable predicate.

Domain sampling:
1. `FreeGroupProduct.HasSolvableGeneratingProblem` in Definition `4-4-5` is the source-facing
   owner for the theorem's conclusion.
2. `FreeGroup (Fin n)` is the canonical owner for the textbook free group `F_n`.
3. `FreeGroup.mk` is the canonical evaluation map from finite signed words to free-group
   elements.
4. `Subgroup.closure` is the owner construction behind the generating predicate.

Primitive vs. derived:
- primitive public data: the rank `n`;
- derived owner-side API: the source-facing predicate `HasSolvableGeneratingProblem n`.
-/

-- Proof sketch: encode finitely generated subgroups of `F_n × F_n` by finite lists of pairs of
-- words in the standard free bases. Mihailova's construction embeds an unsolvable subgroup
-- membership problem into the question whether such a finite family generates the whole direct
-- product. For `n ≥ 6`, the required finitely presented group with unsolvable word problem exists
-- by the preceding Higman-Rabin results, so no algorithm can solve the generating problem.
/-- Theorem 4-4-6: if `n ≥ 6`, then the generating problem for `F_n × F_n` is unsolvable. -/
theorem not_hasSolvableGeneratingProblem (n : ℕ) (hn : 6 ≤ n) :
    ¬ HasSolvableGeneratingProblem n := sorry

end FreeGroupProduct

/-! ### Theorem_4_4_8 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algorithmic group theory for finitely presented residually finite groups.

Layer triage:
- `source-facing`: an abstract group `G` together with the textbook assertion that finite
  presentability and residual finiteness imply solvability of the word problem for `G`.
- `core/canonical`: `Group.IsFinitelyPresented G` and `Group.ResiduallyFinite G` are mathlib's
  owner predicates for the two hypotheses, while `PresentedGroup R ≃* G` is the project's
  canonical bridge from a finite-generator presentation to an abstract group.
- `bridge/view`: the chapter's concrete owner predicate for solvability is
  `GroupPresentation.HasSolvableWordProblem R` on a relator set `R`, so the abstract group-level
  property is recorded by the existence of some finite-generator presentation with that property.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's canonical abstract owner for finite presentability.
2. `Group.ResiduallyFinite` is mathlib's canonical abstract owner for residual finiteness.
3. `PresentedGroup R ≃* G` is the project's canonical presentation datum from Definition `2-1-1`.
4. `GroupPresentation.HasSolvableWordProblem R` is the chapter owner predicate for solvability of
   the word problem in a concrete presentation.

Primitive vs. derived:
- primitive public data for the abstract owner: only the ambient group `G`;
- derived bridge data: a finite generator rank `n`, a relator set
  `R : Set (FreeGroup (Fin n))`, and a presentation equivalence `PresentedGroup R ≃* G`.
-/

/-- An abstract group has solvable word problem if some finite-generator presentation of it has
solvable word problem in the chapter's presentation-level sense. -/
def HasSolvableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, ∃ R : Set (FreeGroup (Fin n)), ∃ _ : PresentedGroup R ≃* G,
    GroupPresentation.HasSolvableWordProblem R

/-- An abstract group has solvable conjugacy problem if some finite-generator presentation of it
has solvable conjugacy problem in the chapter's presentation-level sense. -/
def HasSolvableConjugacyProblem (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, ∃ R : Set (FreeGroup (Fin n)), ∃ _ : PresentedGroup R ≃* G,
    GroupPresentation.HasSolvableConjugacyProblem R

variable {G : Type u} [Group G]

-- Proof sketch: the chosen presentation equivalence together with the owner-side solvable word
-- problem for that presentation is exactly the data required by `HasSolvableWordProblem G`.
/-- A solvable word problem for an explicit finite-generator presentation induces a solvable word
problem for the abstract group it presents. -/
theorem hasSolvableWordProblem_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.HasSolvableWordProblem R) :
    HasSolvableWordProblem G := by
  exact ⟨n, R, P, hR⟩

-- Proof sketch: the chosen presentation equivalence together with the owner-side solvable
-- conjugacy problem for that presentation is exactly the data required by
-- `HasSolvableConjugacyProblem G`.
/-- A solvable conjugacy problem for an explicit finite-generator presentation induces a solvable
conjugacy problem for the abstract group it presents. -/
theorem hasSolvableConjugacyProblem_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.HasSolvableConjugacyProblem R) :
    HasSolvableConjugacyProblem G := by
  exact ⟨n, R, P, hR⟩

-- Proof sketch: choose a finite presentation of `G` from `IsFinitelyPresented G`. For that
-- presentation, words equal to `1` are recursively enumerable from the finite relator set, while
-- residual finiteness lets one recursively enumerate the words not equal to `1` by searching over
-- all homomorphisms from `G` to finite groups and checking when the image of the word is
-- nontrivial. Running the two enumerations in parallel yields a decision procedure for the word
-- problem of the chosen finite presentation, which then witnesses `HasSolvableWordProblem G`.
/-- Theorem 4-4-8: a finitely presented residually finite group has solvable word problem. -/
theorem hasSolvableWordProblem_of_isFinitelyPresented_of_residuallyFinite
    (G : Type u) [Group G] [IsFinitelyPresented G] [ResiduallyFinite G] :
    HasSolvableWordProblem G := sorry

end Group

/-! ### Theorem_4_4_9 (from Items/Chap04) -/
universe u

section

variable {G : Type u} [Group G] [Group.FG G]

namespace Subgroup

-- Layer triage:
-- `source-facing`: finite generation of `G`, subgroups of a fixed finite index, and a
-- characteristic finite-index subgroup contained in a given finite-index subgroup.
-- `core/canonical`: `Subgroup.index`, `H.FiniteIndex`, `K.Characteristic`, and finite
-- intersections of finite-index subgroups.
-- `bridge/view`: the first clause packages the textbook "number of subgroups" as finiteness of
-- the set `{H : Subgroup G | H.index = n}`, and the second clause keeps the source-facing
-- existential conclusion with the canonical finite-index owner property instead of introducing an
-- auxiliary bundled wrapper.
-- Domain sampling:
-- 1. `Subgroup.index` is mathlib's owner for subgroup index.
-- 2. `Subgroup.FiniteIndex` is the canonical finite-index hypothesis on a subgroup.
-- 3. `Subgroup.characteristic_iff_map_eq` is the owner criterion for invariance under
--    automorphisms.
-- 4. `Subgroup.finiteIndex_iInf'` is the finite-intersection owner theorem used by the textbook's
--    intersection construction.
-- Primitive vs. derived:
-- the primitive public data are only the ambient finitely generated group `G`, the index `n` in
-- the first clause, and the finite-index subgroup `H` in the second clause. The finite set of
-- index-`n` subgroups and the characteristic finite-index subgroup contained in `H` are derived
-- owner-level conclusions.

-- Proof sketch: encode each subgroup of index `n` by its transitive action on the `n` right
-- cosets, producing a homomorphism into the symmetric group on `n` letters. A finitely generated
-- group has only finitely many homomorphisms into a fixed finite group, so only finitely many
-- index-`n` subgroups can occur.
/-- Theorem 4-4-9 (1): a finitely generated group has only finitely many subgroups of any fixed
positive index `n`. -/
theorem finite_setOf_index_eq (n : ℕ+) :
    Set.Finite {H : Subgroup G | H.index = (n : ℕ)} := sorry

-- Proof sketch: let `n = H.index` and intersect all subgroups of `G` of index `n`. By the first
-- clause this is a finite intersection, hence still of finite index; it lies in `H` because `H`
-- itself has index `n`; and every automorphism of `G` permutes the index-`n` subgroups, so their
-- intersection is characteristic.
/-- Theorem 4-4-9 (2): every finite-index subgroup of a finitely generated group contains a
characteristic subgroup of finite index. -/
theorem exists_characteristic_le_of_finiteIndex (H : Subgroup G) [H.FiniteIndex] :
    ∃ K : Subgroup G, K ≤ H ∧ K.Characteristic ∧ K.FiniteIndex := sorry

end Subgroup

end

/-! ### Theorem_4_4_10 (from Items/Chap04) -/
universe u

section

variable {G : Type u} [Group G] [Group.FG G] [Group.ResiduallyFinite G]

-- Layer triage:
-- `source-facing`: a finitely generated residually finite group `G` and the automorphism group
-- `Aut(G)`.
-- `core/canonical`: `Group.FG G`, `Group.ResiduallyFinite G`, `FiniteIndexNormalSubgroup`, and
-- `MulAut G`.
-- `bridge/view`: the textbook notation `Aut(G)` is the canonical multiplicative automorphism group
-- `MulAut G`; residual finiteness is stated directly via the mathlib class on that owner.
-- Domain sampling:
-- 1. `Group.ResiduallyFinite` is mathlib's owner predicate for residual finiteness.
-- 2. `Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup` is the owner-level separation
--    criterion for residual finiteness.
-- 3. `Subgroup.exists_characteristic_le_of_finiteIndex` from Theorem `4-4-9` is the chapter's
--    canonical bridge from an arbitrary finite-index subgroup to a characteristic one.
-- 4. `MulAut G` is the canonical group of automorphisms of `G`.
--
-- Primitive vs. derived:
-- the primitive public content is only the owner instance
-- `Group.ResiduallyFinite (MulAut G)`. The separating finite-index normal subgroup of `MulAut G`
-- used in the textbook argument is derived owner-level data, so it should not be promoted to a
-- separate wrapper or existentially chosen public definition.

-- Proof sketch: for a nontrivial automorphism `α`, choose `c : G` moved by `α`, so
-- `α c * c⁻¹ ≠ 1`. By
-- `Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup`, choose a finite-index normal
-- subgroup of `G` missing that element, then apply Theorem `4-4-9` to refine it to a
-- characteristic finite-index subgroup `K`. Every automorphism of `G` then descends to `G ⧸ K`,
-- yielding a homomorphism `MulAut G →* MulAut (G ⧸ K)` into a finite group that does not kill
-- `α`.
/-- Theorem 4-4-10: if `G` is finitely generated and residually finite, then its automorphism
group `Aut(G)` is residually finite. -/
instance residuallyFinite_mulAut_of_fg_residuallyFinite :
    Group.ResiduallyFinite (MulAut G) where
  iInf_eq_bot := sorry

end

/-! ### Theorem_4_4_11 (from Items/Chap04) -/
set_option autoImplicit false

namespace BaumslagSolitar23

/-!
Primary domain: one-relator groups and Hopfianity for the Baumslag-Solitar group `BS(2,3)`.

Layer triage:
- `source-facing`: the standard endomorphism of `BS(2,3)` written in the textbook letters `b`
  and `t`, with `t` fixed and `b` sent to `b^2`.
- `core/canonical`: the existing project owner `BaumslagSolitar23.Group` from Theorem `2-2-5`,
  mathlib's `PresentedGroup.toGroup`, and the chapter owner predicate `IsHopfian`.
- `bridge/view`: the textbook letters are recovered from the upstream owner by `b := y` and
  `t := x`.

Domain sampling:
1. Theorem `2-2-5` already packages `BS(2,3)` in the owner namespace `BaumslagSolitar23`,
   together with the canonical generator images `x` and `y`.
2. `PresentedGroup.toGroup` and `PresentedGroup.toGroup.of` are the owner APIs for defining an
   endomorphism from generator images and then evaluating it on those generators.
3. `PresentedGroup.one_of_mem` is the canonical relator-triviality lemma, so a separate local
   theorem saying the defining relator becomes `1` would duplicate owner API.
4. `IsHopfian` from Proposition `1-3-5` is the canonical owner predicate for the conclusion that
   `BS(2,3)` is non-Hopfian.

Primitive vs. derived:
the public primitive data are the existing owner group together with its canonical generators `x`
and `y`. The textbook letters `b` and `t` are only a local notation bridge, and the generator
assignment used to build the endomorphism plus its relator check are derived implementation
details, so they remain private. The named endomorphism and its image/surjectivity/noninjectivity
lemmas are the public companion surface; there is no separate existential wrapper API.
-/

/- Source-facing notation: the textbook letters `b` and `t` are just the upstream owner
generators `y` and `x`. They are kept local so the public API stays on the canonical owner
declarations from Theorem `2-2-5`. -/
local notation "b" => y
local notation "t" => x

private def squareEndomorphismImages : BaumslagSolitar23Generator → Group
  | .x => x
  | .y => y ^ (2 : ℕ)

private theorem squareEndomorphism_respects_relator
    (r : FreeGroup BaumslagSolitar23Generator) (hr : r ∈ relators) :
    FreeGroup.lift squareEndomorphismImages r = (1 : Group) := by
  sorry

/-- The standard endomorphism of `BS(2,3)` fixing `t` and sending `b` to `b^2`. -/
noncomputable def squareEndomorphism : Group →* Group :=
  PresentedGroup.toGroup squareEndomorphism_respects_relator

/-- The standard endomorphism of `BS(2,3)` sends `b` to `b^2`. -/
@[simp] theorem squareEndomorphism_of_b :
    squareEndomorphism b = b ^ (2 : ℕ) := by
  simpa [squareEndomorphismImages] using
    (show squareEndomorphism (PresentedGroup.of BaumslagSolitar23Generator.y) =
        squareEndomorphismImages BaumslagSolitar23Generator.y from
      PresentedGroup.toGroup.of squareEndomorphism_respects_relator)

/-- The standard endomorphism of `BS(2,3)` fixes the generator `t`. -/
@[simp] theorem squareEndomorphism_of_t :
    squareEndomorphism t = t := by
  simpa [squareEndomorphismImages] using
    (show squareEndomorphism (PresentedGroup.of BaumslagSolitar23Generator.x) =
        squareEndomorphismImages BaumslagSolitar23Generator.x from
      PresentedGroup.toGroup.of squareEndomorphism_respects_relator)

/-- The standard endomorphism of `BS(2,3)` is surjective. -/
-- Proof sketch: the image contains `t` by `squareEndomorphism_of_t`, and it also contains `b`
-- because the defining relation rewrites `t⁻¹ b^2 t = b^3`, so from the image element `b^2` one
-- recovers `b`. Since `b` and `t` generate the group, the endomorphism is surjective.
theorem squareEndomorphism_surjective :
    Function.Surjective squareEndomorphism := by
  sorry

/-- The standard endomorphism of `BS(2,3)` is not injective. -/
-- Proof sketch: the commutator `[t⁻¹ b t, b]` is nontrivial by Britton's lemma in the HNN
-- extension model of `BS(2,3)`, but its image under `squareEndomorphism` is
-- `[t⁻¹ b^2 t, b^2] = [b^3, b^2] = 1`.
theorem squareEndomorphism_not_injective :
    ¬ Function.Injective squareEndomorphism := by
  sorry

/-- Theorem 4-4-11: the group `⟨ b, t ; t⁻¹ b^2 t = b^3 ⟩` is non-Hopfian. -/
theorem not_isHopfian : ¬ IsHopfian Group := by
  intro hHopfian
  exact squareEndomorphism_not_injective <|
    MonoidHom.injective_of_surjective squareEndomorphism squareEndomorphism_surjective

end BaumslagSolitar23

/-! ### Remark_4_4_12 (from Items/Chap04) -/
set_option autoImplicit false

namespace BaumslagSolitar23

/-!
Primary domain: residual finiteness and Hopfianity for the Baumslag-Solitar group `BS(2,3)`.

Layer triage:
- `source-facing`: the textbook consequence that `BS(2,3)` is not residually finite.
- `core/canonical`: `Group.ResiduallyFinite`, `IsHopfian`, the chapter theorem `not_isHopfian`,
  and the owner instance `isHopfian_of_fg_residuallyFinite`.
- `bridge/view`: this remark is the direct contradiction between those owner-level facts, so it
  should stay a thin theorem rather than introducing a new endomorphism-level wrapper.

Domain sampling:
1. `Group.ResiduallyFinite` is mathlib's owner predicate for residual finiteness.
2. `IsHopfian` from Proposition `1-3-5` is the chapter owner predicate for Hopfianity.
3. `not_isHopfian` from Theorem `4-4-11` is the canonical non-Hopfianity result for `BS(2,3)`.
4. `isHopfian_of_fg_residuallyFinite` from Theorem `4-4-13` is the canonical owner instance
   turning finite generation and residual finiteness into Hopfianity.

Primitive vs. derived:
the only new public content here is the source-facing failure of residual finiteness. The Hopfian
instance and the non-Hopfian counterexample already live upstream, so the remark should expose only
their direct owner-level consequence.
-/

/-- Remark 4-4-12: the Baumslag-Solitar group `⟨ b, t ; t⁻¹ b^2 t = b^3 ⟩` is not residually
finite. -/
theorem not_residuallyFinite : ¬ Group.ResiduallyFinite Group := by
  intro hRF
  letI : Group.ResiduallyFinite Group := hRF
  exact not_isHopfian inferInstance

end BaumslagSolitar23

/-! ### Theorem_4_4_13 (from Items/Chap04) -/
universe u

section

variable {G : Type u} [Group G] [Group.FG G] [Group.ResiduallyFinite G]

-- Primary domain: Hopfianity of finitely generated residually finite groups.
--
-- Layer triage:
-- `source-facing`: a group `G` that is both finitely generated and residually finite.
-- `core/canonical`: `Group.FG`, `Group.ResiduallyFinite`, and the chapter owner `IsHopfian`.
-- `bridge/view`: the textbook endomorphism formulation is a thin consequence of the owner
-- predicate `IsHopfian`.
-- Domain sampling:
-- 1. `Group.FG` from `Mathlib.GroupTheory.Finiteness` is the canonical owner predicate for finite
--    generation of a group.
-- 2. `Group.ResiduallyFinite` from `Mathlib.GroupTheory.ResiduallyFinite` is the canonical owner
--    predicate for residual finiteness.
-- 3. `IsHopfian` from Proposition `1-3-5` is the project's owner predicate for the Hopfian
--    conclusion.
-- 4. `MonoidHom.injective_of_surjective` is the canonical bridge from `IsHopfian G` back to the
--    source-facing endomorphism statement.
--
-- Primitive vs. derived:
-- the primitive public content is the owner instance `IsHopfian G`; the endomorphism-level
-- injectivity statement is derived API and should not remain the main declaration.

/-- Theorem 4-4-13: every finitely generated residually finite group is Hopfian. -/
-- Proof sketch: let `φ : G →* G` be surjective with kernel `K`. For each positive index `n`,
-- finite generation gives only finitely many subgroups of index `n`; surjectivity permutes them by
-- inverse image, so `K` lies in every subgroup of index `n`. Since this holds for every finite
-- index and `G` is residually finite, the intersection of all finite-index subgroups is trivial,
-- forcing `K = ⊥` and hence `φ` to be injective.
instance isHopfian_of_fg_residuallyFinite : IsHopfian G where
  injective_of_surjective (φ : G →* G) (hφ : Function.Surjective φ) := by
    sorry

/-- Source-facing reformulation of Theorem `4-4-13`: every surjective endomorphism of a finitely
generated residually finite group is injective. -/
theorem injective_of_surjective_endomorphism_of_fg_residuallyFinite (φ : G →* G)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  letI : IsHopfian G := isHopfian_of_fg_residuallyFinite
  exact MonoidHom.injective_of_surjective φ hφ

end
