import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_2_2_1 (from Items/Chap02) -/
universe u

namespace GroupPresentation

-- Layer triage:
-- `source-facing`: a finite presentation consists of a finite generator type together with a
-- finite relator set, and Tietze transformations are the elementary operations on such data.
-- `core/canonical`: `PresentedGroup` is the owner object attached to a relator set,
-- `Group.IsFinitelyPresented` is mathlib's owner predicate for the abstract group-level notion,
-- and `Relation.EqvGen` is the canonical owner for equivalence closure of elementary steps.
-- `bridge/view`: the proposition identifies equality up to a finite Tietze sequence on the
-- source-facing data with isomorphism of the associated canonical presented groups.
-- Domain sampling:
-- 1. `PresentedGroup rels` is mathlib's canonical group attached to generators and relations.
-- 2. `PresentedGroup.toGroup` and `PresentedGroup.equivPresentedGroup` are the owner transport
--    maps for changing generators and relators while preserving the presented group.
-- 3. `Group.IsFinitelyPresented` is the canonical abstract owner predicate for the existence of a
--    finite presentation.
-- 4. `Relation.EqvGen` is mathlib's canonical equivalence closure for a primitive one-step
--    relation, so a separate inductive closure API is unnecessary here.
-- 5. Definition `2-1-2` in this chapter already identifies "finite presentation" with the
--    primitive owner predicates `Finite X` and `Set.Finite R`, so no parallel wrapper structure
--    is needed here.
-- Primitive vs. derived:
-- the primitive source data are the generator type and relator set together with the owner
-- finiteness predicates `Finite X` and `Set.Finite R`, together with the one-step
-- source-facing Tietze expansion relation; the presented group, the abstract
-- finite-presentation property, and Tietze equivalence are derived owner-side API.

variable {X Y Z : Type u}
variable {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)} {T : Set (FreeGroup Z)}

-- Proof sketch: choose an equivalence between the finite generator type `X` and some `Fin n`,
-- transport the relator set `R` across that equivalence using
-- `PresentedGroup.equivPresentedGroup`, and use the finiteness of the transported relator set to
-- instantiate `Group.IsFinitelyPresented`.
/-- The group canonically defined by a finite presentation is finitely presented in mathlib's
abstract sense. -/
theorem isFinitelyPresented_presentedGroup [Finite X] (hR : R.Finite) :
    Group.IsFinitelyPresented (PresentedGroup R) := sorry

/-- An elementary Tietze expansion either adjoins finitely many relators already implied by the
old ones, up to reindexing of generators, or adjoins finitely many new generators together with
defining relators expressing them as words in the old generators. -/
inductive TietzeExpansion :
    {X : Type u} → Set (FreeGroup X) → {Y : Type u} → Set (FreeGroup Y) → Prop
  | addConsequenceRelators
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (e : X ≃ Y)
      (T : Set (FreeGroup Y))
      (hTfinite : T.Finite)
      (hTclosure : T ⊆ Subgroup.normalClosure (FreeGroup.freeGroupCongr e '' R))
      (hS : S = FreeGroup.freeGroupCongr e '' R ∪ T) :
      TietzeExpansion R S
  | addGenerators
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (Z : Type u)
      [Finite Z]
      (e : X ⊕ Z ≃ Y)
      (words : Z → FreeGroup X)
      (hS :
        S =
          FreeGroup.freeGroupCongr e ''
            ((FreeGroup.lift (fun x : X ↦ FreeGroup.of (Sum.inl x)) '' R) ∪
              Set.range
                (fun z : Z ↦
                  (FreeGroup.of (Sum.inr z))⁻¹ *
                    FreeGroup.lift (fun x : X ↦ FreeGroup.of (Sum.inl x)) (words z)))) :
      TietzeExpansion R S

private abbrev Presentation :=
  Σ X : Type u, Set (FreeGroup X)

private abbrev presentation {X : Type u} (R : Set (FreeGroup X)) : Presentation :=
  ⟨X, R⟩

private inductive TietzeStep : Presentation → Presentation → Prop
  | mk
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (h : TietzeExpansion R S) :
      TietzeStep (presentation R) (presentation S)

/-- Two finite presentations are Tietze equivalent when one can be obtained from the other by a
finite sequence of elementary Tietze expansions and their inverses. -/
def TietzeEquivalent :
    {X : Type u} → Set (FreeGroup X) → {Y : Type u} → Set (FreeGroup Y) → Prop
  | _, R, _, S => Relation.EqvGen TietzeStep (presentation R) (presentation S)

-- Proof sketch: each elementary Tietze expansion preserves the associated presented group up to a
-- canonical multiplicative equivalence, so a finite sequence gives an isomorphism by composition.
-- Conversely, given an isomorphism between the groups defined by two finite presentations, pass to
-- a common presentation on the disjoint union of the generator sets, adjoin the finite defining
-- relators coming from the chosen words on each side, and realize each enlargement as a finite
-- Tietze sequence.
/-- Proposition 2-2-1: two finite presentations define isomorphic groups if and only if they are
related by a finite sequence of Tietze transformations. -/
theorem presentedGroup_mulEquiv_iff_tietzeEquivalent [Finite X] [Finite Y]
    (hR : R.Finite) (hS : S.Finite) :
    Nonempty (PresentedGroup R ≃* PresentedGroup S) ↔ TietzeEquivalent R S := sorry

end GroupPresentation

/-! ### Proposition_2_2_2 (from Items/Chap02) -/
universe u v

namespace GroupPresentation

section

variable {X₁ : Type u} {X₂ : Type v}
variable {R₁ : Set (FreeGroup X₁)} {R₂ : Set (FreeGroup X₂)}

local notation "G₁" => PresentedGroup R₁
local notation "G₂" => PresentedGroup R₂

-- Layer triage:
-- `source-facing`: two finite presentations of the same group, together with the claim that
-- solvability of the word problem or of the conjugacy problem does not depend on which finite
-- presentation is chosen.
-- `core/canonical`: the owner objects `PresentedGroup R₁` and `PresentedGroup R₂`, the chapter
-- owner predicates `HasSolvableWordProblem` and `HasSolvableConjugacyProblem`, and the owner
-- conjugacy relation `IsConj` on a group.
-- `bridge/view`: "presentations of the same group" is expressed canonically by a multiplicative
-- equivalence `G₁ ≃* G₂`; the internal transport lemmas below isolate the owner-side transport,
-- while the public theorem surface keeps only the invariant presentation-level statements.
-- Domain sampling:
-- 1. `PresentedGroup R` is the mathlib owner abstraction for a group given by generators and
--    relators.
-- 2. `HasSolvableWordProblem R` from Definition `2-1-4` is the chapter owner predicate for the
--    word problem of a presentation.
-- 3. `HasSolvableConjugacyProblem R` is the matching chapter owner predicate for solvability of
--    the conjugacy problem.
-- 4. `IsConj` is the owner relation for conjugacy in a group.
-- 5. `MulEquiv` is the canonical bridge for transporting group-theoretic decidability data
--    between isomorphic presented groups.
-- Primitive vs. derived:
-- the primitive data for the owner-level transport are the two relator sets and an isomorphism
-- between their presented groups; solvable word and conjugacy problems are the chapter's
-- presentation-level computability predicates on coded words, while finiteness of the generator
-- types is the only extra effective hypothesis used by the transport. The source phrase "finite
-- presentation" from Definition `2-1-2` adds relator finiteness as a separate source-facing
-- condition, but that condition is inert for the invariance statement proved here.

section WordProblem

variable [Primcodable X₁] [Primcodable X₂] [Finite X₂]

-- Proof sketch: choose, for each generator of the second finite presentation, a word in the first
-- free group with the same value in the common presented group. Because the target generator type
-- is finite, this gives a finite lookup table for substituting words from `X₂` into words on
-- `X₁`, so the decision procedure for triviality in `PresentedGroup R₁` transports to one for
-- `PresentedGroup R₂`.
private theorem hasSolvableWordProblem_of_mulEquiv
    (e : G₁ ≃* G₂) :
    HasSolvableWordProblem R₁ → HasSolvableWordProblem R₂ := sorry

/-- Bridge lemma: for finite generating sets on both sides, solvability of the word problem is
invariant under an isomorphism of presented groups. -/
theorem hasSolvableWordProblem_iff_mulEquiv [Finite X₁]
    (e : G₁ ≃* G₂) :
    HasSolvableWordProblem R₁ ↔ HasSolvableWordProblem R₂ := by
  constructor
  · exact hasSolvableWordProblem_of_mulEquiv e
  · exact hasSolvableWordProblem_of_mulEquiv e.symm

end WordProblem

section ConjugacyProblem

variable [Primcodable X₁] [Primcodable X₂] [Finite X₂]

-- Proof sketch: choose, for each generator of the second finite presentation, a word in the first
-- free group with the same value after transporting along `e.symm`. This finite substitution table
-- translates pairs of words on `X₂` to pairs of words on `X₁`, and `e` preserves `IsConj`, so a
-- conjugacy algorithm for `R₁` transports to one for `R₂`.
private theorem hasSolvableConjugacyProblem_of_mulEquiv
    (e : G₁ ≃* G₂) :
    HasSolvableConjugacyProblem R₁ → HasSolvableConjugacyProblem R₂ := sorry

/-- Bridge lemma: for finite generating sets on both sides, solvability of the conjugacy problem
is invariant under an isomorphism of presented groups. -/
theorem hasSolvableConjugacyProblem_iff_mulEquiv [Finite X₁]
    (e : G₁ ≃* G₂) :
    HasSolvableConjugacyProblem R₁ ↔ HasSolvableConjugacyProblem R₂ := by
  constructor
  · exact hasSolvableConjugacyProblem_of_mulEquiv e
  · exact hasSolvableConjugacyProblem_of_mulEquiv e.symm

end ConjugacyProblem

section IsomorphismInvariance

variable [Primcodable X₁] [Primcodable X₂] [Finite X₁] [Finite X₂]

-- Proof sketch: the one-way word-problem bridge only needs finiteness of the target generator
-- type, so applying it to `e` and `e.symm` gives a symmetric statement once both generator types
-- are finite. The conjugacy bridge has the same effective transport shape, so it becomes
-- symmetric under the same pair of finiteness hypotheses.
/-- Proposition 2-2-2, core form: along an isomorphism between two presented groups with finite
generating types, solvability of the word problem and of the conjugacy problem are invariant. By
Definition `2-1-2`, this applies in particular to finite presentations. -/
theorem solvable_word_and_conjugacy_problems_iff_mulEquiv
    (e : G₁ ≃* G₂) :
    (HasSolvableWordProblem R₁ ↔ HasSolvableWordProblem R₂) ∧
      (HasSolvableConjugacyProblem R₁ ↔ HasSolvableConjugacyProblem R₂) := by
  exact ⟨hasSolvableWordProblem_iff_mulEquiv e, hasSolvableConjugacyProblem_iff_mulEquiv e⟩

end IsomorphismInvariance

/- Source-facing finite-presentation wording: Definition `2-1-2` identifies a finite presentation
with `Finite X ∧ Set.Finite R`, so Proposition `2-2-2` is the immediate specialization of
`solvable_word_and_conjugacy_problems_iff_mulEquiv` obtained by discarding the inert
`Set.Finite R` hypotheses. -/

end

end GroupPresentation

/-! ### Proposition_2_2_3 (from Items/Chap02) -/
open scoped BigOperators
open GroupPresentation

universe u

-- Layer triage:
-- `source-facing`: a group `G` equipped with a chosen generating `n`-tuple
-- `generators : Fin n → G`, its abelianization `Abelianization G`, a finite integer matrix
-- `M : Matrix (Fin m) (Fin n) ℤ` presenting that abelianization relative to those generators, and
-- a group presentation on the same `n` generators whose relators lift the rows of `M` modulo the
-- commutator subgroup of the free group.
-- `core/canonical`: `PresentedGroup`, `Abelianization`, `FreeAbelianGroup`, `Matrix`, and the
-- standard free `ℤ`-module `FreeAbelianGroup (Fin n)`, together with the chapter owner map
-- `GroupPresentation.generatorImage`.
-- `bridge/view`: the abelian relation matrix determines the canonical quotient module
-- `FreeAbelianGroup (Fin n) ⧸ relationMatrixSubmodule M`; the chosen generators induce the
-- canonical classes `Additive.ofMul (Abelianization.of (generators j))`, and the relator
-- congruences are expressed by equalities in the additive owner
-- `FreeAbelianGroup (Fin n) = Additive (Abelianization (FreeGroup (Fin n)))`.
-- Domain sampling:
-- 1. `PresentedGroup rels` is mathlib's owner abstraction for a presentation on generators
--    indexed by a type.
-- 2. `Abelianization.of` is the canonical map recording equality modulo the commutator subgroup.
-- 3. `GroupPresentation.generatorImage P` is the chapter owner map from defining generators in a
--    presentation to their images in the ambient group.
-- 4. `FreeAbelianGroup.of` and `FreeAbelianGroup.lift` are the canonical owner maps for linear
--    combinations of generators in the free abelian group.
-- 5. `FreeAbelianGroup (Fin n) ⧸ relationMatrixSubmodule M` is the canonical quotient module
--    presented by the rows of `M`.
-- 6. `Matrix (Fin m) (Fin n) ℤ` is the owner abstraction for a finite integer relation matrix.
-- Primitive vs. derived:
-- the primitive extra data are the chosen generating `n`-tuple `generators : Fin n → G`, its
-- closure hypothesis, and the matrix rows as elements of the free abelian group on `n`
-- generators together with the induced quotient by their span; the presentation equivalence, its
-- compatibility with `generators`, and the additive abelianized relator formulas are the derived
-- existential conclusion.

/-- The `i`-th row of an integer relation matrix, viewed in the free abelian group on
`Fin n`. -/
def relationMatrixRow {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) :
    FreeAbelianGroup (Fin n) :=
  ∑ j : Fin n, M i j • FreeAbelianGroup.of j

/-- The submodule of the free abelian group generated by the rows of a relation matrix. -/
def relationMatrixSubmodule {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    Submodule ℤ (FreeAbelianGroup (Fin n)) :=
  Submodule.span ℤ <| Set.range (relationMatrixRow M)

-- Proof sketch: use the chosen generating tuple `generators : Fin n → G` to obtain the canonical
-- epimorphism `FreeGroup (Fin n) →* G`, whose kernel yields a presentation on the same generators.
-- The hypothesis on `M` identifies the abelianization of that epimorphism with the quotient of
-- `FreeAbelianGroup (Fin n)` by the row span of `M`, so each row relation lifts to a relator in
-- the kernel. Enumerate the remaining kernel elements after the first `m` relators by words whose
-- abelianization is trivial.
/-- Proposition 2-2-3: if `generators : Fin n → G` generates `G` and `M` is a finite `m`-by-`n`
relation matrix presenting `Abelianization G` relative to the images of those generators, then `G`
admits a presentation on the same generators `Fin n` with relators `r₀, r₁, ...` such that the
first `m` relators have the prescribed images in the abelianization of the free group, while every
later relator is trivial modulo the commutator subgroup. -/
theorem exists_presentation_with_abelianized_relation_matrix {m n : ℕ}
    (G : Type u) [Group G] (generators : Fin n → G)
    (hgenerators : Subgroup.closure (Set.range generators) = ⊤) (M : Matrix (Fin m) (Fin n) ℤ)
    (hM : ∃ e : (FreeAbelianGroup (Fin n) ⧸ relationMatrixSubmodule M) ≃ₗ[ℤ]
        Additive (Abelianization G),
      ∀ j : Fin n,
        e (Submodule.Quotient.mk (FreeAbelianGroup.of j)) =
          Additive.ofMul (Abelianization.of (generators j))) :
    ∃ relators : ℕ → FreeGroup (Fin n),
      ∃ P : PresentedGroup (Set.range relators) ≃* G,
        generatorImage P = generators ∧
          (∀ i : Fin m, Additive.ofMul (Abelianization.of (relators i)) = relationMatrixRow M i) ∧
            ∀ k : ℕ, m ≤ k → Additive.ofMul (Abelianization.of (relators k)) = 0 := sorry

/-! ### Proposition_2_2_4 (from Items/Chap02) -/
universe u v

open scoped Classical

noncomputable section

namespace GroupPresentation

variable {G : Type u} [Group G] {X : Type v} {R : Set (FreeGroup X)}

-- Layer triage:
-- `source-facing`: a finite presentation `G = (X; R)` together with the deficiency question from
-- Proposition `2-2-4`.
-- `core/canonical`: `PresentedGroup R ≃* G`, the chapter owner map
-- `GroupPresentation.generatorImage`, `Subgroup.closure`, and the subset-style basis predicate
-- `IsFreeGroupBasis`.
-- `bridge/view`: the selected subset `X₀ ⊆ X` is transported into `G` by `generatorImage P`;
-- the source generators must remain distinguishable, and that relation to the image subset is
-- recorded canonically by `Set.BijOn (generatorImage P) X₀ (generatorImage P '' X₀)` before the
-- image is regarded as a basis subset of the subgroup it generates.
-- Domain sampling:
-- 1. `PresentedGroup R ≃* G` is the canonical presentation datum from Definition `2-1-1`.
-- 2. `GroupPresentation.generatorImage` is the chapter owner map sending each generator to its
--    image in `G`.
-- 3. `Subgroup.closure` is the canonical subgroup generated by a subset of a group.
-- 4. `IsFreeGroupBasis` is the project's source-faithful basis predicate for a subset of a group.
-- Primitive vs. derived:
-- the primitive source data are the presentation equivalence `P`, the owner finiteness predicates
-- `Finite X` and `Set.Finite R`, and a subset `X₀ ⊆ X`; the numerical deficiency is then the
-- derived cardinal `Nat.card X₀`, while the bijection from `X₀` onto its image under
-- `generatorImage P`, its generated subgroup, and the corresponding subset of that subgroup are
-- all derived from `generatorImage P`.

/-- Proposition 2-2-4: for a finite presentation `G = (X; R)`, the deficiency question asks
whether there is a subset `X₀ ⊆ X` such that `|R| + |X₀| = |X|`, and whose image in `G` is a
basis of the free subgroup generated by that image, with the chosen generators mapping
bijectionally onto that image subset.
-/
def finitePresentationDeficiencyQuestion (P : PresentedGroup R ≃* G) : Prop :=
  let gen : X → G := generatorImage P
  Finite X ∧
    Set.Finite R ∧
      ∃ X₀ : Set X,
        let Y : Set G := gen '' X₀
        Nat.card R + Nat.card X₀ = Nat.card X ∧
          Set.BijOn gen X₀ Y ∧
          IsFreeGroupBasis { g : Subgroup.closure Y | (g : G) ∈ Y }

end GroupPresentation

/-! ### Theorem_2_2_5 (from Items/Chap02) -/
-- Primary domain: groups presented by generators and relators, specialized to two-generator
-- one-relator presentations.
-- Layer triage:
-- `source-facing`: the specific Baumslag-Solitar group `⟨x, y | x⁻¹ y² x = y³⟩`, the element
-- `z = y⁴`, and the assertion that `{x, z}` generates the group but is not the defining-generator
-- set of any two-generator one-relator presentation.
-- `core/canonical`: the chosen-presentation owner datum `PresentedGroup R ≃* G`, together with
-- the chapter API `GroupPresentation.generatorImage`,
-- `GroupPresentation.closure_range_generatorImage_eq_top`, and `Subgroup.closure`.
-- `bridge/view`: a subset `S ⊆ G` is compared with the canonical defining-generator set of a
-- two-generator one-relator presentation via a chosen equivalence.
-- Domain sampling:
-- 1. `PresentedGroup R ≃* G` from Definition `2-1-1` is the chapter owner abstraction for a
--    chosen presentation of `G`.
-- 2. `GroupPresentation.generatorImage` is the canonical map sending a defining generator to its
--    image in `G`.
-- 3. `Set.range (GroupPresentation.generatorImage P)` is the canonical defining-generator subset
--    attached to a chosen presentation.
-- 4. `GroupPresentation.closure_range_generatorImage_eq_top` is the owner generation theorem for
--    those images.
-- 5. `Subgroup.closure` is the owner construction for the subgroup generated by a set of
--    elements.
-- Primitive vs. derived:
-- the source-facing primitive data are the specific presentation of `BS(2, 3)` and the
-- generating set `{x, y⁴}` inside that group. The property of admitting a one-relator
-- presentation on that generating set is a bridge property derived from the owner-side defining
-- generator set, so no ordered-coordinate wrapper around presentations is introduced.

namespace GroupPresentation

variable {G : Type u} [Group G]

/-- A subset `S` of `G` admits a two-generator one-relator presentation when `G` is isomorphic to
a group presented on two generators and one defining relator whose defining-generator set is
exactly `S`. -/
def HasOneRelatorPresentationOn (S : Set G) : Prop :=
  ∃ r : FreeGroup (Fin 2),
    ∃ P : PresentedGroup ({r} : Set (FreeGroup (Fin 2))) ≃* G,
      Set.range (generatorImage P) = S

end GroupPresentation

/-- The two generators of the Baumslag-Solitar presentation `⟨x, y | x⁻¹ y² x = y³⟩`. -/
inductive BaumslagSolitar23Generator
  | x
  | y
  deriving DecidableEq

namespace BaumslagSolitar23

open BaumslagSolitar23Generator

/-- The relator `y³ x⁻¹ y⁻² x`, equivalent to the defining relation `x⁻¹ y² x = y³`. -/
abbrev relator : FreeGroup BaumslagSolitar23Generator :=
  FreeGroup.of y ^ (3 : ℕ) * (FreeGroup.of x)⁻¹ * (FreeGroup.of y ^ (2 : ℕ))⁻¹ * FreeGroup.of x

/-- The singleton relator set defining the Baumslag-Solitar group `BS(2, 3)`. -/
abbrev relators : Set (FreeGroup BaumslagSolitar23Generator) := {relator}

/-- The Baumslag-Solitar group `BS(2, 3)` presented by `⟨x, y | x⁻¹ y² x = y³⟩`. -/
abbrev Group : Type := PresentedGroup relators

/-- The image of the generator `x` in `BS(2, 3)`. -/
abbrev x : Group := PresentedGroup.of BaumslagSolitar23Generator.x

/-- The image of the generator `y` in `BS(2, 3)`. -/
abbrev y : Group := PresentedGroup.of BaumslagSolitar23Generator.y

/-- The alternative generator `z = y⁴` used in Higman's counterexample. -/
abbrev z : Group := y ^ (4 : ℕ)

-- Proof sketch: in `BS(2, 3)` one computes `[z, x] = y²` and then `[[z, x], x] = y`, so `y`
-- lies in the subgroup generated by `x` and `z`. Since the original presentation already shows
-- that `x` and `y` generate the whole group, the pair `x, z` also generates it.
/-- The elements `x` and `z = y⁴` generate `BS(2, 3)`. -/
theorem closure_x_z_eq_top : Subgroup.closure ({x, z} : Set Group) = ⊤ := sorry

-- Proof sketch: assume a one-relator presentation whose defining-generator set is `{x, z}`.
-- Restrict the canonical quotient map to the subgroup generated by `x` and `z`, pass to the
-- normal closure of
-- `y`, and apply the staggered Freiheitssatz twice to show that the single relator must be
-- conjugate to `z₀³ z₁⁻²`. Magnus's theorem then forces the kernel to be the normal closure of
-- that relator, contradicting the existence of a one-relator presentation on the generating set
-- `{x, z}`.
/-- Higman's observation: the generating set `{x, z = y⁴}` does not support a one-relator
presentation of `BS(2, 3)`. -/
theorem not_hasOneRelatorPresentationOn_x_z :
    ¬ GroupPresentation.HasOneRelatorPresentationOn ({x, z} : Set Group) := sorry

end BaumslagSolitar23

open BaumslagSolitar23

/-- Theorem 2-2-5: in the Baumslag-Solitar group `⟨x, y | x⁻¹ y² x = y³⟩`, the pair `x` and
`z = y⁴` generates the whole group, but there is no presentation on these two generators with only
one defining relator. -/
-- Proof sketch: the original one-relator presentation defines the ambient group. Higman's
-- commutator calculation shows that `y` belongs to the subgroup generated by `x` and `y⁴`, so
-- that pair generates the group. The Freiheitssatz reductions and Magnus's theorem then exclude
-- any one-relator presentation whose defining-generator set is `{x, y⁴}`.
theorem baumslag_solitar23_yFourth_generating_pair_not_one_relator :
    Subgroup.closure ({x, z} : Set BaumslagSolitar23.Group) = ⊤ ∧
      ¬ GroupPresentation.HasOneRelatorPresentationOn ({x, z} : Set BaumslagSolitar23.Group) :=
  sorry

/-! ### Definition_2_2_6 (from Items/Chap02) -/
open FreeGroup

-- Layer triage:
-- `source-facing`: Conway's family of groups `F_n`, given by `n` generators with the cyclic
-- relators `x_i x_{i+1} = x_{i+2}`.
-- `core/canonical`: `PresentedGroup` is mathlib's owner abstraction for groups given by
-- generators and relators, and `ZMod n` is the clean cyclic indexing type for the generator
-- family.
-- `bridge/view`: the textbook list
-- `x₁ x₂ = x₃, ..., x_{n-1} x_n = x₁, x_n x₁ = x₂`
-- is encoded as the uniform cyclic relator family indexed by `i : ZMod n`.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the canonical quotient attached to a relator set in the free group.
-- 2. `PresentedGroup.of` supplies the canonical generators in the quotient.
-- 3. `PresentedGroup.one_of_mem` is the owner lemma saying a listed relator becomes trivial in the
--    presented group.
-- Primitive vs. derived:
-- the primitive data are the cyclic relators in the free group; the group `F_n` is the derived
-- canonical quotient by those relators, so no auxiliary wrapper structure is introduced.

namespace Conway

/-- The canonical cyclic relator `x_i x_{i+1} x_{i+2}^{-1}` used in Conway's presentations. -/
def relator (n : ℕ+) (i : ZMod n) : FreeGroup (ZMod n) :=
  of i * of (i + 1) * (of (i + 2))⁻¹

/-- The relator set for Conway's balanced presentation on `n` cyclically indexed generators. -/
def relators (n : ℕ+) : Set (FreeGroup (ZMod n)) :=
  Set.range (relator n)

/-- Definition 2-2-6: Conway's group `F_n` is the group presented by cyclically indexed generators
`x_i` with relators `x_i x_{i+1} = x_{i+2}` for all `i : ZMod n`, which reproduces the textbook
list `x₁ x₂ = x₃, ..., x_{n-1} x_n = x₁, x_n x₁ = x₂`. -/
abbrev F (n : ℕ+) : Type :=
  PresentedGroup (relators n)

notation "F_" n:arg => Conway.F n

/-- Conway's defining relation holds between the canonical generators of `F_n`. -/
-- Proof sketch: `PresentedGroup.one_of_mem` makes the relator word
-- `x_i x_{i+1} x_{i+2}^{-1}` trivial in the quotient, and simplifying that quotient equation
-- recovers the textbook relation `x_i x_{i+1} = x_{i+2}`.
theorem generator_relation (n : ℕ+) (i : ZMod n) :
    (PresentedGroup.of i : F_ n) * PresentedGroup.of (i + 1) = PresentedGroup.of (i + 2) := by
  have h : PresentedGroup.mk (relators n) (relator n i) = (1 : F_ n) :=
    PresentedGroup.one_of_mem (Set.mem_range_self i)
  have h' : ((PresentedGroup.of i : F_ n) * PresentedGroup.of (i + 1)) *
      (PresentedGroup.of (i + 2))⁻¹ = 1 := by
    simpa [relator, PresentedGroup.of, mul_assoc] using h
  have h'' := congrArg (fun x : F_ n ↦ x * PresentedGroup.of (i + 2)) h'
  simpa [mul_assoc] using h''

end Conway

/-! ### Definition_2_2_7 (from Items/Chap02) -/
open FreeGroup

-- Layer triage:
-- `source-facing`: the cyclically indexed presentation `F_{r,n}` with `n` generators and the
-- relators `x_i x_{i+1} ... x_{i+r-1} = x_{i+r}`.
-- `core/canonical`: `PresentedGroup` is mathlib's owner abstraction for a group given by
-- generators and relators, and `ZMod n` is the canonical cyclic index type.
-- `bridge/view`: the displayed cyclic list of relators is encoded uniformly by a relator family
-- indexed by `i : ZMod n`, using a list product for the left-hand side word.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the canonical group attached to a relator set in `FreeGroup`.
-- 2. `PresentedGroup.mk` and `PresentedGroup.one_of_mem` express that listed relators become
--    trivial in the quotient.
-- 3. `Conway.F` from the previous item is the `r = 2` specialization of the same owner-side
--    presentation pattern, so the generalized file should bridge back to it explicitly.
-- Primitive vs. derived:
-- the primitive data are the cyclic relator words indexed by `r : ℕ`; positivity of `r` is not
-- part of the canonical construction, while the group `F_{r,n}` is the derived quotient by those
-- relators, so no auxiliary package around the presentation is introduced.

namespace Conway.Generalized

/-- The cyclic relator `x_i x_{i+1} ... x_{i+r-1} x_{i+r}^{-1}` used in the presentation of
`F_{r,n}`. -/
def relator (r : ℕ) (n : ℕ+) (i : ZMod n) : FreeGroup (ZMod n) :=
  ((List.range r).map fun j ↦ of (i + j)).prod * (of (i + r))⁻¹

/-- The relator set for the cyclic presentation of `F_{r,n}` on generators indexed by `ZMod n`. -/
def relators (r : ℕ) (n : ℕ+) : Set (FreeGroup (ZMod n)) :=
  Set.range (relator r n)

/-- Definition 2-2-7: `F_{r,n}` is the group presented by cyclically indexed generators `x_i`
with relators `x_i x_{i+1} ... x_{i+r-1} = x_{i+r}` for all `i` modulo `n`. -/
abbrev F (r : ℕ) (n : ℕ+) : Type :=
  PresentedGroup (relators r n)

notation "F_{" r "," n "}" => Conway.Generalized.F r n

/-- The defining relation of `F_{r,n}` holds between its canonical generators. -/
-- Proof sketch: `PresentedGroup.one_of_mem` makes the relator word
-- `x_i x_{i+1} ... x_{i+r-1} x_{i+r}^{-1}` trivial in the quotient; multiplying by `x_{i+r}` on
-- the right recovers the source-facing relation.
theorem generator_relation (r : ℕ) (n : ℕ+) (i : ZMod n) :
    ((List.range r).map fun j ↦ (PresentedGroup.of (i + j) : F_{r,n})).prod =
      PresentedGroup.of (i + r) := by
  have hrel : PresentedGroup.mk (relators r n) (relator r n i) = (1 : F_{r,n}) :=
    PresentedGroup.one_of_mem (Set.mem_range_self i)
  have h : ((List.range r).map fun j ↦ (PresentedGroup.of (i + j) : F_{r,n})).prod *
      (PresentedGroup.of (i + r) : F_{r,n})⁻¹ = 1 := by
    simpa [relator, PresentedGroup.of, map_list_prod] using hrel
  have h' := congrArg (fun x : F_{r,n} ↦ x * PresentedGroup.of (i + r)) h
  simpa [mul_assoc] using h'

/-- The generalized relator specializes to Conway's original relator when `r = 2`. -/
theorem relator_two (n : ℕ+) (i : ZMod n) :
    relator 2 n i = Conway.relator n i := by
  rw [relator, show List.range 2 = [0, 1] by rfl, Conway.relator]
  simp

/-- The generalized cyclic relator set specializes to Conway's original relator set when `r = 2`.
-/
theorem relators_two (n : ℕ+) :
    relators 2 n = Conway.relators n := by
  ext w
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨i, (relator_two n i).symm⟩
  · exact ⟨i, relator_two n i⟩

/-- The generalized presentation `F_{r,n}` recovers Conway's `F_n` when `r = 2`. -/
theorem F_two (n : ℕ+) : F_{2,n} = F_ n := by
  simp [F, Conway.F, relators_two n]

end Conway.Generalized
