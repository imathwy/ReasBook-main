import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_6_1 (from Items/Chap04) -/
universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: the two poles `E` and `E*`, admissible sector factorizations, and the bipolar
  decomposition of a group into the fixed subgroup piece and four sectors.
- `core/canonical`: the involution on poles is the standard `Star`/`InvolutiveStar` API, and
  disjointness of the sector family is recorded by mathlib's `Pairwise (Disjoint on ...)`.
- `bridge/view`: coercing a `BipolarStructure` to its sector family `Pole → Pole → Set G`, and the
  owner-side irreducibility predicate `B.IsIrreducible g`.

Domain sampling:
1. `Star` and `InvolutiveStar` are mathlib's owner abstractions for a type equipped with an
   involution.
2. `Pairwise (Disjoint on f)` is the canonical mathlib surface for a pairwise disjoint indexed
   family of sets.
3. `BipolarStructure` is the chapter-facing owner abstraction for Definition `4-6-1`.
4. `HasSectorFactorization` is the primitive source-facing predicate recording admissible products
   through a pole sequence, while `B.IsIrreducible g` is its canonical owner-side view.

Primitive vs. derived:
the primitive data are the subgroup piece `F`, the sector family `sector`, and the axioms they
satisfy. The old five-piece indexing wrapper was only bookkeeping for cover/disjointness, so the
owner now stores those axioms directly instead of exposing a second public piece-index type.
The primitive factorization predicate itself only depends on the multiplicative structure, so it is
stated at the weaker `Monoid` level and then reused inside the group-level owner.
In particular, the source nontriviality axiom `EE* ≠ ∅` belongs to the owner itself rather than to
an auxiliary later predicate, while irreducibility is derived from the primitive factorization
predicate and therefore belongs in the owner file rather than a later theorem file.
-/

/-- The two poles used to label the non-subgroup pieces of a bipolar structure. -/
inductive Pole where
  | E
  | EStar
  deriving DecidableEq, Repr, Fintype

namespace Pole

/-- The involution exchanging `E` and `E*`. -/
instance : Star Pole where
  star
    | .E => .EStar
    | .EStar => .E

/-- The pole involution is an involution. -/
instance : InvolutiveStar Pole where
  star_involutive
    | .E => rfl
    | .EStar => rfl

@[simp] theorem star_E : star E = EStar := rfl

@[simp] theorem star_EStar : star EStar = E := rfl

end Pole

open Function Pole

section

variable {G : Type u} [Monoid G]

/-- A length-`n` sector factorization of `g` is an ordered product `g = g₁ ⋯ gₙ`
together with a pole sequence `X₀, ..., Xₙ` such that each factor lies in `Xᵢ₋₁* Xᵢ`. -/
def HasSectorFactorization (sector : Pole → Pole → Set G) (g : G) (n : ℕ) : Prop :=
  ∃ factors : Fin n → G,
    ∃ poles : Fin (n + 1) → Pole,
      g = (List.ofFn factors).prod ∧
        ∀ i : Fin n, factors i ∈ sector (star (poles i.castSucc)) (poles i.succ)

end

/-- Definition 4-6-1: a bipolar structure on a group is a decomposition of the group
into the subgroup piece `F` and the four sectors `EE`, `EE*`, `E*E`, and `E*E*`,
satisfying the subgroup, nontriviality, right-translation, inverse, product, and boundedness
axioms from the text. -/
structure BipolarStructure (G : Type u) [Group G] where
  /-- The subgroup piece `F`. -/
  F : Subgroup G
  /-- The sector `XY` for `X,Y ∈ {E,E*}`. -/
  sector : Pole → Pole → Set G
  /-- The fixed subgroup piece together with the four sectors cover the whole group. -/
  pieces_cover :
    (F : Set G) ∪ ⋃ X : Pole, ⋃ Y : Pole, sector X Y = (Set.univ : Set G)
  /-- The fixed subgroup piece is disjoint from every sector. -/
  fixed_disjoint_sector (X Y : Pole) :
    Disjoint (F : Set G) (sector X Y)
  /-- Distinct sectors are pairwise disjoint. -/
  sector_pairwiseDisjoint :
    Pairwise (Disjoint on fun p : Pole × Pole ↦ sector p.1 p.2)
  /-- The mixed sector `EE*` is nonempty. -/
  eeStar_nonempty : (sector E EStar).Nonempty
  /-- Right multiplication by an element of `F` preserves each sector. -/
  sector_mul_mem {X Y : Pole} {g f : G} (hg : g ∈ sector X Y) (hf : f ∈ F) :
    g * f ∈ sector X Y
  /-- Inversion sends the sector `XY` to the sector `YX`. -/
  inv_mem_sector {X Y : Pole} {g : G} (hg : g ∈ sector X Y) :
    g⁻¹ ∈ sector Y X
  /-- Multiplying an `XY` element by a `Y*Z` element lands in `XZ`. -/
  mul_mem_sector {X Y Z : Pole} {g h : G} (hg : g ∈ sector X Y)
      (hh : h ∈ sector (star Y) Z) :
    g * h ∈ sector X Z
  /-- The lengths of admissible sector factorizations of a fixed group element are
  uniformly bounded. -/
  bounded_factorizations (g : G) :
    ∃ N : ℕ, ∀ n : ℕ, HasSectorFactorization sector g n → n ≤ N

namespace BipolarStructure

variable {G : Type u} [Group G]

/-- A bipolar structure is used via its sector family. -/
instance : CoeFun (BipolarStructure G) (fun _ ↦ Pole → Pole → Set G) where
  coe B := B.sector

/-- Every group element lies either in the fixed subgroup piece or in one of the four sectors. -/
theorem mem_fixed_or_mem_sector (B : BipolarStructure G) (g : G) :
    g ∈ B.F ∨ ∃ X Y : Pole, g ∈ B X Y := by
  have hg : g ∈ (B.F : Set G) ∪ ⋃ X : Pole, ⋃ Y : Pole, B X Y := by
    rw [B.pieces_cover]
    simp
  rcases hg with hgF | hgSectors
  · exact Or.inl hgF
  · rcases Set.mem_iUnion.1 hgSectors with ⟨X, hgX⟩
    rcases Set.mem_iUnion.1 hgX with ⟨Y, hgXY⟩
    exact Or.inr ⟨X, Y, hgXY⟩

/-- Distinct sectors are disjoint. -/
theorem sector_disjoint (B : BipolarStructure G) {X Y Z W : Pole}
    (h : (X, Y) ≠ (Z, W)) :
    Disjoint (B X Y) (B Z W) :=
  B.sector_pairwiseDisjoint h

/-- Inversion shows that the other mixed sector `E*E` is nonempty as well. -/
theorem eStarE_nonempty (B : BipolarStructure G) : (B EStar E).Nonempty := by
  rcases B.eeStar_nonempty with ⟨g, hg⟩
  exact ⟨g⁻¹, B.inv_mem_sector hg⟩

/-- The chapter-facing irreducibility predicate: `g` admits no admissible two-step sector
factorization. -/
def IsIrreducible (B : BipolarStructure G) (g : G) : Prop :=
  ¬ HasSectorFactorization B g 2

@[simp] theorem isIrreducible_iff (B : BipolarStructure G) (g : G) :
    B.IsIrreducible g ↔ ¬ HasSectorFactorization B g 2 := Iff.rfl

end BipolarStructure

/-! ### Lemma_4_6_2 (from Items/Chap04) -/
universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: sector membership statements `g ∈ XY`, `h ∈ YZ`, the irreducibility of `h`,
  and the conclusion that `gh` is either fixed or lies in a sector with left pole `X`.
- `core/canonical`: `BipolarStructure` is the owner abstraction for the subgroup piece `F`, the
  sector family, and the owner-side irreducibility predicate `B.IsIrreducible g`.
- `bridge/view`: this lemma converts the source word “irreducible” into the canonical owner API
  from Definition `4-6-1`.

Domain sampling:
1. `BipolarStructure` is the project owner for the five-piece bipolar decomposition.
2. Its coercion to `Pole → Pole → Set G` supplies the sector notation `B X Y`.
3. `HasSectorFactorization` from Definition `4-6-1` is the primitive notion for admissible
   products along poles.
4. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner API for the source
   notion “`g` admits no length-two admissible sector factorization”.

Primitive vs. derived:
the primitive source data are the bipolar structure `B`, the poles `X,Y,Z`, and the elements
`g,h` with their sector-membership assumptions. The irreducibility notion is already part of the
owner-side API imported from Definition `4-6-1`, so this file only states the first structural
consequence of that owner predicate.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-2: if `g ∈ XY`, `h ∈ YZ`, and `h` admits no length-two admissible sector
factorization, then `gh` lies either in the fixed subgroup piece `F` or in some sector `XW`. -/
-- Proof sketch: if `gh ∉ F`, the covering axiom places `gh` in some sector `UW`. If `U ≠ X`,
-- then `U = star X`; inversion puts `g⁻¹` in `YX`, so the equality `h = g⁻¹ * (gh)` gives a
-- forbidden length-two sector factorization of `h`. Hence the only non-fixed possibility is a
-- sector with left pole `X`.
theorem mul_mem_fixed_or_sector_of_irreducible
    (B : BipolarStructure G) {X Y Z : Pole} {g h : G}
    (hg : g ∈ B X Y) (hh : h ∈ B Y Z) (hirr : B.IsIrreducible h) :
    g * h ∈ B.F ∨ ∃ W : Pole, g * h ∈ B X W := sorry

end

end BipolarStructure

/-! ### Lemma_4_6_3 (from Items/Chap04) -/
universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: products `g * h` of irreducible sector elements with `g ∈ XY` and `h ∈ YZ`.
- `core/canonical`: `BipolarStructure`, its fixed subgroup `B.F`, its sector family `B X Y`, and
  the sector-factorization predicate `HasSectorFactorization`.
- `bridge/view`: the chapter-facing irreducibility predicate `B.IsIrreducible g` together with the
  union `(B.F : Set G) ∪ B X Z`, which records the textbook phrase “an irreducible element of
  `F ∪ XZ`” without introducing a surrogate wrapper.

Domain sampling:
1. `BipolarStructure` is the owner abstraction for the bipolar axioms and sector notation.
2. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner for irreducibility.
3. `HasSectorFactorization` is the primitive owner-side predicate for admissible sector
   decompositions.
4. The subgroup piece is used canonically through the subgroup-to-set coercion `(B.F : Set G)`.

Primitive vs. derived:
the primitive public data are the bipolar structure `B`, poles `X Y Z`, elements `g h`, their
sector-membership assumptions, and the primitive factorization predicate behind irreducibility.
The public source-facing statement uses the derived owner predicate `B.IsIrreducible` for both the
inputs and the output, while the union-membership conclusion remains the direct set-level view.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-3: if `g ∈ XY` and `h ∈ YZ` are both irreducible, meaning that neither admits a
length-two sector factorization, then `gh` is an irreducible element of `F ∪ XZ`. -/
-- Proof sketch: Lemma `4-6-2` gives the membership of `g * h` in `F ∪ XZ`. If `g * h` admitted a
-- length-two sector factorization, rewrite `g = p * (q * h⁻¹)` and use irreducibility of `h` to
-- show `q * h⁻¹ ∈ F`; then the bipolar axioms force `g` and `h` into incompatible sectors,
-- contradicting the irreducibility assumptions.
theorem mul_mem_fixed_union_sector_and_isIrreducible
    (B : BipolarStructure G) {X Y Z : Pole} {g h : G}
    (hg : g ∈ B X Y) (hh : h ∈ B Y Z)
    (hgirr : B.IsIrreducible g) (hhirr : B.IsIrreducible h) :
    g * h ∈ (B.F : Set G) ∪ B X Z ∧ B.IsIrreducible (g * h) := sorry

end

end BipolarStructure

/-! ### Lemma_4_6_4 (from Items/Chap04) -/
universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: an element of a sector `XY` that is irreducible, meaning it does not admit a
  two-step factorization through an intermediate pole.
- `core/canonical`: `BipolarStructure` from Definition `4-6-1`, its sector family `B X Y`, its
  fixed subgroup `B.F`, and the owner predicate `HasSectorFactorization`.
- `bridge/view`: the right- and left-multiplication actions of the fixed subgroup on a sector,
  expressed directly through sector membership together with the chapter-facing irreducibility
  predicate `B.IsIrreducible g`.

Domain sampling:
1. `BipolarStructure` is the owner abstraction for the bipolar axioms.
2. `B.sector_mul_mem` is the canonical owner-side API for the axiom that right multiplication by an
   element of `F` preserves a sector.
3. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner for irreducibility.
4. `B.inv_mem_sector` is the owner-side API for the inverse axiom used in the second clause.

Primitive vs. derived:
the primitive public data for this item are a bipolar structure `B`, poles `X Y`, an element
`g ∈ B X Y`, the irreducibility predicate `B.IsIrreducible g`, and an element `f ∈ B.F`. The old
local structure `IsIrreducibleIn` duplicated those primitives, so the public surface is refined to
the canonical conjunction of sector membership and the owner-side irreducibility API instead.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-4: right multiplication by an element of the fixed subgroup preserves
irreducibility in a sector. -/
-- Proof sketch: use the bipolar axiom that right multiplication by an element of `F` preserves the
-- sector `XY`. If `g * f` factored through some intermediate pole, multiply the second factor on
-- the right by `f⁻¹ ∈ F` to obtain a forbidden factorization of `g`.
theorem isIrreducibleIn_mul_fixed_right
    (B : BipolarStructure G) {X Y : Pole} {g f : G}
    (hg : g ∈ B X Y) (hgirr : B.IsIrreducible g) (hf : f ∈ B.F) :
    g * f ∈ B X Y ∧ B.IsIrreducible (g * f) := sorry

/-- Left multiplication by an element of the fixed subgroup also preserves irreducibility in a
sector. -/
-- Proof sketch: apply the inverse axiom to transport irreducibility of `g` in `XY` to
-- irreducibility of `g⁻¹` in `YX`, use the right-multiplication statement on `g⁻¹ * f⁻¹`, and then
-- invert again to conclude that `f * g` is irreducible in `XY`.
theorem isIrreducibleIn_mul_fixed_left
    (B : BipolarStructure G) {X Y : Pole} {g f : G}
    (hg : g ∈ B X Y) (hgirr : B.IsIrreducible g) (hf : f ∈ B.F) :
    f * g ∈ B X Y ∧ B.IsIrreducible (f * g) := sorry

end

end BipolarStructure

/-! ### Theorem_4_6_5 (from Items/Chap04) -/
universe u v w

set_option autoImplicit false

open Subgroup

/-!
Primary domain: Bass-LinearRepresentations_Serre_1977 type decompositions of groups with bipolar structures.

Layer triage:
- `source-facing`: a group admitting a bipolar structure, and the two alternative decompositions
  from the theorem, namely a nontrivial amalgamated free product or an HNN extension.
- `core/canonical`: `Nonempty (BipolarStructure G)`, `Subgroup.amalgamatedProductAlong`, and
  `HNNExtension G₀ A B φ`.
- `bridge/view`: a multiplicative equivalence from the ambient group onto one of those canonical
  owner constructions.

Domain sampling:
1. `BipolarStructure` from Definition `4-6-1` is the project owner for the bipolar axioms.
2. `Subgroup.amalgamatedProductAlong` from Definition `4-2-9` is the chapter-facing owner for a
   two-factor free product with amalgamation.
3. `HNNExtension G₀ A B φ` is mathlib's canonical owner abstraction for HNN extensions.
4. `MulEquiv` is the canonical API for identifying the ambient group with one of these
   constructions.

Primitive vs. derived:
the primitive public content is the ambient group `G` together with either a bipolar structure or
one of the two source-facing decomposition data sets appearing directly in the theorem statement.
The exact subgroup pieces and stable-letter data belong to those existential alternatives, while
the theorem itself is the direct equivalence between `Nonempty (BipolarStructure G)` and
admitting one of the two canonical owner-level decomposition types.
-/

section

/-- Theorem 4-6-5: a group has a bipolar structure if and only if it is either a nontrivial free
product with amalgamation, including the ordinary free product case, or an HNN extension. -/
-- Proof sketch: for the forward direction, build the subgroups `G₁` and `G₂` from the fixed part
-- and the irreducible sector pieces of a bipolar structure, then distinguish whether the sector
-- `EE*` is empty or not to obtain respectively an amalgamated-product or HNN-extension
-- decomposition. For the reverse direction, use the canonical bipolar structures constructed
-- earlier for amalgamated free products and for HNN extensions.
theorem nonempty_bipolarStructure_iff_nontrivialAmalgamatedFreeProduct_or_hnnExtension
    (G : Type u) [Group G] :
    Nonempty (BipolarStructure G) ↔
      (∃ (G₁ : Type v) (_ : Group G₁) (G₂ : Type w) (_ : Group G₂)
        (A : Subgroup G₁) (B : Subgroup G₂) (e : A ≃* B)
        (_ : G ≃* amalgamatedProductAlong e),
          A < ⊤ ∧ B < ⊤) ∨
      ∃ (G₀ : Type v) (_ : Group G₀) (A : Subgroup G₀) (B : Subgroup G₀) (φ : A ≃* B),
        Nonempty (G ≃* HNNExtension G₀ A B φ) := sorry

end

/-! ### Theorem_4_6_6 (from Items/Chap04) -/
universe u v w

set_option autoImplicit false

open Monoid
open HNNExtension
open scoped Pointwise

/-!
Primary domain: subgroup decompositions in free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a subgroup of a two-factor amalgamated product or of an HNN extension whose
  intersections with conjugates of the amalgamated subgroup or of the HNN associated subgroups are
  trivial, and the resulting free-product decomposition of that subgroup.
- `core/canonical`: `Subgroup.amalgamatedProductAlong` and `HNNExtension` are the ambient owners,
  while `IsKuroshFactorDecomposition` is the project owner for the resulting free-product
  decomposition with one distinguished free factor.
- `bridge/view`: the amalgamated-product decomposition is obtained internally by specializing the
  Chapter 1 Kurosh theorem to the canonical two-factor pushout, while the public subgroup factors
  are stated directly as intersections with conjugates of `(left e).range` and `(right e).range`.
  In the HNN case the factors are likewise expressed directly as the corresponding
  `Subgroup.comap` intersections inside `H`.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong e`, together with `left`, `right`, and `base`, is the
   chapter owner for two-factor free products with amalgamation.
2. `HNNExtension G A B φ`, together with `of`, is mathlib's canonical owner for HNN extensions and
   the embedded base group.
3. `IsKuroshFactorDecomposition` and `kuroshFactorFamily` from Proposition `1-11-24` are the
   project's canonical owners for the subgroup free-product decomposition data.
4. `MulAut.conj` and `Subgroup.comap` are the canonical APIs for expressing the subgroup factors
   as actual intersections inside the subgroup `H`; the generic Chapter 1
   `conjugateFactorIntersectionSubgroup` remains only an internal bridge.

Primitive vs. derived:
- primitive source-facing data: the subgroup `H` and the hypothesis that it is disjoint from every
  conjugate of the amalgamated subgroup or of the embedded HNN associated subgroups;
- derived API: the free subgroup factor, the family of subgroup factors, the free-product
  equivalence, and the identification of each factor with the corresponding conjugate-intersection
  subgroup.

The finite-generation and nontriviality hypotheses from the textbook are omitted below: the
canonical Kurosh/Bass-LinearRepresentations_Serre_1977 decomposition statements do not require them.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type v} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e
/-- Theorem 4-6-6 (1): in a two-factor free product with amalgamation, a subgroup that meets
every conjugate of the amalgamated subgroup trivially is a free product of one free factor
together with subgroup factors which are the corresponding conjugate intersections with the left
or right factor subgroups. -/
-- Proof sketch: specialize Proposition `1-11-24` to the canonical two-factor pushout presenting
-- `P`. The resulting Kurosh factors identify with the direct subgroup intersections with
-- conjugates of `(left e).range` and `(right e).range`, viewed as subgroups of `H`, so the
-- theorem surface stays at the owner level `left`/`right` rather than the internal `Bool`-indexed
-- pushout presentation.
theorem exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong
    (H : Subgroup P)
    (hbase : ∀ p : P, Disjoint H (MulAut.conj p⁻¹ • (base e).range)) :
    ∃ (κ : Type w) (K : κ → Subgroup H) (F : Subgroup H)
      (ψ : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F ψ ∧
        ∀ j,
          ∃ p : P,
            K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • (left e).range) ∨
              K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • (right e).range) := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Theorem 4-6-6 (2): in an HNN extension, a subgroup that meets every conjugate of the embedded
associated subgroups trivially is a free product of one free factor together with subgroup factors
which are the corresponding conjugate intersections with conjugates of the embedded base subgroup.
-/
-- Proof sketch: let the subgroup act on the Bass-LinearRepresentations_Serre_1977 tree of the HNN extension, or equivalently
-- use the bipolar structure from Section `6`. Trivial intersections with conjugates of the base
-- associated subgroups `A` and `B` force the edge stabilizers to be trivial, so the subgroup is
-- the free product of its vertex stabilizers together with a free group. Those vertex stabilizers
-- are exactly the intersections with conjugates of the embedded base subgroup.
theorem exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension
    (H : Subgroup E)
    (hA : ∀ p : E, Disjoint H (MulAut.conj p⁻¹ • A.map of))
    (hB : ∀ p : E, Disjoint H (MulAut.conj p⁻¹ • B.map of)) :
    ∃ (κ : Type w) (K : κ → Subgroup H) (F : Subgroup H)
      (ψ : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F ψ ∧
        ∀ j,
          ∃ p : E,
            K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • of.range) := sorry

end HNN

/-! ### Corollary_4_6_7 (from Items/Chap04) -/
universe u v

set_option autoImplicit false

open scoped Pointwise

/-!
Primary domain: subgroup structure of free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a subgroup of an amalgamated product or of an HNN extension, together with the
  hypothesis that it has trivial intersection with every conjugate of the factor subgroups or of
  the embedded base subgroup, and the conclusion that the subgroup is free.
- `core/canonical`: `Subgroup.amalgamatedProductAlong`, `HNNExtension`,
  `IsKuroshFactorDecomposition`, and `IsFreeGroup` are the owner abstractions for the ambient
  groups, the subgroup free-product decomposition, and the freeness conclusion.
- `bridge/view`: the chapter-specific existence theorems from Theorem `4-6-6`
  `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong` and
  `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`
  bridge the present disjointness hypotheses to the canonical decomposition owner. The source
  hypotheses here are stated directly through the canonical conjugation action on the factor ranges
  `(Subgroup.amalgamatedProductAlong.left e).range`,
  `(Subgroup.amalgamatedProductAlong.right e).range`, and the HNN base range `(of).range`; in the
  HNN case the base-range hypothesis is stronger than the associated-subgroup disjointness used by
  Theorem `4-6-6`.

Domain sampling:
1. `IsKuroshFactorDecomposition` from Proposition `1-11-24` is the canonical project owner for
   the free-product decomposition data underlying both corollaries.
2. `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong` from
   Theorem `4-6-6` is the chapter-specialized bridge theorem for the amalgamated-product case.
3. `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`
   from Theorem `4-6-6` is the corresponding HNN-extension bridge theorem.
4. `Subgroup.amalgamatedProductAlong` with `left` and `right`, and `HNNExtension` with `of`, are
   the canonical ambient owners for the two group constructions.

Primitive vs. derived:
- primitive public data: the subgroup and the disjointness hypotheses against conjugates of the
  canonical factor or base subgroups;
- derived API: the Kurosh- or Bass-LinearRepresentations_Serre_1977-type free-product decomposition whose extra factors are
  forced to be trivial, leaving only a free subgroup factor.

The textbook includes finite generation, but for the freeness conclusion that hypothesis is
redundant and is omitted from the canonical statements below.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type v} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e

/-- Corollary 4-6-7 (1): in a free product with amalgamation, a subgroup that meets every
conjugate of each factor subgroup trivially is free. -/
-- Proof sketch: apply the chapter owner
-- `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong`. Its
-- subgroup factors are intersections with conjugates of the left or right factor ranges, so the
-- present disjointness hypotheses make those factors trivial. The remaining distinguished factor
-- is free, and the resulting free-product decomposition therefore identifies `K` with a free
-- group.
theorem isFreeGroup_of_disjoint_factor_conjugates_amalgamatedProductAlong
    (K : Subgroup P)
    (hleft : ∀ p : P, Disjoint K (MulAut.conj p⁻¹ • (left e).range))
    (hright : ∀ p : P, Disjoint K (MulAut.conj p⁻¹ • (right e).range)) :
    IsFreeGroup K := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Corollary 4-6-7 (2): in an HNN extension, a subgroup that meets every conjugate of the
embedded base subgroup trivially is free. -/
-- Proof sketch: apply the chapter owner
-- `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`.
-- The present hypothesis on conjugates of `(of).range` is stronger than the owner's hypotheses on
-- conjugates of `A.map of` and `B.map of`, and its subgroup factors are intersections with
-- conjugates of the canonical base range `(of).range`. Hence every such factor is trivial, so only
-- the distinguished free factor remains.
theorem isFreeGroup_of_disjoint_base_conjugates_hnnExtension
    (K : Subgroup E)
    (hbase : ∀ p : E, Disjoint K (MulAut.conj p⁻¹ • (of).range)) :
    IsFreeGroup K := sorry

end HNN

/-! ### Lemma_4_6_8 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open Monoid.CoprodI
open Monoid.CoprodI.Word
open HNNExtension
open HNNExtension.NormalWord
open scoped Pointwise

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

/-!
Primary domain: subgroup structure of free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a finitely generated subgroup of an amalgamated free product or an HNN
  extension, together with the dichotomy that it either lies in a conjugate of a factor/base or a
  conjugate of it contains a cyclically reduced element of length at least `2`.
- `core/canonical`: `Subgroup.amalgamatedProductAlong` with its factor embeddings `left` and
  `right`, `HNNExtension` with its base embedding `of`, subgroup conjugation via `MulAut.conj •`,
  and the chapter's cyclically reduced word owners
  `Monoid.CoprodI.Word.IsCyclicallyReduced` and
  `HNNExtension.NormalWord.ReducedWord.IsCyclicallyReduced`.
- `bridge/view`: the textbook "cyclically reduced element of length at least two" is rendered by
  the existence of a cyclically reduced reduced word of syllable-list length at least `2` whose
  canonical evaluation lies in a conjugate of the subgroup.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong`, together with
   `Subgroup.amalgamatedProductAlong.left`, `right`, and `ofWord`, is the chapter-facing owner for
   free products with amalgamation.
2. `Monoid.CoprodI.Word.IsCyclicallyReduced` from Theorem `4-2-12` is the project owner for
   cyclically reduced source words in an amalgamated product.
3. `HNNExtension.NormalWord.ReducedWord G B A` and `ReducedWord.toHNNExtension` are the source
   owner and evaluation bridge for HNN normal words, while `ReducedWord.IsCyclicallyReduced` from
   Theorem `4-2-8` is the project owner for cyclic reducedness.
4. `MulAut.conj p • K` is the canonical expression for a conjugate subgroup.

Primitive vs. derived:
the primitive public data are the ambient amalgamated product or HNN extension, the subgroup
`K`, and the finite-generation hypothesis `K.FG`. The conjugate factor/base subgroups and the
existence of a cyclically reduced element are stated directly in terms of the canonical owner-side
embeddings and reduced-word APIs, without introducing any extra package or surrogate notion.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type u} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e
local notation "Family" => Monoid.CoprodI.twoFactorFamily G1 G2
local notation "W" => Word Family
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/-- Lemma 4-6-8 (1): a finitely generated subgroup of a nontrivial free product with amalgamation
is either contained in a conjugate of one of the two factor subgroups, or some conjugate of that
subgroup contains a cyclically reduced element represented by a reduced word of length at least
two. -/
-- Proof sketch: induct on the sum of the normal-form lengths of a finite generating set of the
-- subgroup. If every generator has length `1`, the subgroup lies in a conjugate of one factor.
-- Otherwise, after conjugating so that all generators begin and end in the same factor, one
-- shortens the total length by peeling off a common initial syllable. If this reduction process
-- ever fails, a product of two generators yields a cyclically reduced word of length at least `2`
-- inside a conjugate of the subgroup.
theorem subgroup_le_conjugate_factor_or_exists_cyclicallyReduced_conjugate_amalgamatedProductAlong
    (K : Subgroup P) (hK : K.FG) :
    (∃ p : P, K ≤ MulAut.conj p • (left e).range) ∨
      (∃ p : P, K ≤ MulAut.conj p • (right e).range) ∨
      ∃ p : P, ∃ w : W,
        w.IsCyclicallyReduced ιA ιB ∧
          2 ≤ w.toList.length ∧
          ofWord e w ∈ MulAut.conj p • K := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Lemma 4-6-8 (2): a finitely generated subgroup of an HNN extension is either contained in a
conjugate of the embedded base group, or some conjugate of that subgroup contains a cyclically
reduced HNN word with at least two stable-letter syllables. -/
-- Proof sketch: repeat the amalgamated-product induction with Britton normal forms in place of
-- free-product normal forms. If every generator has no stable-letter syllable, the subgroup lies
-- in a conjugate of the base. Otherwise, conjugating by a suitable initial base syllable reduces
-- the total stable-letter length unless one already obtains a cyclically reduced HNN word of
-- length at least `2` in a conjugate of the subgroup.
theorem subgroup_le_conjugate_base_or_exists_cyclicallyReduced_conjugate_hnnExtension
    (K : Subgroup E) (hK : K.FG) :
    (∃ p : E, K ≤ MulAut.conj p • (of).range) ∨
      ∃ p : E, ∃ w : ReducedWord G B A,
        w.IsCyclicallyReduced ∧
          2 ≤ w.toList.length ∧
          w.toHNNExtension φ ∈ MulAut.conj p • K := sorry

end HNN

/-! ### Theorem_4_6_9 (from Items/Chap04) -/
universe u

open scoped MatrixGroups

set_option autoImplicit false

section

variable {K : Type u} [Field K]

/-!
Primary domain: Bass-LinearRepresentations_Serre_1977 decompositions of matrix groups over polynomial rings.

Layer triage:
- `source-facing`: the decomposition of `GL₂(K[x])` as the amalgamated free product of the
  constant copy of `GL₂(K)` and the upper triangular subgroup `T(K[x])`, with common subgroup
  `T(K)`.
- `core/canonical`: `Subgroup.amalgamatedProductComparison`, together with the owner-side subgroup
  declarations `constantLinearSubgroup` and `upperTriangularSubgroup`.
- `bridge/view`: Proposition `3-13-8` already provides the constant-coefficient subgroup, the
  upper triangular subgroup, and the identification of `T(K)` with their intersection, so this
  file should recall the resulting comparison theorem directly rather than rebuild a local
  `Monoid.PushoutI` presentation.

Domain sampling:
1. `Subgroup.amalgamatedProductComparison` from Proposition `3-12-5` is the chapter owner for the
   comparison map from a two-factor amalgamated product into the ambient group.
2. `upperTriangularSubgroup` from Proposition `3-13-8` is the source-facing subgroup `T(K[x])`.
3. `constantLinearSubgroup` from Proposition `3-13-8` is the constant copy of `GL₂(K)` inside
   `GL₂(K[x])`.
4. `glPolynomial_amalgamatedProductComparison_bijective` from Proposition `3-13-8` already states
   the exact owner-level Bass-LinearRepresentations_Serre_1977 decomposition used here.

Primitive vs. derived:
- primitive source objects: the two actual subgroups inside `GL (Fin 2) (Polynomial K)`;
- derived owner-side API: their amalgamated product and the canonical comparison map into the
  ambient matrix group.
-/

/- Theorem 4-6-9 adds no new owner-level API beyond Proposition `3-13-8`. The upstream theorem
already states the source-faithful Bass-LinearRepresentations_Serre_1977 decomposition on the canonical subgroup objects, so
this file keeps only a direct recall instead of a parallel local `Monoid.PushoutI` presentation. -/
#check (glPolynomial_amalgamatedProductComparison_bijective K :
  Function.Bijective
    (Subgroup.amalgamatedProductComparison
      (constantLinearSubgroup K)
      (upperTriangularSubgroup : Subgroup (GL (Fin 2) (Polynomial K)))))

end
