import Mathlib
import Mathlib.Algebra.Group.Conj

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_11_1 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

open Monoid.CoprodI
open Monoid.PushoutI
open Monoid.PushoutI.NormalWord

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

section

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" =>
  Monoid.CoprodI.twoFactorAmalgamatingMaps A.subtype (B.subtype.comp e.toMonoidHom)
local notation "W" => Word Family
local notation "P" => Subgroup.amalgamatedProductAlong e

-- Primary domain: normal forms in free products with amalgamation.
-- Layer triage:
-- `source-facing`: a normal form of one fixed nontrivial element in the amalgamated product,
-- recorded as a reduced alternating word that evaluates to that element.
-- `core/canonical`: `Subgroup.amalgamatedProductAlong e` for the ambient amalgamated product,
-- `Subgroup.amalgamatedProductAlong.Reduced` for the source reduced-word predicate,
-- `Subgroup.amalgamatedProductAlong.ofWord e` for evaluation of a word in the amalgamated
-- product, and `Monoid.PushoutI.syllableLength` for the chosen-transversal owner length on the
-- ambient pushout.
-- `bridge/view`: the textbook phrase “normal form of `w`” is the conjunction that the source
-- reduced word represents the chosen element `w`; no second word owner is introduced.
--
-- Domain sampling:
-- 1. `Subgroup.amalgamatedProductAlong e` is the chapter-facing owner for a two-factor
--    amalgamated product.
-- 2. `Subgroup.amalgamatedProductAlong.Reduced e` already encodes exactly the source condition
--    that successive syllables come from different factors and that syllables from the
--    amalgamated subgroup are allowed only in the length-one case.
-- 3. `Subgroup.amalgamatedProductAlong.ofWord e` is the canonical evaluation map from a reduced
--    factor word to the represented element of the amalgamated product.
-- 4. `Monoid.PushoutI.syllableLength` is the chapter's canonical owner for the chosen-transversal
--    normal-form length, and the source length here differs from it only by the length-one
--    convention for nontrivial elements of the amalgamated subgroup.
--
-- Primitive vs. derived:
-- the primitive public inputs are the amalgamating identification `e`, the represented element
-- `w : P`, and the reduced word `u : W`. The textbook notion “`u` is a normal form of `w`” is the
-- derived conjunction that `u` is reduced and evaluates to `w`, together with the source
-- restriction `w ≠ 1`. The uniqueness-of-length statement is derived through the canonical owner
-- `syllableLength`, not by a second parallel length API.

/-- Definition 5-11-1: if `w ≠ 1` is an element of the free product of `G` and `H` with `A` and
`B` amalgamated along `e`, then a normal form of `w` is a reduced alternating word in the two
factors whose product is `w`. The length-one exception for letters lying in the amalgamated part
is already built into `Reduced e`. -/
def IsNormalForm (w : P) (u : W) : Prop :=
  w ≠ 1 ∧ Reduced e u ∧ ofWord e u = w

private theorem maps_injective : ∀ b, Function.Injective (Maps b)
  | false => by
      intro a₁ a₂ h
      exact Subtype.ext <| congrArg ULift.down h
  | true => by
      intro a₁ a₂ h
      exact e.injective <| Subtype.ext <| congrArg ULift.down h

/-- A source normal form has the canonical pushout syllable length, except that a nontrivial
element of the amalgamated subgroup is counted as one syllable in the source convention. -/
-- Proof sketch: choose a transversal for the amalgamated product and compare `u` with the
-- canonical `NormalWord` of `w`. Away from the amalgamated subgroup, `u` and the canonical normal
-- word have the same factor pattern, so they have the same syllable count. If `w` lies in the
-- amalgamated subgroup, the chosen normal word has syllable length `0`, while the source
-- convention records the unique nontrivial base syllable, producing `max 1 0 = 1`.
theorem length_eq_max_one_syllableLength
    (d : NormalWord.Transversal Maps)
    {w : P} {u : W}
    (hu : IsNormalForm e w u) :
    u.toList.length = max 1 (syllableLength d w) := sorry

/-- Any two normal forms of the same nontrivial element have the same syllable length. -/
theorem length_eq_of_isNormalForm
    {w : P} {u v : W}
    (hu : IsNormalForm e w u)
    (hv : IsNormalForm e w v) :
    u.toList.length = v.toList.length := by
  obtain ⟨d⟩ := transversal_nonempty Maps (maps_injective e)
  rw [length_eq_max_one_syllableLength e d hu, length_eq_max_one_syllableLength e d hv]

end

end Subgroup.amalgamatedProductAlong

/-! ### Definition_5_11_2 (from Items/Chap05) -/
universe u

set_option autoImplicit false

open Monoid.CoprodI Monoid.PushoutI
open Subgroup.amalgamatedProductAlong

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

/-!
Primary domain: cyclic reduction for normal-form words in a free product with amalgamation.

Layer triage:
- `source-facing`: a reduced two-factor word `w = y₁ ⋯ yₙ` in amalgam normal form, together with
  the textbook predicate “weakly cyclically reduced”, and the specialization of the already owned
  cyclic-reduction predicate to normal-form words.
- `core/canonical`: `Monoid.CoprodI.Word` is the owner for reduced alternating words in the two
  factors, specialized here through `Monoid.CoprodI.twoFactorFamily G H`.
- `bridge/view`: the first and last letters of a nonempty word are boundary data in one of the two
  factors, viewed in the ambient amalgamated product through `Monoid.PushoutI.of`; weak cyclic
  reduction compares their product with the canonical base subgroup `(base e).range`.

Domain sampling:
1. `Monoid.CoprodI.Word.IsCyclicallyReduced` from Theorem `4-2-12` is the chapter owner for
   cyclic reduction of a reduced alternating two-factor word.
2. `Monoid.CoprodI.NeWord.head` and `Monoid.CoprodI.NeWord.last` show that first and last letters
   are canonical boundary data of a nonempty reduced word.
3. `Subgroup.amalgamatedProductAlong.Reduced` is the chapter-facing owner for “normal form” in the
   two-factor amalgamated product.
4. `Monoid.PushoutI.of` and `Subgroup.amalgamatedProductAlong.base` are the canonical factor and
   base embeddings into the ambient amalgamated product.

Primitive vs. derived:
primitive public data: a source word `w : Word Family`, together with the owner-side reducedness
proof `Reduced e w` from Definition `4-2-9`, and its first and last boundary letters;
- derived API: the recalled cyclic-reduction owner predicate and the source weak cyclic-reduction
  predicate.
-/

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}
variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "P" => amalgamatedProductAlong e
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/- Definition 5-11-2 (1): for a normal-form word, “cyclically reduced” is the existing chapter
owner predicate `Monoid.CoprodI.Word.IsCyclicallyReduced`, specialized to the amalgamating maps
`ιA` and `ιB`. -/
#check (Word.IsCyclicallyReduced ιA ιB)

-- Proof sketch: this is the length-`0`/length-`1` branch built directly into the definition.
/-- Words of syllable length at most one are cyclically reduced. -/
theorem isCyclicallyReduced_of_length_le_one
    {w : Word Family} (hwred : Reduced e w) (hw : w.toList.length ≤ 1) :
    w.IsCyclicallyReduced ιA ιB := by
  exact ⟨hwred, fun _ _ _ ↦ hw⟩

/-- Definition 5-11-2 (2): a normal-form word is weakly cyclically reduced when a boundary pinch
through the amalgamated subgroup can occur only in syllable length at most one. Equivalently, for
words of length greater than one, if the last and first syllables lie in the same factor, then
their product does not lie in the amalgamated subgroup. -/
def IsWeaklyCyclicallyReduced
    (w : Word Family) : Prop :=
  Reduced e w ∧
    ∀ {b} {yLast yFirst : Family b},
      w.toList.getLast? = some ⟨b, yLast⟩ →
        w.toList.head? = some ⟨b, yFirst⟩ →
          ((Monoid.PushoutI.of b yLast : P) * Monoid.PushoutI.of b yFirst) ∈ (base e).range →
            w.toList.length ≤ 1

-- Proof sketch: this is again the length-`0`/length-`1` branch built directly into the
-- definition.
/-- Words of syllable length at most one are weakly cyclically reduced. -/
theorem isWeaklyCyclicallyReduced_of_length_le_one
    {w : Word Family} (hwred : Reduced e w) (hw : w.toList.length ≤ 1) :
    IsWeaklyCyclicallyReduced e w := by
  refine ⟨hwred, ?_⟩
  intro _ _ _ _ _ _
  exact hw

end

end Subgroup.amalgamatedProductAlong

/-! ### Definition_5_11_3 (from Items/Chap05) -/
universe u

set_option autoImplicit false

open Monoid.CoprodI

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

section

variable {G : Type u} {H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} {e : A ≃* B}

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family
local notation "P" => Subgroup.amalgamatedProductAlong e

/-!
Primary domain: symmetrized relator families for small-cancellation over free products with
amalgamation.

Layer triage:
- `source-facing`: a relator set `R : Set P` in the amalgamated product and the corresponding
  family of weakly cyclically reduced word representatives of conjugates of relators and their
  inverses.
- `core/canonical`: `Subgroup.amalgamatedProductAlong e` is the ambient owner,
  `IsWeaklyCyclicallyReduced e` is the Section `11` owner predicate on words,
  `ofWord e` is the canonical bridge from words to the amalgamated product, and `IsConj` is the
  owner relation for conjugacy.
- `bridge/view`: the source relator family is read through weakly cyclically reduced word
  representatives rather than by introducing a second packaged conjugacy-class wrapper.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong e` from Definition `4-2-9` is the chapter owner for the
   two-factor amalgamated product.
2. `Subgroup.amalgamatedProductAlong.IsWeaklyCyclicallyReduced` from Definition `5-11-2` is the
   source-facing reduction predicate on normal-form words in that owner.
3. `IsConj` from `Mathlib.Algebra.Group.Conj` is the canonical owner for conjugacy, so the
   inverse-and-conjugacy closure should be expressed directly with it.
4. The Section `10` free-product owner `symmetrizedRelatorFamily` already fixes the chapter shape:
   separate weak cyclic reduction from the conjugacy data and expose the relator family as a set
   of words.

Primitive vs. derived:
- primitive public data: the ambient owner `P`, the relator set `R : Set P`, and a reduced word
  `q : W`;
- primitive source clauses: `q` is weakly cyclically reduced and represents a conjugate of some
  `r ∈ R` or of `r⁻¹`;
- derived API: projection lemmas recovering the weak cyclic reduction and relator-conjugacy data
  from membership in the symmetrized family.
-/

/-- Definition 5-11-3: the symmetrized relator family generated by `R` in the amalgamated
product `P = ⟨G * H, A = B⟩` consists of the weakly cyclically reduced words whose value in `P`
is conjugate to some relator from `R` or to its inverse. -/
def symmetrizedRelatorFamily (R : Set P) : Set W :=
  { q | IsWeaklyCyclicallyReduced e q ∧
      ∃ r ∈ R, IsConj (ofWord e q) r ∨ IsConj (ofWord e q) r⁻¹ }

/-- A word in the symmetrized relator family is weakly cyclically reduced. -/
theorem isWeaklyCyclicallyReduced_of_mem_symmetrizedRelatorFamily
    {R : Set P} {q : W} (hq : q ∈ symmetrizedRelatorFamily R) :
    IsWeaklyCyclicallyReduced e q :=
  hq.1

/-- A word in the symmetrized relator family represents a conjugate of some relator from `R` or
of its inverse. -/
theorem exists_isConj_or_inv_isConj_of_mem_symmetrizedRelatorFamily
    {R : Set P} {q : W} (hq : q ∈ symmetrizedRelatorFamily R) :
    ∃ r ∈ R, IsConj (ofWord e q) r ∨ IsConj (ofWord e q) r⁻¹ :=
  hq.2

end

end Subgroup.amalgamatedProductAlong

/-! ### Definition_5_11_8 (from Items/Chap05) -/
universe u

set_option autoImplicit false

section

variable {H : Type u} [Group H]

/-!
Primary domain: subgroup combinatorics in small cancellation theory over amalgamated products and
HNN extensions.

Layer triage:
- `source-facing`: a subgroup `A ≤ H` together with two elements `x₁, x₂ : H` forming the
  textbook blocking pair.
- `core/canonical`: `Subgroup H` is the owner abstraction for `A`, and the condition is a
  `Prop`-valued structure on the displayed elements rather than a second packaged owner.
- `bridge/view`: the unordered pair `{x₁, x₂}` is rendered by the two-point set
  `({x₁, x₂} : Set H)`, and the signs `±1` are rendered by the canonical sign type `ℤˣ`,
  coerced to integer exponents in powers.

Domain sampling:
1. `Subgroup H` is mathlib's canonical owner for subgroup-valued data in a group.
2. `({x₁, x₂} : Set H)` is the canonical set-theoretic rendering of the unordered pair
   `{x₁, x₂}`.
3. `ℤˣ` is the project's canonical carrier for the source signs `±1`, and the group-theoretic
   powers use the coerced exponents `y ^ (ε : ℤ)`.
4. Existing chapter predicates such as `Subgroup.IsBenign` are stated directly on the subgroup
   owner rather than through a parallel wrapper structure on the ambient group.

Primitive vs. derived:
- primitive public data: the subgroup `A` and the elements `x₁`, `x₂`;
- primitive source conditions: `x₁ ≠ x₂`, `x₁ ∉ A`, `x₂ ∉ A`, and the blocking condition for
  every nontrivial `a ∈ A`;
- derived API: consequences such as any element of `{x₁, x₂}` lying outside `A`.
-/

namespace Subgroup

/-- Definition 5-11-8: `{x₁, x₂}` is a blocking pair for the subgroup `A ≤ H` if `x₁ ≠ x₂`,
neither `x₁` nor `x₂` belongs to `A`, and for every nontrivial `a ∈ A`, every choice of
`y, z ∈ {x₁, x₂}`, and every signs `ε, δ : ℤˣ`, the element
`y ^ (ε : ℤ) * a * z ^ (δ : ℤ)` does not belong to `A`. -/
structure IsBlockingPair (A : Subgroup H) (x₁ x₂ : H) : Prop where
  /-- The two displayed elements of a blocking pair are distinct. -/
  distinct : x₁ ≠ x₂
  /-- Every element of the displayed pair lies outside the subgroup. -/
  not_mem {x : H} (hx : x ∈ ({x₁, x₂} : Set H)) : x ∉ A
  /-- No signed sandwich `y^ε a z^δ` with nontrivial `a ∈ A`, `y, z ∈ {x₁, x₂}`, and
  signs `ε, δ : ℤˣ` returns to `A`. -/
  blocked {a y z : H} (ha : a ∈ A) (ha_ne_one : a ≠ 1)
      (hy : y ∈ ({x₁, x₂} : Set H)) (hz : z ∈ ({x₁, x₂} : Set H))
      (ε δ : ℤˣ) : y ^ (ε : ℤ) * a * z ^ (δ : ℤ) ∉ A

/-- Any element of the pair underlying a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.not_mem_of_mem_pair
    {A : Subgroup H} {x₁ x₂ x : H} (h : A.IsBlockingPair x₁ x₂)
    (hx : x ∈ ({x₁, x₂} : Set H)) :
    x ∉ A :=
  h.not_mem hx

/-- The left entry of a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.left_not_mem
    {A : Subgroup H} {x₁ x₂ : H} (h : A.IsBlockingPair x₁ x₂) :
    x₁ ∉ A :=
  h.not_mem_of_mem_pair (by simp)

/-- The right entry of a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.right_not_mem
    {A : Subgroup H} {x₁ x₂ : H} (h : A.IsBlockingPair x₁ x₂) :
    x₂ ∉ A :=
  h.not_mem_of_mem_pair (by simp)

end Subgroup

end

/-! ### Theorem_5_11_9 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

section

variable {H : Type u} {K : Type v} [Group H] [Group K]

open Subgroup

/-!
Primary domain: small-cancellation theory over free products with amalgamation.

Layer triage:
- `source-facing`: proper subgroups `A ≤ H` and `B ≤ K`, an identification `e : A ≃* B`, and the
  existence of a blocking pair for `A` inside `H`.
- `core/canonical`: `Subgroup H` and `Subgroup K` are the owner abstractions for the amalgamated
  subgroups, `Subgroup.IsBlockingPair` is the source-facing predicate from Definition `5-11-8`,
  `Subgroup.amalgamatedProductAlong e` is the canonical owner for the amalgamated product, and
  `IsSQUniversal` is the project owner predicate for the conclusion.
- `bridge/view`: the textbook notation `P = ⟨H ∗ K, A = B⟩` is rendered directly by the canonical
  owner `Subgroup.amalgamatedProductAlong e`.

Domain sampling:
1. `Subgroup.IsBlockingPair` from Definition `5-11-8` already formalizes the source blocking-pair
   condition on the subgroup owner `A`.
2. `Subgroup.amalgamatedProductAlong e` from Definition `4-2-9` is the chapter owner for the free
   product of `H` and `K` amalgamating `A` with `B`.
3. `IsSQUniversal` from Proposition `2-5-31` is the existing owner predicate for `SQ`-universality.

Primitive vs. derived:
the primitive public data are the ambient groups, the subgroup pair `A ≤ H`, `B ≤ K`, the
identification `e : A ≃* B`, the properness of `B`, and the existence of a blocking pair for `A`.
Properness of `A` is derived from the blocking-pair hypothesis, so it is not repeated as a
separate public assumption.
-/

-- Proof sketch: apply the section-11 small-cancellation theorem for amalgamated products with a
-- blocking pair on one side. The blocking-pair hypothesis supplies the combinatorial separation
-- needed to build the required small-cancellation quotient, and the properness of `B` excludes
-- the degenerate amalgamation case. The conclusion is then stated on the canonical owner
-- `Subgroup.amalgamatedProductAlong e`.
/-- Theorem 5-11-9: if `P = ⟨H ∗ K, A = B⟩` is a free product with amalgamation, `B` is a proper
subgroup of `K`, and there is a blocking pair for `A` in `H`, then `P` is `SQ`-universal. -/
theorem isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair
    (A : Subgroup H) (B : Subgroup K) (e : A ≃* B) (hB_proper : B < ⊤)
    (hblocking : ∃ x₁ x₂, A.IsBlockingPair x₁ x₂) :
    IsSQUniversal (amalgamatedProductAlong e) := sorry

end

/-! ### Corollary_5_11_10 (from Items/Chap05) -/
universe u v w

set_option autoImplicit false

section

variable {H : Type u} {K : Type v} [Group H] [Group K] [IsFreeGroup H]

open Subgroup

/-!
Primary domain: `SQ`-universality of free products with amalgamation over free groups.

Layer triage:
- `source-facing`: a free group `H`, a finitely generated subgroup `A ≤ H` of infinite index, a
  proper subgroup `A' ≤ K` isomorphic to `A`, and the resulting free product with amalgamation
  `P = (H * K; A = A')`.
- `core/canonical`: `Subgroup.IsBlockingPair` from Definition `5-11-8` and
  `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair` from Theorem `5-11-9` are the
  chapter owner predicate and owner theorem for the Section `11` argument.
- `bridge/view`: this corollary turns the source free-group hypotheses `A.FG` and the canonical
  infinite-index condition `Infinite (H ⧸ A)` into the blocking-pair hypothesis needed by Theorem
  `5-11-9`; `Subgroup.index_eq_zero_iff_infinite` is only the internal mathlib bridge to the
  older index-sentinel encoding.

Domain sampling:
1. `Subgroup.IsBlockingPair` from Definition `5-11-8` is the source-facing owner predicate for
   the combinatorial obstruction used in Section `11`.
2. `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair` from Theorem `5-11-9` is the
   chapter owner theorem for the `SQ`-universality conclusion.
3. `amalgamatedProductAlong e` from Definition `4-2-9` is the canonical owner for the
   resulting free product with amalgamation.
4. `Subgroup.index`, `Subgroup.FiniteIndex`, and
   `Subgroup.index_eq_zero_iff_infinite` in `Mathlib/GroupTheory/Index` are the canonical owner
   API and bridge for subgroup index; the quotient-side `Infinite (H ⧸ A)` hypothesis is the
   mathematically faithful public surface here.
5. `IsFreeGroup H` and `A.FG` are the canonical encodings of the remaining source free-group
   hypotheses.

Primitive vs. derived:
the primitive data are exactly the two ambient groups, the subgroup `A ≤ H`, the proper copy
`A' ≤ K`, and the chosen isomorphism `e : A ≃* A'`. The blocking-pair witness is derived from the
free-group hypotheses and is therefore produced internally in the corollary proof rather than
exposed as a second local declaration with overlapping mathematical content. The index-sentinel
equation `A.index = 0` is likewise treated as derived bridge API, not primitive public data.
-/

-- Proof sketch: derive a blocking pair for `A` from the free-group hypotheses together with the
-- canonical quotient-infinitude input `Infinite (H ⧸ A)`, then apply the owner theorem
-- `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair`.
/-- Corollary 5-11-10: if `H` is free, `A ≤ H` is finitely generated of infinite index, and `K`
contains a proper subgroup `A'` isomorphic to `A`, then the amalgamated free product
`(H * K; A = A')` is `SQ`-universal. -/
theorem isSQUniversal_amalgamatedProductAlong_of_freeGroup_subgroup_fg_of_infiniteIndex
    (A : Subgroup H) (hA_fg : A.FG) (hA_quotient : Infinite (H ⧸ A))
    (A' : Subgroup K) (hA'_proper : A' < ⊤) (e : A ≃* A') :
    IsSQUniversal (amalgamatedProductAlong e) := by
  have hblocking : ∃ x₁ x₂, A.IsBlockingPair x₁ x₂ := by
    -- A finitely generated infinite-index subgroup of a free group admits a blocking pair in the
    -- sense of Definition `5-11-8`.
    -- The quotient-side infinitude needed for the classical free-group argument is supplied
    -- directly by `hA_quotient`.
    sorry
  intro L _ _
  exact isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair A A' e hA'_proper hblocking

end

/-! ### Definition_5_11_11 (from Items/Chap05) -/
universe u

set_option autoImplicit false

open Monoid.CoprodI

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

section

variable {G : Type u} {H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} {e : A ≃* B}

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family
local notation "P" => Subgroup.amalgamatedProductAlong e

/-!
Primary domain: small-cancellation conditions for symmetrized relator systems in a free product
with amalgamation.

Layer triage:
- `source-facing`: a relator set `R : Set P`, the corresponding weakly cyclically reduced
  symmetrized relator family, and the Section `11` piece-prefix inequalities on those relator
  words.
- `core/canonical`: `Subgroup.amalgamatedProductAlong.symmetrizedRelatorFamily` is the owner for
  the relevant relator system, and `Monoid.CoprodI.Word` is the owner for the normal-form words on
  which prefixes and lengths are read.
- `bridge/view`: the textbook factorization `q = bc` is rendered by the canonical list-prefix
  relation `b <+: q.toList`.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong.symmetrizedRelatorFamily` from Definition `5-11-3` is the
   Section `11` owner for the weakly cyclically reduced relator words associated to `R`.
2. `Subgroup.amalgamatedProductAlong.IsWeaklyCyclicallyReduced` from Definition `5-11-2` is the
   reduction predicate built into that owner.
3. `FreeGroupBasis.is_piece` and `FreeGroupBasis.condition_c_prime` from Definition `5-2-1` fix
   the chapter pattern: the piece notion is derived from the symmetrized relator family, and
   `C'(λ)` is stated directly on that owner.
4. `Monoid.CoprodI.condition_c_prime` from Theorem `5-10-1` uses the same owner discipline for
   free products, reading small-cancellation directly on weakly cyclically reduced relator words.

Primitive vs. derived:
- primitive public data: the ambient owner `P`, the relator set `R : Set P`, and the parameter
  `λ`;
- primitive source clauses: every nonempty common initial segment of two distinct symmetrized
  relators has length `< λ` times the length of each relator in which it occurs, and every
  symmetrized relator has length `> 1 / λ`;
- derived API: the piece predicate and the projection lemmas for the two `C'(λ)` clauses.
-/

/-- A word `piece` is a Section `11` piece for `R` when it is a nonempty common initial segment
of two distinct symmetrized relator words generated by `R`. -/
def is_piece (R : Set P) (piece : List (Σ b, Family b)) : Prop :=
  piece ≠ [] ∧
    ∃ q₁ : W, q₁ ∈ symmetrizedRelatorFamily R ∧
      ∃ q₂ : W, q₂ ∈ symmetrizedRelatorFamily R ∧
        q₁ ≠ q₂ ∧ piece <+: q₁.toList ∧ piece <+: q₂.toList

/-- Definition 5-11-11: the relator set `R` satisfies the Section `11` small-cancellation
condition `C'(λ)` when every piece prefix of a symmetrized relator from `R` has length strictly
less than `λ` times the relator length, and every symmetrized relator has length strictly greater
than `1 / λ`. -/
def condition_c_prime (R : Set P) (lambda : ℝ) : Prop :=
  (∀ {q : W} (_ : q ∈ symmetrizedRelatorFamily R)
      {piece : List (Σ b, Family b)} (_ : piece <+: q.toList) (_ : is_piece R piece),
        (piece.length : ℝ) < lambda * q.toList.length) ∧
    ∀ {q : W} (_ : q ∈ symmetrizedRelatorFamily R), (1 / lambda : ℝ) < q.toList.length

notation:55 "C'(" lambda ")[" R "]" => condition_c_prime R lambda

/-- Under `C'(λ)`, every piece prefix occurring in a symmetrized relator has length strictly less
than `λ` times the relator length. -/
theorem piece_length_lt_of_condition_c_prime
    {R : Set P} {lambda : ℝ} (hR : C'(lambda)[R]) {q : W}
    (hq : q ∈ symmetrizedRelatorFamily R)
    {piece : List (Σ b, Family b)}
    (hprefix : piece <+: q.toList) (hpiece : is_piece R piece) :
    (piece.length : ℝ) < lambda * q.toList.length :=
  hR.1 hq hprefix hpiece

/-- Under `C'(λ)`, every symmetrized relator has length strictly greater than `1 / λ`. -/
theorem relator_length_gt_inv_of_condition_c_prime
    {R : Set P} {lambda : ℝ} (hR : C'(lambda)[R]) {q : W}
    (hq : q ∈ symmetrizedRelatorFamily R) :
    (1 / lambda : ℝ) < q.toList.length :=
  hR.2 hq

/-- The empty relator set satisfies `C'(λ)` vacuously. -/
theorem empty_condition_c_prime (lambda : ℝ) :
    C'(lambda)[(∅ : Set P)] := by
  refine ⟨?_, ?_⟩
  · intro q hq piece hprefix hpiece
    rcases hq.2 with ⟨r, hr, _⟩
    cases hr
  · intro q hq
    rcases hq.2 with ⟨r, hr, _⟩
    cases hr

end

end Subgroup.amalgamatedProductAlong

/-! ### Lemma_5_11_15 (from Items/Chap05) -/
universe u

noncomputable section

section

/-!
Primary domain: one-relator groups and the Nielsen-transform step that prepares a relator for an
HNN-extension argument.

Layer triage:
- `source-facing`: a one-relator presentation `⟨X ; r⟩` with at least two generators, together
  with the existence of an equivalent one-relator presentation whose relator has exponent sum zero
  in some distinguished generator.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `MulAut (FreeGroup X)` for Nielsen-transform automorphisms of the ambient free group,
  `FreeGroup.lift` for the exponent-sum homomorphism, and `Cardinal.mk X` for the lower bound on
  the size of the generator type.
- `bridge/view`: the new presentation is obtained by applying a free-group automorphism `α` to the
  relator, and `QuotientGroup.congr` together with `Subgroup.map_normalClosure` supplies the
  canonical quotient transport from `PresentedGroup (Set.singleton r)` to
  `PresentedGroup (Set.singleton (α r))`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the project owner for a one-relator group with defining
   relator `r`.
2. `MulAut (FreeGroup X)` is the canonical owner for Nielsen moves on the ambient free group.
3. `QuotientGroup.congr` together with `Subgroup.map_normalClosure` is the canonical transport
   from a free-group automorphism to the induced equivalence of one-relator quotients.
4. `FreeGroup.lift` is the canonical way to define the exponent-sum homomorphism from the free
   group by sending one generator to `1 ∈ ℤ` and all others to `0`.
5. `Cardinal.mk X` is the project's universe-stable expression of “at least two generators”.

Primitive vs. derived:
the primitive source data are the generator type `X`, the relator `r`, and the cardinality
assumption `2 ≤ Cardinal.mk X`; the Nielsen automorphism `α`, the rewritten relator `α r`, the
distinguished generator `t` are derived existential data, while the induced presentation
equivalence is canonically supplied by `QuotientGroup.congr` and `Subgroup.map_normalClosure`, so
no wrapper structure is introduced.
-/

variable {X : Type u}

/-- The exponent sum of the generator `x` in the free-group word `r`. -/
def generatorExponentSum (x : X) (r : FreeGroup X) : ℤ :=
  let _ : DecidableEq X := Classical.decEq X
  (FreeGroup.lift (fun y ↦ Multiplicative.ofAdd (if y = x then (1 : ℤ) else 0)) r).toAdd

/-- The exponent sum of a generator in its own free-group letter is `1`. -/
@[simp] theorem generatorExponentSum_of_generator (x : X) :
    generatorExponentSum x (FreeGroup.of x) = 1 := by
  classical
  simp [generatorExponentSum]

/-- The exponent sum of `x` in a different generator letter is `0`. -/
@[simp] theorem generatorExponentSum_of_generator_ne (x y : X) (hxy : y ≠ x) :
    generatorExponentSum x (FreeGroup.of y) = 0 := by
  classical
  simp [generatorExponentSum, hxy]

-- Proof sketch: if some generator already has exponent sum `0` in `r`, keep that generator. If
-- not, choose two distinct generators and perform Nielsen moves on the free basis, replacing one
-- generator by a product with a suitable power of the other. The classical induction on the sum
-- of the absolute values of the two exponent sums decreases under this move, yielding an
-- automorphic relator whose exponent sum in one distinguished generator is `0`; the corresponding
-- one-relator quotient equivalence is the canonical `QuotientGroup.congr` transport.
/-- Auxiliary Nielsen-transform form of Lemma 5-11-15: after applying a suitable automorphism of
the ambient free group, the relator has exponent sum `0` in some distinguished generator. -/
lemma exists_automorphism_with_zero_generatorExponentSum
    (r : FreeGroup X) (hX : 2 ≤ Cardinal.mk X) :
    ∃ (α : MulAut (FreeGroup X)) (t : X), generatorExponentSum t (α r) = 0 := sorry

/-- Lemma 5-11-15: a one-relator presentation with at least two generators is equivalent to one on
the same generator type whose relator has exponent sum `0` in some distinguished generator. -/
lemma exists_equivalent_presentation_with_zero_generatorExponentSum
    (r : FreeGroup X) (hX : 2 ≤ Cardinal.mk X) :
    ∃ (r' : FreeGroup X) (_ : PresentedGroup ({r} : Set (FreeGroup X)) ≃*
      PresentedGroup ({r'} : Set (FreeGroup X))) (t : X), generatorExponentSum t r' = 0 := by
  rcases exists_automorphism_with_zero_generatorExponentSum r hX with ⟨α, t, ht⟩
  refine ⟨α r, QuotientGroup.congr
    (Subgroup.normalClosure ({r} : Set (FreeGroup X)))
    (Subgroup.normalClosure ({α r} : Set (FreeGroup X)))
    α ?_, t, ht⟩
  simpa using
    (Subgroup.map_normalClosure ({r} : Set (FreeGroup X))
      (α : FreeGroup X →* FreeGroup X) α.surjective)

end

/-! ### Theorem_5_11_16 (from Items/Chap05) -/
universe u

section

variable {X : Type u}

/-!
Primary domain: one-relator groups and `SQ`-universality.

Layer triage:
- `source-facing`: a one-relator group on at least three generators, written in the text as
  `⟨t, b, c, ... ; r⟩`.
- `core/canonical`: `PresentedGroup (Set.singleton r)` is the project's owner for one-relator
  groups, `Cardinal.mk X` records the lower bound on the number of generators, and
  `IsSQUniversal` is the owner predicate for `SQ`-universality.
- `bridge/view`: the Chapter V proof route rewrites the relator using Lemma `5-11-15` and then
  applies an HNN-extension criterion, but those intermediate choices do not belong in the public
  statement. The resulting theorem is exactly the canonical one-relator statement already recorded
  in Proposition `2-5-31`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the established owner for one-relator groups in this
   project.
2. `IsSQUniversal` from Proposition `2-5-31` is the canonical owner predicate for the conclusion.
3. `isSQUniversal_of_three_generator_one_relator_group` already states the one-relator
   `SQ`-universality theorem with the exact owner-level interface needed here.

Primitive vs. derived:
the primitive public data are only the relator `r` and the cardinality hypothesis
`3 ≤ Cardinal.mk X`. The distinguished generator `t` from the proof, the zero exponent-sum
rewriting from Lemma `5-11-15`, and the HNN-extension decomposition are proof-level bridges, not
part of the statement API.
-/

/- Theorem 5-11-16: a group with a one-relator presentation on at least three generators is
`SQ`-universal.

This item adds no new public declaration beyond the canonical theorem
`isSQUniversal_of_three_generator_one_relator_group`; the Chapter V HNN-extension argument is a
proof route for that already existing owner-level statement. -/
#check (isSQUniversal_of_three_generator_one_relator_group :
  (r : FreeGroup X) → (hX : 3 ≤ Cardinal.mk X) →
    IsSQUniversal (PresentedGroup (Set.singleton r)))

end
