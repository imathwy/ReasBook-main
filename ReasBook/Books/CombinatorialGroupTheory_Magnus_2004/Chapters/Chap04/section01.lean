import Mathlib
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1_1 (from Items/Chap04) -/
universe u v

open scoped Monoid.Coprod

set_option autoImplicit false

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

-- Layer triage:
-- `source-facing`: the textbook definition of the free product of two groups `A` and `B`,
-- presented by adjoining the generators and relators of two disjoint presentations.
-- `core/canonical`: `Monoid.Coprod`, with scoped notation `A ∗ B`, is mathlib's owner
-- abstraction for the coproduct of two groups.
-- `bridge/view`: no extra bridge is needed here, because the textbook item is only recalling the
-- basic owner construction itself rather than asserting a new universal property or comparison
-- theorem.
-- Domain sampling:
-- 1. `Monoid.Coprod` in `Mathlib/GroupTheory/Coprod/Basic` is the canonical free-product
--    construction for monoids and groups.
-- 2. The scoped notation `A ∗ B` is the canonical source-facing notation for that owner
--    construction.
-- 3. `Proposition_1_6_4` and `Proposition_3_12_3` already use `Monoid.Coprod` and the notation
--    `G₁ ∗ G₂` as the project's free-product API for groups.
-- 4. `Definition_4_1_2` immediately derives the factor subgroups from the canonical embeddings
--    `Monoid.Coprod.inl` and `Monoid.Coprod.inr`, so this owner file should expose only the
--    ambient free-product object itself.
-- Primitive vs. derived:
-- the primitive mathematical content of this item is just the ambient free-product object; the
-- universal property maps and later structural lemmas are derived API on top of `Monoid.Coprod`.

/- Definition 4-1-1: for groups `A` and `B` with disjoint chosen presentations, the free product
`A * B` is the group obtained by taking the combined generators and relators of those two
presentations.

This item is a direct recall of mathlib's canonical free-product owner expression for groups, so
the file records the type expression `A ∗ B` itself rather than introducing a redundant alias. -/
#check (A ∗ B)

end

/-! ### Definition_4_1_2 (from Items/Chap04) -/
universe u v

open Monoid.Coprod
open scoped Monoid.Coprod

set_option autoImplicit false

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

/-!
Primary domain: free products of groups and their canonical factor subgroups.

Layer triage:
- `source-facing`: the two factor subgroups of the free product `A ∗ B`.
- `core/canonical`: `Monoid.Coprod.inl`, `Monoid.Coprod.inr`, and `MonoidHom.range`.
- `bridge/view`: the textbook factors are expressed as the ranges of the canonical embeddings.

Domain sampling:
1. `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner abstraction for the free product.
2. `Monoid.Coprod.inl` and `Monoid.Coprod.inr` are the canonical embeddings of the two factors.
3. `MonoidHom.range` is the canonical owner for the subgroup image of a homomorphism.

Primitive vs. derived:
- primitive public data: the factor groups `A`, `B`, the free product `A ∗ B`, and the canonical
  embeddings of the factors;
- derived API: the left and right factor subgroups inside `A ∗ B`, obtained as the ranges of those
  embeddings.
-/

/- Definition 4-1-2: inside the free product `A ∗ B`, the two textbook factor subgroups are the
ranges of the canonical embeddings `inl : A →* A ∗ B` and `inr : B →* A ∗ B`.

This item is a direct bridge/view recall of mathlib's canonical range expressions, so the file
records those expressions directly instead of introducing parallel local aliases. -/
#check (((inl : A →* A ∗ B).range) : Subgroup (A ∗ B))
#check (((inr : B →* A ∗ B).range) : Subgroup (A ∗ B))

end

/-! ### Lemma_4_1_3 (from Items/Chap04) -/
open scoped Monoid.Coprod
open Monoid.Coprod

universe u v

set_option autoImplicit false

/-!
Primary domain: free products of groups and their canonical factor subgroups.

Layer triage:
- `source-facing`: the free product `A ∗ B`, its two canonical factor subgroups, and the textbook
  claims that the free product depends only on the factor groups and contains isomorphic copies of
  the factors generating the whole group with trivial intersection.
- `core/canonical`: `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner for the free
  product, `MulEquiv.coprodCongr` is the canonical invariance theorem under factor isomorphisms,
  and the canonical injections `inl`, `inr` together with `Subgroup.ofLeftInverse` and
  `range_inl_sup_range_inr` give the range-level factor API.
- `bridge/view`: the subgroup-valued view of the two factors inside `A ∗ B` is obtained by passing
  from the canonical injections to their ranges.

Domain sampling:
1. `Monoid.Coprod` is the canonical free-product owner abstraction in mathlib.
2. `MulEquiv.coprodCongr` is the canonical statement that free products are preserved by
   equivalences of factors.
3. `Subgroup.ofLeftInverse` is the canonical equivalence from a group to the range of a
   homomorphism equipped with a specified left inverse.
4. `Monoid.Coprod.range_inl_sup_range_inr` is the canonical generation statement for the two
   factor ranges inside a free product.

Primitive vs. derived:
- primitive public data: the factor groups `A`, `B`, the free product `A ∗ B`, and the canonical
  injections of the two factors;
- derived API: the factor ranges `(inl : A →* A ∗ B).range` and `(inr : B →* A ∗ B)`, the induced
  equivalences from `A` and `B` onto those ranges via the canonical projections `fst` and `snd`,
  and the facts that these subgroups generate the free product and intersect trivially.
-/

/- Lemma 4-1-3: the free product is uniquely determined by the factor groups, via the canonical
equivalence `MulEquiv.coprodCongr` induced from equivalences of the two factors. -/
#check MulEquiv.coprodCongr

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

/- Lemma 4-1-3 (1): the canonical left factor subgroup of `A ∗ B` is isomorphic to `A`. -/
#check (Subgroup.ofLeftInverse
  (show Function.LeftInverse (fst : A ∗ B →* A) (inl : A →* A ∗ B) from fst_apply_inl) :
    A ≃* (inl : A →* A ∗ B).range)

/- Lemma 4-1-3 (2): the canonical right factor subgroup of `A ∗ B` is isomorphic to `B`. -/
#check (Subgroup.ofLeftInverse
  (show Function.LeftInverse (snd : A ∗ B →* B) (inr : B →* A ∗ B) from snd_apply_inr) :
    B ≃* (inr : B →* A ∗ B).range)

/-- Lemma 4-1-3 (3): the canonical left and right factor subgroups generate the free product
`A ∗ B`. -/
theorem leftFreeProductFactor_sup_rightFreeProductFactor :
    (inl : A →* A ∗ B).range ⊔ (inr : B →* A ∗ B).range = ⊤ := by
  exact
    (range_inl_sup_range_inr : (inl : A →* A ∗ B).range ⊔ (inr : B →* A ∗ B).range = ⊤)

/-- Lemma 4-1-3 (4): the canonical left and right factor subgroups of `A ∗ B` intersect
trivially. -/
theorem leftFreeProductFactor_disjoint_rightFreeProductFactor :
    Disjoint ((inl : A →* A ∗ B).range) ((inr : B →* A ∗ B).range) := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have ha : a = 1 := by
    simpa using congrArg fst hb.symm
  simp [ha]

end

/-! ### Definition_4_1_4 (from Items/Chap04) -/
universe u v

set_option autoImplicit false

open Monoid.CoprodI

namespace Monoid.CoprodI

/- The canonical `Bool`-indexed two-factor bridge for reduced words. This mirrors the
`fun b ↦ cond b M N` family behind `Monoid.Coprod`, with the necessary `ULift`s to place the two
factors in a common universe and with `false` indexing the left factor. This bridge is reused
later for free products with amalgamation, so it belongs at the chapter's first reduced-word item
rather than as a repeated local helper. Since `Word` is a monoid-level notion, the bridge also
lives at the monoid level and later group-specific files specialize it. -/
abbrev twoFactorFamily (A : Type u) (B : Type v) : Bool → Type (max u v) :=
  fun b ↦ cond b (ULift.{max u v} B) (ULift.{max u v} A)

instance (priority := 50) twoFactorFamilyMonoid
    (A : Type u) (B : Type v) [Monoid A] [Monoid B] (b : Bool) :
    Monoid (twoFactorFamily A B b) := by
  cases b <;> dsimp [twoFactorFamily] <;> infer_instance

instance twoFactorFamilyGroup
    (A : Type u) (B : Type v) [Group A] [Group B] (b : Bool) :
    Group (twoFactorFamily A B b) := by
  cases b with
  | false =>
      dsimp [twoFactorFamily]
      let inst : Group (ULift.{max u v} A) := inferInstance
      exact { inst with toMonoid := twoFactorFamilyMonoid A B false }
  | true =>
      dsimp [twoFactorFamily]
      let inst : Group (ULift.{max u v} B) := inferInstance
      exact { inst with toMonoid := twoFactorFamilyMonoid A B true }

end Monoid.CoprodI

section

variable (A : Type u) (B : Type v) [Monoid A] [Monoid B]

-- Primary domain: reduced words for free products of monoids, later specialized to groups.
-- Layer triage:
-- `source-facing`: the textbook notion of a reduced normal form in the free product of two
-- factors `A` and `B`.
-- `core/canonical`: `Monoid.Coprod` is mathlib's two-factor free-product owner, and `Word` in
-- `Monoid.CoprodI` is mathlib's owner abstraction for reduced words in an indexed free product.
-- `bridge/view`: `Monoid.CoprodI.twoFactorFamily A B` is the chapter's shared `Bool`/`ULift`
-- specialization used to view the two-factor case through the indexed owner.
-- No separate public two-factor reduced-word owner is introduced.
-- Domain sampling:
-- 1. `Monoid.Coprod` is mathlib's canonical two-factor free product, implemented via a
--    `Bool`-indexed family of factor types behind the scenes.
-- 2. `Monoid.CoprodI.twoFactorFamily` is the chapter's minimal same-kind bridge from two factors
--    to the
--    indexed free-product word owner.
-- 3. `Word` is the canonical reduced-word owner for indexed free products.
-- 4. `Word.empty`, `Word.prod`, and `Word.equiv` are the canonical empty-word, evaluation, and
--    normal-form API.
-- Primitive vs. derived:
-- the primitive data remain the reduced list of nontrivial letters with adjacent-factor
-- inequality; the empty word, evaluation map, and normal-form equivalence are derived API from the
-- owner abstraction. The shared two-factor specialization is exposed only as the minimal bridge
-- needed to reuse that owner abstraction in later chapter files.

/- Definition 4-1-4: a reduced sequence (normal form) for the free product of `A` and `B` is
mathlib's canonical reduced-word object specialized to the two-factor free product.

This item keeps `Monoid.CoprodI.Word` as the public owner of reduced words. The only extra chapter
API introduced here is the reusable bridge `Monoid.CoprodI.twoFactorFamily`, which specializes the
indexed owner to the two-factor case without creating a second reduced-word wrapper. -/
#check (Word (twoFactorFamily A B))

end

/-! ### Remark_4_1_11 (from Items/Chap04) -/
universe u v

open Monoid.Coprod
open scoped Monoid.Coprod commutatorElement

set_option autoImplicit false

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

-- Layer triage:
-- `source-facing`: the explicit set of commutators `⁅a, b⁆` with `a ∈ A`, `b ∈ B`, and
-- `a ≠ 1`, `b ≠ 1`, viewed inside the free product `A ∗ B`.
-- `core/canonical`: `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner for the free
-- product, the two canonical factor subgroups inside `A ∗ B` are `(inl : A →* A ∗ B).range` and
-- `(inr : B →* A ∗ B).range`, and `⁅-, -⁆` is the canonical owner for the subgroup commutator of
-- those factor subgroups.
-- `bridge/view`: the displayed commutator set is the source-facing subset of the canonical
-- subgroup commutator whose closure recovers
-- `⁅(inl : A →* A ∗ B).range, (inr : B →* A ∗ B).range⁆`.
-- Domain sampling:
-- 1. `Monoid.Coprod` and its maps `inl`, `inr` are mathlib's owner API for free products.
-- 2. The canonical factor subgroups inside `A ∗ B` are the ranges of `inl` and `inr`.
-- 3. `⁅H, K⁆` is mathlib's canonical owner for the subgroup generated by commutators of elements
--    from subgroups `H` and `K`.
-- 4. `IsFreeGroupBasis` from Definition `1-1-1` is the project's canonical source-facing way to
--    state that a displayed subset is a free basis of the subgroup it generates.
-- Primitive vs. derived:
-- the primitive source data are the nonidentity factor elements and their displayed commutators
-- in `A ∗ B`; the derived canonical subgroup is
-- `⁅(inl : A →* A ∗ B).range, (inr : B →* A ∗ B).range⁆`.

/-- The commutators of nonidentity elements from the two factors of the free product `A ∗ B`. -/
def freeProductFactorCommutatorSet : Set (A ∗ B) :=
  { g | ∃ a : A, a ≠ (1 : A) ∧ ∃ b : B, b ≠ (1 : B) ∧
      g = ⁅(inl a : A ∗ B), (inr b : A ∗ B)⁆ }

/-- Membership in `freeProductFactorCommutatorSet A B` means being a commutator of nontrivial
elements coming from the two free-product factors. -/
@[simp] theorem mem_freeProductFactorCommutatorSet_iff (g : A ∗ B) :
    g ∈ freeProductFactorCommutatorSet A B ↔
      ∃ a : A, a ≠ (1 : A) ∧ ∃ b : B, b ≠ (1 : B) ∧
        g = ⁅(inl a : A ∗ B), (inr b : A ∗ B)⁆ :=
  Iff.rfl

/-- The subgroup generated by the displayed nontrivial factor commutators is the canonical
subgroup commutator of the two free-product factor subgroups. -/
theorem closure_freeProductFactorCommutatorSet_eq_factorSubgroupCommutator :
    Subgroup.closure (freeProductFactorCommutatorSet A B) =
      ⁅(inl : A →* A ∗ B).range, (inr : B →* A ∗ B).range⁆
    := by
  rw [Subgroup.commutator_def]
  have hset :
      { g : A ∗ B |
          ∃ x ∈ (inl : A →* A ∗ B).range, ∃ y ∈ (inr : B →* A ∗ B).range, ⁅x, y⁆ = g } =
        insert (1 : A ∗ B) (freeProductFactorCommutatorSet A B) := by
    ext g
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      rcases hx with ⟨a, rfl⟩
      rcases hy with ⟨b, rfl⟩
      by_cases ha : a = 1
      · simp [ha]
      · by_cases hb : b = 1
        · simp [hb]
        · right
          exact (mem_freeProductFactorCommutatorSet_iff A B _).2 ⟨a, ha, b, hb, rfl⟩
    · intro hg
      rcases hg with rfl | hg
      · exact ⟨1, ⟨1, by simp⟩, 1, ⟨1, by simp⟩, by simp⟩
      · rcases (mem_freeProductFactorCommutatorSet_iff A B _).1 hg with
          ⟨a, ha, b, hb, rfl⟩
        exact ⟨inl a, ⟨a, rfl⟩, inr b, ⟨b, rfl⟩, rfl⟩
  rw [hset, Subgroup.closure_insert_one]

/-- Remark 4-1-11: in the free product `A ∗ B`, the commutators `a b a⁻¹ b⁻¹` with
`a ∈ A \ {1}` and `b ∈ B \ {1}` form a free basis of the subgroup that they generate. Via
`closure_freeProductFactorCommutatorSet_eq_factorSubgroupCommutator`, this generated subgroup is
the canonical subgroup commutator of the two factor ranges, so the basis statement is recorded in
that canonical ambient subgroup. -/
-- Proof sketch: realize `A ∗ B` as the free product of the factor subgroups given by the canonical
-- inclusions and apply the normal-form theorem for reduced words in a free product. A nonempty
-- reduced word in distinct commutators stays reduced after expansion into alternating factor
-- letters, so it is nontrivial; then the subgroup generated by these commutators is free on the
-- displayed generating set.
theorem freeProduct_factor_commutators_isFreeGroupBasis :
    IsFreeGroupBasis
      { g : (⁅(inl : A →* A ∗ B).range, (inr : B →* A ∗ B).range⁆ : Subgroup (A ∗ B)) |
          (g : A ∗ B) ∈ freeProductFactorCommutatorSet A B } := sorry

end

/-! ### Remark_4_1_12 (from Items/Chap04) -/
universe u v w x y

open scoped Monoid.Coprod

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: group theory, free products, direct products, and free indecomposability.

Layer triage:
- `source-facing`: a group `G` together with a nontrivial free-product decomposition
  `G ≃* A ∗ B` and a nontrivial direct-product decomposition `G ≃* D × E`.
- `core/canonical`: `Monoid.Coprod` is mathlib's owner for free products, the product type
  `D × E` is the canonical owner for direct products, and `IsFreelyIndecomposable` from
  Proposition `2-5-12` is the project's owner abstraction for excluding nontrivial free-product
  decompositions.
- `bridge/view`: the two source-facing equivalences are composed into
  `D × E ≃* A ∗ B`, and the textbook contradiction is then a short corollary of the owner field
  `of_mulEquiv_coprod`.

Domain sampling:
1. `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner abstraction for free products.
2. `IsFreelyIndecomposable` from Proposition `2-5-12` is the chapter owner for the property
   “every free-product decomposition has a trivial factor”.
3. `IsFreelyIndecomposable.of_mulEquiv_coprod` is the owner field that turns a free-product
   equivalence into the conclusion `Subsingleton A ∨ Subsingleton B`.
4. `false_of_nontrivial_of_subsingleton` is the atomic mathlib contradiction used to pass from the
   owner conclusion `Subsingleton A ∨ Subsingleton B` back to the source wording with
   nontriviality hypotheses.

Best owner abstraction:
- the reusable mathematical core is `IsFreelyIndecomposable`, not a one-off theorem returning
  `False` from two decomposition witnesses.

Primitive vs. derived:
- primitive public data: the nontrivial direct-product factors `D`, `E` and, in the source-facing
  corollary, the nontrivial free-product factors `A`, `B`;
- derived API: free indecomposability of `D × E` and the resulting contradiction for a
  simultaneous nontrivial free-product decomposition of `G`.
-/

-- Proof sketch: a nontrivial direct product has enough commuting structure to force any
-- free-product decomposition to collapse to a trivial factor, so the correct reusable output is
-- the owner predicate `IsFreelyIndecomposable`. The source-facing remark then follows by applying
-- that owner predicate to the given free-product equivalence.
/-- A direct product of two nontrivial groups is freely indecomposable. -/
theorem isFreelyIndecomposable_prod
    (D : Type x) [Group D] (E : Type y) [Group E]
    (hD : Nontrivial D) (hE : Nontrivial E) :
    IsFreelyIndecomposable (D × E) := by
  sorry

/-- Remark 4-1-12: a group that is isomorphic to a free product `A ∗ B` with both factors
nontrivial cannot also be isomorphic to a direct product `D × E` with both factors nontrivial. -/
theorem not_nontrivial_directProduct_of_nontrivial_freeProduct
    {A : Type v} [Group A] {B : Type w} [Group B]
    {D : Type x} [Group D] {E : Type y} [Group E]
    (hA : Nontrivial A) (hB : Nontrivial B)
    (hfree : G ≃* A ∗ B)
    (hD : Nontrivial D) (hE : Nontrivial E)
    (hdirect : G ≃* D × E) : False := by
  rcases (isFreelyIndecomposable_prod D E hD hE).of_mulEquiv_coprod (hdirect.symm.trans hfree) with
    hA' | hB'
  · letI := hA
    letI := hA'
    exact false_of_nontrivial_of_subsingleton A
  · letI := hB
    letI := hB'
    exact false_of_nontrivial_of_subsingleton B

end

/-! ### Theorem_4_1_13 (from Items/Chap04) -/
universe u v w

open Monoid

section

variable {ι : Type v} {F : Type u} {A : ι → Type w}
variable [Group F] [IsFreeGroup F] [Group.FG F]
variable [∀ i, Group (A i)]

/-!
Primary domain: indexed free products of groups and free-group decompositions.

Layer triage:
- `source-facing`: a finitely generated free group `F`, a surjection `φ : F →* CoprodI A`,
  and a decomposition of `F` as an indexed free product of subgroup factors mapping onto the
  canonical factor subgroups.
- `core/canonical`: `IsFreeGroup` for the ambient free-group hypothesis, `CoprodI` with its
  canonical inclusions `CoprodI.of`, and `Subgroup.map` for the image condition.
- `bridge/view`: the textbook equality `F = *ᵢ H i` is expressed by a multiplicative equivalence
  `CoprodI (fun i ↦ H i) ≃* F` whose restriction to each canonical inclusion is the
  corresponding subgroup embedding. Proposition `3-3-7` already states this theorem at the owner
  level used here, so this file should recall that theorem directly rather than restating a local
  copy.

Domain sampling:
1. `CoprodI` is mathlib's owner abstraction for indexed free products.
2. `CoprodI.of` is the canonical factor inclusion, including for subgroup-indexed free products.
3. `CoprodI.lift` is the universal-property owner for maps out of an indexed free product.
4. `exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct` from
   Proposition `3-3-7` is the project owner theorem for this finitely generated source-facing
   statement, while
   `Subgroup.map` is the canonical owner for the factor-image condition.

Primitive vs. derived:
- primitive public data: the finitely generated free group `F`, the factor family `A`, and the
  surjection
  `φ : F →* CoprodI A`;
- derived API: the subgroup family `H`, the free-product equivalence onto `F`, the compatibility
  of that equivalence with the canonical inclusions, and the image-identification equalities.
-/

/- Theorem `4-1-13` adds no new owner-level API beyond Proposition `3-3-7`, so this file recalls
that upstream theorem directly instead of restating its interface as a parallel local item. -/
#check (exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct :
  ∀ (_ : Nonempty ι) (φ : F →* CoprodI A) (_ : Function.Surjective φ),
    ∃ H : ι → Subgroup F, ∃ e : CoprodI (fun i ↦ H i) ≃* F,
      (∀ i, e.toMonoidHom.comp CoprodI.of = (H i).subtype) ∧
        ∀ i, Subgroup.map φ (H i) = (CoprodI.of : A i →* CoprodI A).range)

end

/-! ### Corollary_4_1_14 (from Items/Chap04) -/
universe u v

open Monoid

noncomputable section

section

variable {ι : Type u} {A : ι → Type v}
variable [Fintype ι] [∀ i, Group (A i)] [∀ i, Group.FG (A i)]

/-!
Primary domain: ranks of finitely generated groups and finite indexed free products.

Layer triage:
- `source-facing`: the rank of a finite free product `*ᵢ A i`.
- `core/canonical`: `Group.rank` is the owner for the minimum number of generators of a finitely
  generated group, `Monoid.CoprodI` is the owner abstraction for indexed free products, and
  `FreeGroupBasis.coprodI` is the canonical free-basis owner for free products of free groups.
- `bridge/view`: Proposition `3-3-7`, recalled later in Chapter 4 as Theorem `4-1-13`, is the
  owner bridge from a surjection out of a finitely generated free group onto `CoprodI A` to a
  corresponding free-product decomposition of that free group by subgroup factors mapping onto the
  ambient factors.

Domain sampling:
1. `Group.rank`, `Group.rank_spec`, and `Group.rank_le_of_surjective` in
   `Mathlib/GroupTheory/Rank` are the canonical owner API for finite generating-number statements.
2. `Monoid.CoprodI`, `Monoid.CoprodI.of`, and `Monoid.CoprodI.lift` in
   `Mathlib/GroupTheory/CoprodI` are the canonical free-product owners.
3. `FreeGroupBasis.coprodI` in `Mathlib/GroupTheory/CoprodI` is the owner theorem saying that a
   free product of free groups is free on the sigma-sum of the component bases.
4. `exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct` from Proposition
   `3-3-7` is the project owner bridge; Theorem `4-1-13` only recalls that declaration, so this
   file should depend on the owner directly rather than on the recall wrapper.

Primitive vs. derived:
- primitive public data: the finite family `A : ι → Type` of finitely generated groups;
- derived API: finite generation of `CoprodI A`, the sharp upper rank bound from the union of
  factor generating sets, and the free-group decomposition of a minimal-rank free cover used for
  the lower bound.
-/

private instance coprodI_fg : Group.FG (CoprodI A) := by
  sorry

/-- Corollary 4-1-14: for a finite free product `*ᵢ A i`, the minimum number of generators is the
sum of the minimum numbers of generators of the factors. -/
-- Proof sketch: the upper bound comes from taking minimal generating sets in each factor and
-- adjoining them through the canonical inclusions into the indexed free product. For the lower
-- bound, take a free cover of `CoprodI A` on exactly `Group.rank (CoprodI A)` generators and apply
-- Proposition `3-3-7` (recalled in Chapter 4 as Theorem `4-1-13`) to decompose that free group
-- as a free product of subgroup factors mapping onto the `A i`. The free-product basis theorem
-- `FreeGroupBasis.coprodI` identifies the total number of basis elements of those subgroup factors
-- with the rank of the covering free group, while each factor rank dominates the rank of the
-- corresponding quotient `A i`.
theorem rank_coprodI_eq_sum :
    Group.rank (CoprodI A) = ∑ i, Group.rank (A i) := by
  sorry

end

/-! ### Theorem_4_1_15 (from Items/Chap04) -/
universe u v w

open Monoid
open scoped Pointwise

section

variable {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]

/-!
Primary domain: subgroup structure of free products.

Layer triage:
- `source-facing`: the Kurosh subgroup theorem for a subgroup `H ≤ CoprodI G`.
- `core/canonical`: `CoprodI` is the owner abstraction for indexed free products, and
  `IsKuroshFactorDecomposition` is the project owner for the corresponding decomposition data.
- `bridge/view`: the ambient-factor description of each Kurosh subgroup factor is expressed using
  `Subgroup.map` and conjugation by `MulAut.conj`; no extra owner is needed here because
  Proposition `3-3-6` already states the theorem at the correct source-facing level.

Domain sampling:
1. `CoprodI` and `CoprodI.of` are the canonical indexed free-product API.
2. `IsKuroshFactorDecomposition` from Chapter 1 is the project owner for the free-product
   decomposition data with one distinguished free factor.
3. `exists_kurosh_freeProduct_decomposition` from Proposition `3-3-6` already has the exact
   Kurosh-subgroup interface in this project.
4. `Subgroup.map` together with `MulAut.conj` is the canonical subgroup-conjugation API used to
   describe the factors.

Primitive vs. derived:
- primitive source-facing data: the subgroup `H` of `CoprodI G`;
- derived API: the free subgroup factor, the family of Kurosh factors, the free-product
  equivalence, and the ambient conjugacy description of each factor.
-/

/- Theorem 4-1-15 (Kurosh Subgroup Theorem): every subgroup of an indexed free product is itself
a free product of one free group together with subgroup factors whose ambient images are conjugate
to subgroups of the original free factors.

This item adds no new source-facing construction beyond Proposition `3-3-6`, so the file keeps a
direct recall of that canonical theorem instead of restating its interface locally. -/
#check exists_kurosh_freeProduct_decomposition

end
