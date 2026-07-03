import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_5_1 (from Items/Chap01) -/
open MulAction Matrix.GeneralLinearGroup
open scoped commutatorElement

universe u v

noncomputable section

section

variable {F : Type v} [Group F]

open RankTwoFreeGroup

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a rank-two basis `basis : FreeGroupBasis (Fin 2) F` and the cyclic word
-- determined by the commutator of its two basis elements.
-- `core/canonical`: the basis-induced action `basis.cyclicWordMulAction` on `CyclicWord (Fin 2)`,
-- the owner subgroup `MulAction.stabilizer`, the bridge `basis.toGL : MulAut F →* GL (Fin 2) ℤ`,
-- and the determinant morphism on `GL (Fin 2) ℤ`.
-- `bridge/view`: `commutatorCyclicWord` is the standard rank-two commutator word, while the
-- textbook subgroup `SA(F)` is expressed directly by the determinant-one kernel
-- `(det.comp basis.toGL).ker`.
--
-- Domain sampling:
-- 1. `CyclicWord X` and the induced action from Proposition `1-5-2` are the chapter owner API for
--    cyclic words and their automorphic images.
-- 2. `MulAction.stabilizer` is mathlib's owner subgroup for automorphisms fixing a cyclic word.
-- 3. `FreeGroupBasis.toGL` from Corollary `1-4-16` is the canonical bridge from automorphisms of
--    a rank-two free group to `GL (Fin 2) ℤ`.
-- 4. `Matrix.GeneralLinearGroup.det` is the owner determinant morphism on `GL (Fin 2) ℤ`.
--
-- Primitive vs. derived:
-- the primitive source data are only the chosen rank-two basis; the commutator cyclic words come
-- from the source-facing owner declarations `RankTwoFreeGroup.commutatorCyclicWord` and
-- `RankTwoFreeGroup.inverseCommutatorCyclicWord` imported from Proposition `1-5-2`. The
-- stabilizer subgroup and the determinant-one kernel `(det.comp basis.toGL).ker` are derived
-- owner constructions built from those data.

/-- Proposition 1-5-1 (1): every automorphism of a rank-two free group carries the commutator
cyclic word to itself or to its inverse. -/
-- Proof sketch: it is enough to check the claim on elementary Nielsen automorphisms generating
-- `Aut(F)`. Direct calculations on the commutator show that proper generators fix the cyclic word
-- and improper generators send it to the inverse cyclic word.
theorem smul_commutatorCyclicWord_eq_or_eq_inverse
    (basis : FreeGroupBasis (Fin 2) F) (α : MulAut F) :
    letI := basis.cyclicWordMulAction
    α • commutatorCyclicWord = commutatorCyclicWord ∨
      α • commutatorCyclicWord = inverseCommutatorCyclicWord := sorry

/-- Proposition 1-5-1 (2): the stabilizer `A_w` of the commutator cyclic word is the subgroup
`SA(F)` of proper automorphisms. -/
-- Proof sketch: combine the previous dichotomy with the determinant description of proper
-- automorphisms through `basis.toGL`; determinant `1` is exactly the case where the commutator
-- cyclic word is fixed rather than inverted.
theorem commutatorCyclicWord_stabilizer_eq_det_comp_toGL_ker
    (basis : FreeGroupBasis (Fin 2) F) :
    letI := basis.cyclicWordMulAction
    stabilizer (MulAut F) commutatorCyclicWord = (det.comp basis.toGL).ker := sorry

/-- Proposition 1-5-1 (3): the subgroup `SA(F)` of proper automorphisms has index `2` in
`Aut(F)`. -/
-- Proof sketch: the determinant of `basis.toGL α` detects whether `α` is proper or improper, and
-- its image is exactly `{1, -1}`. Therefore the determinant-one kernel has index `2`.
theorem det_comp_toGL_ker_index_eq_two (basis : FreeGroupBasis (Fin 2) F) :
    ((det.comp basis.toGL).ker).index = 2 := sorry

end FreeGroupBasis

end

/-! ### Proposition_1_5_2 (from Items/Chap01) -/
universe u v

open MulAction QuotientGroup
open scoped commutatorElement

noncomputable section

section

variable {X : Type u}

namespace FreeGroupBasis

variable {F : Type v} [Group F]

/-- The basis-induced `Aut(F)`-action on cyclic words over the basis alphabet `X`. -/
@[reducible] noncomputable def cyclicWordMulAction (basis : FreeGroupBasis X F) :
    MulAction (MulAut F) (CyclicWord X) :=
  MulAction.compHom (CyclicWord X)
    (MulAut.congr basis.repr : MulAut F →* MulAut (FreeGroup X))

end FreeGroupBasis

namespace RankTwoFreeGroup

/-- The standard commutator `[x, y]` in the rank-two free group on `Fin 2`. -/
def commutator : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆

/-- The cyclic word determined by the rank-two commutator `[x, y]`. -/
def commutatorCyclicWord : CyclicWord (Fin 2) :=
  CyclicWord.conjClassesEquiv.symm <| ConjClasses.mk commutator

/-- The cyclic word determined by the inverse commutator `[x, y]⁻¹`. -/
def inverseCommutatorCyclicWord : CyclicWord (Fin 2) :=
  CyclicWord.conjClassesEquiv.symm <| ConjClasses.mk commutator⁻¹

end RankTwoFreeGroup

-- Layer triage:
-- `source-facing`: a cyclic word `w : CyclicWord X` in the free group on a basis `X`, together
-- with the exceptional rank-two commutator-power shape.
-- `core/canonical`: the action of `MulAut (FreeGroup X)` on `CyclicWord X`, the owner subgroup
-- `MulAction.stabilizer`, the inner automorphism owner subgroup
-- `MulAut.innerAutomorphismSubgroup (FreeGroup X)`, the subgroup image `Subgroup.map`, and the
-- owner index quantity `Subgroup.index`.
-- `bridge/view`: the textbook quotient `Aut(F) / JA(F)` is rendered as the quotient modulo the
-- canonical inner automorphism subgroup, and the exceptional source case is expressed by
-- transporting the standard commutator from `FreeGroup (Fin 2)` across a basis equivalence and
-- then passing to the conjugacy class of the resulting nonzero integral power.
-- Domain sampling:
-- 1. The `MulAction (MulAut (FreeGroup X)) (CyclicWord X)` instance from Definition `1-4-17`
--    is the chapter owner action of free-group automorphisms on cyclic words.
-- 2. `MulAction.stabilizer` is mathlib's owner subgroup for point stabilizers under a group
--    action.
-- 3. `MulAut.innerAutomorphismSubgroup` from Proposition `1-4-5` is the chapter owner subgroup
--    of inner automorphisms.
-- 4. `Subgroup.map` and `Subgroup.index` are the owner APIs for the image of a subgroup in a
--    quotient group and for finite-versus-infinite index.
-- Primitive vs. derived:
-- the primitive source data are only the cyclic word `w`, the nontriviality hypothesis that its
-- conjugacy class is nontrivial, and the free-basis rank condition `1 < Nat.card X`; the
-- stabilizer in `Aut(F(X))`, its image in the quotient by inner automorphisms, and the
-- index-zero reformulation of infinite index are all derived owner API.
/-- Proposition 1-5-2: let `w` be a nontrivial cyclic word in a free group of rank at least `2`.
If `w` is not the cyclic word of a nonzero power of a basic commutator in rank `2`, then the
image of its stabilizer in `Aut(F) / JA(F)` has infinite index. -/
-- Proof sketch: assume the image of the stabilizer has finite index in the `JA`-quotient. Then the
-- orbit of `w` under automorphisms has bounded cyclic length modulo `JA`, so repeated Nielsen
-- moves cannot create arbitrarily long cyclic representatives. Whitehead's length-growth argument
-- forces the cyclic word to alternate between two basis letters and hence to be a nonzero power
-- of the rank-two commutator.
theorem cyclicWord_stabilizer_image_in_JAQuotient_index_eq_zero_of_not_rankTwo_commutator_power
    (w : CyclicWord X) (hX : 1 < Nat.card X) (hw : w.toConjClasses ≠ ConjClasses.mk 1)
    (hcomm :
      ¬ ∃ e : X ≃ Fin 2, ∃ k : ℤ, k ≠ 0 ∧
        w.toConjClasses =
          ConjClasses.mk ((FreeGroup.freeGroupCongr e.symm RankTwoFreeGroup.commutator) ^ k)) :
    (Subgroup.map (mk' (JA(FreeGroup X)))
      (stabilizer (MulAut (FreeGroup X)) w)).index = 0 :=
  sorry

/-! ### Theorem_1_5_3 (from Items/Chap01) -/
universe u

open MulAction

noncomputable section

section

variable {F : Type u} [Group F]

namespace FreeGroupBasis

/-- The ordered product `x₁^{a₁} x₂^{a₂} ⋯ xₙ^{aₙ}` attached to a finite list of exponents with
respect to the chosen countable basis `basis`. -/
def orderedBasisPowerWord (basis : FreeGroupBasis ℕ F) (exponents : List ℕ) : F :=
  (List.ofFn fun i : Fin exponents.length ↦ basis ((i : ℕ) + 1) ^ exponents[i]).prod

end FreeGroupBasis

/- Theorem 1-5-3 lives in the domain of basis-dependent automorphism orbits in free groups. -/
-- Layer triage:
-- `source-facing`: a free group `F` equipped with a chosen countable basis
-- `basis : FreeGroupBasis ℕ F`, together with exponent lists specifying the words
-- `x₁^{a₁} ⋯ xₘ^{aₘ}` and `x₁^{b₁} ⋯ xₙ^{bₙ}`.
-- `core/canonical`: the owner abstraction `FreeGroupBasis ℕ F` and the orbit relation
-- `orbitRel (MulAut F) F`.
-- `bridge/view`: the concrete model `FreeGroup ℕ` is recovered by specializing
-- `basis := FreeGroupBasis.ofFreeGroup ℕ`.
-- Domain sampling:
-- 1. `FreeGroupBasis ℕ F` is the chapter's owner abstraction for “a free group with a chosen
--    countable basis”.
-- 2. `FreeGroupBasis.ofFreeGroup ℕ` is the canonical basis on the concrete model `FreeGroup ℕ`.
-- 3. `orbitRel (MulAut F) F` is mathlib's owner relation for automorphism-equivalence.
-- 4. `automorphism_orbitRel_iff_exists_automorphism_eq` is the chapter's canonical bridge back
--    to the source existential formulation.
-- Primitive vs. derived:
-- the primitive source data are the chosen basis and the exponent lists; the orbit relation and
-- automorphism-equivalence formulation are derived owner API.

/-- Theorem 1-5-3: for words of the form `x₁^{a₁} ⋯ xₘ^{aₘ}` and `x₁^{b₁} ⋯ xₙ^{bₙ}` with all
exponents at least `2`, the two basis words lie in the same automorphism orbit if and only if the
exponent lists are permutations of one another, equivalently if and only if they have the same
length and the `bᵢ` are a permutation of the `aᵢ`. -/
-- Proof sketch: the forward direction is Whitehead's length-preservation argument for these
-- positive power words, showing that any chain of Whitehead moves preserves the multiplicity data
-- of the exponents after transporting along `basis.repr`. For the reverse direction, a
-- permutation of the chosen basis generators induces the required automorphism.
theorem orderedBasisPowerWord_orbitRel_iff_perm
    (basis : FreeGroupBasis ℕ F) (a b : List ℕ)
    (ha : ∀ n ∈ a, 2 ≤ n)
    (hb : ∀ n ∈ b, 2 ≤ n) :
    orbitRel (MulAut F) F (basis.orderedBasisPowerWord b) (basis.orderedBasisPowerWord a) ↔
      List.Perm a b := sorry

/-- Source-facing reformulation of Theorem 1-5-3 via the chapter's canonical orbit bridge. -/
theorem exists_automorphism_eq_ordered_basis_power_word_iff_perm
    (basis : FreeGroupBasis ℕ F) (a b : List ℕ)
    (ha : ∀ n ∈ a, 2 ≤ n)
    (hb : ∀ n ∈ b, 2 ≤ n) :
    (∃ α : MulAut F, α (basis.orderedBasisPowerWord a) = basis.orderedBasisPowerWord b) ↔
      List.Perm a b := by
  rw [← automorphism_orbitRel_iff_exists_automorphism_eq
    (basis.orderedBasisPowerWord a) (basis.orderedBasisPowerWord b)]
  exact orderedBasisPowerWord_orbitRel_iff_perm basis a b ha hb

end

/-! ### Proposition_1_5_5 (from Items/Chap01) -/
universe u

open CategoryTheory

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

namespace MulAut

local notation "Fix[" α "]" => MonoidHom.eqLocus (α : F →* F) 1

/-- Proposition 1-5-5: if `F` is a finitely generated free group and `α` is an automorphism of
finite order, then the subgroup of elements fixed by `α` is a free factor of `F`. -/
-- Layer triage:
-- `source-facing`: the finite-order automorphism `α : MulAut F` and its fixed subgroup.
-- `core/canonical`: the automorphism group `MulAut F`, the fixed-subgroup owner
-- `MonoidHom.eqLocus`, and the chapter free-factor-overgroup relation
-- `Subgroup.IsFreeFactorOf`.
-- `bridge/view`: `Subgroup.isFreeFactorOf_iff` unpacks this owner statement into a complementary
-- free factor inside the ambient overgroup `⊤`, while `Subgroup.IsFreeFactorOf.isSplitMono`
-- supplies the retract/split-inclusion view.
-- Domain sampling:
-- 1. `MulAut F` is the canonical owner abstraction for automorphisms of the ambient free group.
-- 2. `MonoidHom.eqLocus` is the canonical subgroup of elements on which two homomorphisms agree;
--    here it expresses the fixed subgroup as the equalizer of `α` and `1`.
-- 3. `Subgroup.IsFreeFactorOf` is the chapter owner abstraction for the source phrase “the fixed
--    subgroup is a free factor of `F`”.
-- 4. `[Group.FG F]` is the chapter's canonical finite-rank owner assumption for free groups; any
--    chosen finite basis or finite generator type should be derived from it internally.
-- Primitive vs. derived:
-- the primitive data are only the ambient owner assumptions `[IsFreeGroup F] [Group.FG F]`
-- together with `α` and its finite-order hypothesis; the fixed subgroup is derived as
-- `((α : F →* F).eqLocus 1)`, and any chosen complementary factor or split inclusion is derived
-- API.
-- Proof sketch: realize the fixed subgroup of `α` as the subgroup fixed by the finite cyclic group
-- generated by `α`, then apply the Dyer--Scott fixed-point theorem for finite-order
-- automorphisms of finitely generated free groups to obtain a complementary free factor.
theorem fixed_eqLocus_isFreeFactorOf_top_of_isOfFinOrder
    (α : MulAut F) (hα : IsOfFinOrder α) :
    (Fix[α]).IsFreeFactorOf (⊤ : Subgroup F) := sorry

/-- Owner-level reformulation of Proposition 1-5-5: the inclusion of the fixed subgroup of a
finite-order automorphism into the ambient free group is split. -/
-- Layer triage:
-- `bridge/view`: this is the retract-subgroup companion to the owner-level free-factor statement
-- above.
-- Proof sketch: apply the derived owner theorem `Subgroup.IsFreeFactorOf.isSplitMono` to the
-- free-factor statement above.
theorem fixed_eqLocus_subtype_isSplitMono_of_isOfFinOrder
    (α : MulAut F) (hα : IsOfFinOrder α) :
    IsSplitMono (GrpCat.ofHom (Fix[α]).subtype) := by
  simpa using
    (fixed_eqLocus_isFreeFactorOf_top_of_isOfFinOrder α hα).isSplitMono

end MulAut

end

/-! ### Proposition_1_5_6 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {X : Type u}

open CyclicWord

local instance instDecidableEqBasisSupport_156 : DecidableEq X := Classical.decEq X

/-- The unsigned basis support of the canonical reduced word of a free-group element. -/
abbrev reducedWordSupport (g : FreeGroup X) : Finset X :=
  (g.toWord.map Prod.fst).toFinset

/-- Proposition 1-5-6: if the canonical reduced word of `g : FreeGroup X` has minimal length in
its `Aut(F(X))`-orbit, then every automorphic image of `g` has at least as many distinct basis
letters in its canonical reduced word. Equivalently, if exactly `n` basis letters occur in the
canonical reduced word of `g`, then at least `n` basis letters occur in every automorphic image. -/
-- Layer triage:
-- `source-facing`: an ordinary word of minimal length in its automorphic orbit together with the
-- number of distinct basis letters occurring in it.
-- `core/canonical`: the ambient owner `FreeGroup X`, the canonical reduced-word API
-- `FreeGroup.toWord`, and the automorphism group `MulAut (FreeGroup X)`.
-- `bridge/view`: a reduced list word is represented canonically by the corresponding element of
-- `FreeGroup X`, so support is read from `g.toWord` instead of from an arbitrary representative.
-- Domain sampling:
-- 1. `FreeGroup.toWord` is the owner reduced-word normal form on `FreeGroup X`.
-- 2. `reducedWordSupport g = (g.toWord.map Prod.fst).toFinset` is the source-facing finite
--    support view derived from that owner normal form.
-- 3. `CyclicWord.support` is the owner unsigned-support API derived from `CyclicWord.letters`.
-- 4. `MulAut (FreeGroup X)` is mathlib's owner abstraction for automorphisms of the free group.
-- Primitive vs. derived:
-- the primitive datum is the automorphic-orbit representative `g`; the occurring-basis-letter set
-- and its cardinality are derived from the canonical reduced word `g.toWord`.
-- Proof sketch: use Whitehead peak reduction to factor any automorphism into a chain whose
-- intermediate words never shorten below the minimal length. The first step at which a new basis
-- letter appears would have to be a Whitehead move inserting that letter, which necessarily
-- increases length, contradicting the monotone length bound.
theorem reducedWord_support_card_le_automorphic_image_support_card_of_minimal_length
    (g : FreeGroup X)
    (hmin : ∀ α : MulAut (FreeGroup X), g.toWord.length ≤ (α g).toWord.length)
    (α : MulAut (FreeGroup X)) :
    (reducedWordSupport g).card ≤ (reducedWordSupport (α g)).card := sorry

/-- Cyclic-word companion of the support monotonicity statement: a cyclic word of minimal cyclic
length in its automorphic orbit cannot lose distinct basis letters under an automorphism.
Equivalently, if exactly `n` basis letters occur in `w`, then at least `n` occur in every
automorphic image of `w`. -/
-- Proof sketch: factor the relevant automorphism by Whitehead peak reduction for cyclic words and
-- inspect the first step where a new basis letter would appear. As in the ordinary-word case,
-- that step inserts a new letter and so forces a strict increase in cyclic length.
theorem cyclicWord_support_card_le_automorphic_image_support_card_of_minimal_length
    (w : CyclicWord X)
    (hmin : ∀ α : MulAut (FreeGroup X), w.length ≤ (α • w).length)
    (α : MulAut (FreeGroup X)) :
    (support w).card ≤ (support (α • w)).card := sorry

end

/-! ### Proposition_1_5_7 (from Items/Chap01) -/
universe u

noncomputable section

open MulAction

section

variable {X : Type u} {F : Type u} [Group F]

namespace FreeGroupBasis

local instance instDecidableEqBasisSupport_157 : DecidableEq X := Classical.decEq X

/-- Owner-level formulation of Proposition 1-5-7: if an element `g` of a free group has minimal
reduced length among its automorphic images with respect to the chosen basis `basis`, and every
basis generator occurs in the canonical reduced word of `g`, then the stabilizer of `g` in
`Aut(F)` is torsion-free. -/
-- Layer triage:
-- `source-facing`: the proposition concerns a word whose reduced length is minimal in its
-- automorphic orbit and whose support contains every basis generator.
-- `core/canonical`: the ambient owner objects are `FreeGroupBasis X F`, the canonical reduced word
-- `(basis.repr g).toWord` of the represented element `g : F`, and the stabilizer subgroup
-- `stabilizer (MulAut F) g`.
-- `bridge/view`: `basisLetterOccurs basis x g` is the chapter owner-side occurrence predicate for
-- basis generators in the canonical reduced word of `g`, and a reduced ordinary word
-- `w : List (X × Bool)` gives the source presentation of the same element via
-- `basis.repr.symm (FreeGroup.mk w)`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the chapter and mathlib owner abstraction for a chosen basis of `F`.
-- 2. `basisLetterOccurs basis x g` from Proposition `1-7-4` is the chapter owner-side predicate
--    expressing that the basis generator `x` occurs in the canonical reduced word of `g`.
-- 3. `stabilizer (MulAut F) g` is the canonical owner subgroup for automorphisms fixing `g`.
-- 4. `FreeGroup.mk` and `FreeGroup.toWord` already read a raw list word through the canonical
--    reduced-word normal form, so ordinary-word occurrence and length conditions belong in the
--    bridge layer only through `FreeGroup.mk w`, not through an extra reducedness field.
-- Primitive vs. derived:
-- the primitive data are the basis `basis` and the group element `g`; the reduced word used to
-- read occurrence is derived canonically from `basis.repr g`, while any concrete list `w`
-- representing `g` belongs only to the bridge layer.
-- Proof sketch: let `α` be a finite-order element of the stabilizer. By Proposition 1-5-5, its
-- fixed subgroup is a free factor of `F`, and it contains `g` because `α` stabilizes `g`. The
-- minimal-length and full-support hypotheses imply, by the preceding proposition, that `g` lies in
-- no proper free factor. Hence the fixed subgroup is all of `F`, so `α = 1`.
theorem stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
    (basis : FreeGroupBasis X F) (g : F)
    (hmin : ∀ α : MulAut F,
      (basis.repr g).toWord.length ≤ (basis.repr (α g)).toWord.length)
    (hcontains : ∀ x : X, basisLetterOccurs basis x g) :
    IsMulTorsionFree (stabilizer (MulAut F) g) := by
  sorry

/-- Source-facing ordinary-word bridge for Proposition 1-5-7: if the canonical reduced form of an
ordinary word `w` has minimal reduced length among its automorphic images and contains every basis
generator, then the stabilizer of the represented element is torsion-free. The hypotheses are read
directly on `FreeGroup.mk w`, so they already refer to the canonical normal form of the element
represented by `w`. -/
theorem ordinaryWord_stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
    (basis : FreeGroupBasis X F) (w : List (X × Bool))
    (hmin : ∀ α : MulAut F,
      (FreeGroup.mk w).toWord.length ≤
        (basis.repr (α (basis.repr.symm (FreeGroup.mk w)))).toWord.length)
    (hcontains : ∀ x : X, basisLetterOccurs basis x (basis.repr.symm (FreeGroup.mk w))) :
    IsMulTorsionFree (stabilizer (MulAut F) (basis.repr.symm (FreeGroup.mk w))) := by
  refine
    stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
      basis (basis.repr.symm (FreeGroup.mk w)) ?_ hcontains
  intro α
  simpa using hmin α

end FreeGroupBasis

end

/-! ### Proposition_1_5_8 (from Items/Chap01) -/
universe u v

open MulAction

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

namespace FreeGroupBasis

/-- Proposition 1-5-8: if `w` is a cyclic word of minimal cyclic length in its automorphism orbit
with respect to a chosen free basis of `F`, if every basis letter occurs in `w`, and if a
finite-order automorphism `α` fixes `w`, then the order of `α` divides the cyclic length of `w`.
-/
-- Layer triage:
-- `source-facing`: a chosen basis `basis : FreeGroupBasis X F`, a cyclic word `w : CyclicWord X`
-- of minimal cyclic length in its automorphism orbit, the separate full-support hypothesis that
-- every basis generator occurs in `w`, and an automorphism `α : MulAut F` fixing `w`.
-- `core/canonical`: `CyclicWord X`, the length function `CyclicWord.length`, the canonical
-- basis-induced action `basis.cyclicWordMulAction`, the owner unsigned-letter view
-- `CyclicWord.letters`, the full-support predicate `CyclicWord.HasFullSupport`, the stabilizer
-- subgroup `stabilizer (MulAut F) w`, and the finite-order predicate `IsOfFinOrder`.
-- `bridge/view`: `MulAut.congr basis.repr` is the transport used to build
-- `basis.cyclicWordMulAction` from the canonical free-group action.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the owner abstraction for a chosen free basis of `F`.
-- 2. `FreeGroupBasis.cyclicWordMulAction` from Proposition `1-5-2` is the owner basis-induced
--    `Aut(F)`-action on cyclic words over `X`.
-- 3. Proposition `1-5-6` already states cyclic-word orbitwise minimality in the owner action form
--    `∀ β : MulAut (FreeGroup X), w.length ≤ (β • w).length`; the same action-based interface is
--    the canonical minimality surface here after transport across the chosen basis.
-- 4. `CyclicWord.HasFullSupport` and `stabilizer (MulAut F) w` are the owner APIs for the
--    separate source conditions “contains every basis letter” and “`α` fixes `w`”.
-- Primitive vs. derived:
-- the primitive data are the chosen basis, the cyclic word, and the automorphism; minimality of
-- `w` under the basis-induced action and containment of basis generators in `w` are separate
-- source-facing hypotheses, with containment expressed through `CyclicWord.HasFullSupport`;
-- the source phrase “`α` fixes `w`” is refined to the owner hypothesis
-- `α ∈ stabilizer (MulAut F) w`.
-- Proof sketch: choose the finite orbit of cyclic representatives of `w` under the cyclic action
-- of the subgroup generated by `α`. Minimality and the basis-containment hypothesis force every
-- orbit to have cardinality `orderOf α`, so the total number of letters in a representative of `w`
-- is a union of `orderOf α`-element orbits.
theorem orderOf_dvd_cyclicWord_length_of_fixed_minimal_word
    (basis : FreeGroupBasis X F) (w : CyclicWord X) (α : MulAut F)
    (hcontains : w.HasFullSupport)
    (hmin : letI := basis.cyclicWordMulAction
      ∀ β : MulAut F, w.length ≤ (β • w).length)
    (hfix : letI := basis.cyclicWordMulAction
      α ∈ stabilizer (MulAut F) w)
    (hα : IsOfFinOrder α) :
    orderOf α ∣ w.length := sorry

end FreeGroupBasis

end

/-! ### Proposition_1_5_9 (from Items/Chap01) -/
universe u v

open MulAction

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

private def cyclicWordFamilyFinset {m : ℕ} (U : Fin m → CyclicWord X) :
    Finset (CyclicWord X) := by
  classical
  exact (Finset.univ : Finset (Fin m)).image U

private theorem cyclicWordFamily_stabilizer_eq_fixingSubgroup
    (basis : FreeGroupBasis X F) {m : ℕ} (U : Fin m → CyclicWord X) :
    letI := basis.cyclicWordMulAction
    stabilizer (MulAut F) U =
      fixingSubgroup (MulAut F) (cyclicWordFamilyFinset U : Set (CyclicWord X)) := by
  classical
  letI := basis.cyclicWordMulAction
  ext α
  rw [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
  constructor
  · intro hα w hw
    change w ∈ cyclicWordFamilyFinset U at hw
    rcases Finset.mem_image.mp hw with ⟨i, -, rfl⟩
    change (α • U) i = U i
    simpa using congrArg (fun V : Fin m → CyclicWord X ↦ V i) hα
  · intro hα
    ext i
    simpa using congrArg Subtype.val <| hα (U i) <| by
      change U i ∈ cyclicWordFamilyFinset U
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

-- Layer triage:
-- `source-facing`: a finite basis `basis : FreeGroupBasis X F`, a finite set
-- `S : Finset (CyclicWord X)`, and the subgroup of `Aut(F)` fixing each cyclic word in `S`.
-- `core/canonical`: `Group.IsFinitelyPresented` as mathlib's owner notion of admitting a finite
-- presentation, together with the basis-induced `Aut(F)`-action `basis.cyclicWordMulAction` and
-- the owner subgroup `MulAction.fixingSubgroup`.
-- `bridge/view`: a tuple `U : Fin m → CyclicWord X` presents the same finite collection as
-- `Finset.univ.image U`, and its Pi-action stabilizer is exactly the fixing subgroup of that
-- finite set.
-- Domain sampling:
-- 1. `FreeGroupBasis.cyclicWordMulAction` from Proposition `1-5-2` is the owner basis-induced
--    `Aut(F)`-action on cyclic words over `X`.
-- 2. `MulAction.stabilizer` and `mem_stabilizer_iff` are mathlib's owner API for point
--    stabilizers.
-- 3. `MulAction.fixingSubgroup` and `mem_fixingSubgroup_iff` are mathlib's owner API for
--    pointwise fixers of a set.
-- 4. `Group.IsFinitelyPresented` is the owner notion of finite presentability.
-- Primitive vs. derived:
-- the primitive source data are the basis and the finite set `S`; the fixing subgroup is derived
-- canonically from `basis.cyclicWordMulAction`, while the tuple presentation
-- `U : Fin m → CyclicWord X` is only a bridge.
-- Proof sketch: McCool's algorithm constructs a finite generating set and a finite relator set for
-- the subgroup of automorphisms fixing the finite collection pointwise; this is exactly the data
-- needed to prove the canonical owner property `Group.IsFinitelyPresented`.
variable [Finite X]

/-- Proposition 1-5-9: for a free group `F` with finite basis `X` and a finite set `S` of cyclic
words over `X`, the subgroup of automorphisms fixing every member of `S` admits a finite
presentation. -/
theorem cyclicWordFinsetFixingSubgroup_isFinitelyPresented
    (basis : FreeGroupBasis X F) (S : Finset (CyclicWord X)) :
    letI := basis.cyclicWordMulAction
    Group.IsFinitelyPresented (fixingSubgroup (MulAut F) (S : Set (CyclicWord X))) := sorry

/-- Bridge form of Proposition 1-5-9 for a tuple presentation of the same finite collection. -/
theorem cyclicWordFamilyStabilizer_isFinitelyPresented
    (basis : FreeGroupBasis X F) {m : ℕ} (U : Fin m → CyclicWord X) :
    letI := basis.cyclicWordMulAction
    Group.IsFinitelyPresented (stabilizer (MulAut F) U) := by
  letI := basis.cyclicWordMulAction
  rw [cyclicWordFamily_stabilizer_eq_fixingSubgroup basis U]
  exact
    cyclicWordFinsetFixingSubgroup_isFinitelyPresented basis
      (cyclicWordFamilyFinset U)

end
