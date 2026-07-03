import Mathlib
import Mathlib.Algebra.Group.Conj
import Mathlib.Topology.NoetherianSpace

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_9_1 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance : DecidableEq X := Classical.decEq X

/-!
Primary domain: word-level small-cancellation estimates for cyclically reduced conjugates of
relators.

Layer triage:
- `source-facing`: a relator `r ∈ R` with a semi-reduced factorization `r = b₁ ⋯ bⱼ c`, where
  the `bᵢ` are pieces, together with a cyclically reduced conjugate `r'` and the maximal
  consecutive subword `c'` of `c` that still appears consecutively in the normal form of `r'`.
- `core/canonical`: `FreeGroupBasis X F` is the chapter owner for the chosen basis,
  `FreeGroupBasis.is_piece` and `C'(\lambda)[basis, R]` from Definition `5-2-1` are the owner
  notions for pieces and the small-cancellation hypothesis, `IsConj` is the owner relation for
  conjugacy, `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced normal
  forms, `SignedLetter X` is the project owner vocabulary for letters of `X^{±1}`, and
  `Vector (List (SignedLetter X)) j` is the chapter's canonical owner for an ordered family of
  exactly `j` piece-words.
- `bridge/view`: `basis.repr r` transports relators in `F` to the canonical free-group model
  `FreeGroup X`, while `List.IsInfix` is the list-level owner for “appears consecutively as a
  subword”.

Domain sampling:
1. `FreeGroupBasis.is_piece` is the established Chapter `5` owner predicate for piece words.
2. `C'(\lambda)[basis, R]` is the chapter owner for the small-cancellation inequality on pieces.
3. `IsConj` and `FreeGroup.IsCyclicallyReduced` are the owner predicates for the cyclically
   reduced conjugate `r'`.
4. `List.IsInfix` is the canonical list-level owner for consecutive subwords, so the maximality
   condition on `c'` should be phrased directly by two infix hypotheses plus a maximality bound on
   common infixes of `c` and `r'.toWord`.
5. `Vector (List (SignedLetter X)) j` from Definition `5-4-6` is the nearby chapter owner for an
   ordered family of exactly `j` piece-words, so the theorem should expose `j` and that `Vector`
   directly rather than re-encoding the same data as a plain `List` plus `pieces.length`.
6. `FreeGroupBasis.is_j_remnant` from Definition `5-4-6` is the nearby chapter owner for the
   initial-segment decomposition `s ++ pieces.toList.flatten`; the present lemma needs the
   source-facing suffix-oriented equality `pieces.toList.flatten ++ c`, so that orientation
   remains an explicit theorem hypothesis instead of a second local wrapper owner.

Primitive vs. derived:
- primitive public data: the basis `basis`, relator set `R`, parameter `lambda`, relator `r`,
  the number `j` of piece factors, the ordered piece family
  `pieces : Vector (List (SignedLetter X)) j`, the tail word `c`, the cyclically reduced
  conjugate `rPrime`, and the candidate maximal subword `cPrime`;
- derived API: the direct piece hypotheses on `pieces`, the source-facing factorization equality
  `(basis.repr r).toWord = pieces.toList.flatten ++ c`, the maximal-common-infix clauses for
  `cPrime`, and the final length inequality.
-/

namespace FreeGroupBasis

-- Proof sketch: use the `C'(\lambda)` estimate on each piece in the initial semi-reduced
-- factorization, compare the total deleted length with `j * \lambda * |r'|`, and use maximality
-- of `cPrime` together with the cyclically reduced conjugacy of `rPrime` to identify the
-- surviving consecutive letters of the tail `c` inside `rPrime.toWord`.
/-- Lemma 5-9-1: if `R` satisfies `C'(\lambda)` and `r ∈ R` has a semi-reduced factorization
`r = b₁ ⋯ bⱼ c` with each `bᵢ` a piece, then any maximal consecutive subword `cPrime` of the tail
`c` that still appears consecutively in the normal form of a cyclically reduced conjugate `rPrime`
of `r` has length strictly greater than `(1 - j \lambda) |rPrime|`, where `j` is the number of
piece factors. -/
theorem maximal_common_consecutive_subword_length_gt_of_condition_c_prime
    (basis : FreeGroupBasis X F) (R : Set F) (lambda : ℝ) {r : F}
    (hR : C'(lambda)[basis, R]) (hr : r ∈ R) (j : ℕ)
    {pieces : Vector (List (SignedLetter X)) j} {c : List (SignedLetter X)}
    (hpieces : ∀ piece ∈ pieces.toList, basis.is_piece R piece)
    (hfactor : (basis.repr r).toWord = pieces.toList.flatten ++ c)
    {rPrime : FreeGroup X} (hconj : IsConj rPrime (basis.repr r))
    (hrPrime_cyclic : FreeGroup.IsCyclicallyReduced rPrime.toWord)
    {cPrime : List (SignedLetter X)}
    (hcPrime_left : cPrime <:+: c) (hcPrime_right : cPrime <:+: rPrime.toWord)
    (hcPrime_max : ∀ ⦃t : List (SignedLetter X)⦄,
      t <:+: c → t <:+: rPrime.toWord → t.length ≤ cPrime.length) :
    (cPrime.length : ℝ) > (1 - (j : ℝ) * lambda) * (rPrime.toWord.length : ℝ) := sorry

end FreeGroupBasis

end

/-! ### Lemma_5_9_2 (from Items/Chap05) -/
universe u

set_option autoImplicit false

section

variable (X : Type u) [TopologicalSpace X]

/-!
Primary domain: Noetherian topological spaces and irreducible components.

Layer triage:
- `source-facing`: a Noetherian topological space `X`, its subspaces, its irreducible components,
  and the claim that each irreducible component contains a nonempty open subset of `X`.
- `core/canonical`: `TopologicalSpace.NoetherianSpace` is mathlib's owner abstraction for
  Noetherian spaces, and `irreducibleComponents X` is the owner for irreducible components.
- `bridge/view`: this file is recall-only. Each numbered clause of Lemma `5.9.2` already exists as
  a canonical owner theorem in mathlib, so the faithful refinement is direct recall rather than a
  parallel local wrapper.

Domain sampling:
1. `TopologicalSpace.NoetherianSpace.set` is the canonical subspace instance for Noetherian
   spaces.
2. `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` is the canonical finiteness
   theorem for irreducible components of a Noetherian space.
3. `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` is the
   canonical theorem that an irreducible component of a Noetherian space contains a nonempty open
   subset.
4. `irreducibleComponents X` from `Mathlib.Topology.Irreducible` is the owner set of irreducible
   components used by the third clause.

Primitive vs. derived:
- primitive public data: the ambient topological space `X` together with the instance
  `[TopologicalSpace.NoetherianSpace X]`;
- derived API: Noetherianity of subspaces, finiteness of irreducible components, and the existence
  of a nonempty open subset inside each irreducible component.
-/

/- Lemma 5-9-2 (1): any subset of a Noetherian topological space, with the induced topology, is
Noetherian. -/
#check TopologicalSpace.NoetherianSpace.set

/- Lemma 5-9-2 (2): a Noetherian topological space has finitely many irreducible components. -/
#check TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/- Lemma 5-9-2 (3): each irreducible component of a Noetherian topological space contains a
nonempty open subset of the ambient space. -/
#check TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent

end

/-! ### Theorem_5_9_3 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqX_5_9_3 : DecidableEq X := Classical.decEq X

/-!
Primary domain: one-eighth small-cancellation relators and the conjugacy obstruction `J`.

Layer triage:
- `source-facing`: a chosen basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`,
  the Chapter `5` small-cancellation hypothesis `C'(1 / 8)`, and the conclusion that no relator
  in `R` is conjugate to its inverse.
- `core/canonical`: `FreeGroupBasis.condition_c_prime`, written `C'(\lambda)[basis, R]`, is the
  chapter owner for the small-cancellation hypothesis, `Set.SatisfiesConditionJ`, written `J[R]`,
  is the owner predicate for the conclusion, and `IsConj` is the owner relation for conjugacy.
- `bridge/view`: this theorem is the direct bridge from the owner `C'((1 / 8 : ℝ))[basis, R]`
  to the already-owned predicate `J[R]`; it does not introduce a parallel wrapper for
  “not conjugate to its inverse”.

Domain sampling:
1. `FreeGroupBasis.condition_c_prime` from Definition `5-2-1` is the Chapter `5` owner for the
   `C'(\lambda)` hypothesis.
2. `Set.SatisfiesConditionJ` from Definition `5-9-7` is the owner predicate for the source
   condition that no relator is conjugate to its inverse.
3. `Set.not_isConj_inv` is the companion elimination lemma for `J[R]`, so the theorem should
   produce `J[R]` directly instead of a theorem with the same conclusion unpacked pointwise.
4. `IsConj` from mathlib is the canonical owner relation for conjugacy, so no explicit conjugator
   witness data belongs in the public interface.

Primitive vs. derived:
- primitive public data: the basis `basis`, the relator set `R`, the one-eighth
  small-cancellation hypothesis, and the nontriviality condition on relators in `R`;
- derived API: the owner-level conclusion `J[R]`.
- API refinement note: the extra nontriviality hypothesis remains explicit because the current
  Chapter `5` owner `condition_c_prime` does not encode the textbook convention that relators are
  already nontrivial cyclically reduced words.
-/

namespace FreeGroupBasis

-- Proof sketch: if some `r ∈ R` were conjugate to `r⁻¹`, pass to a cyclically reduced conjugate
-- of `basis.repr r`, compare it with the inverse cyclic word, and apply the Section `9`
-- one-eighth overlap estimate to obtain a common subword longer than half the relator length.
-- The nontriviality hypothesis rules out the degenerate empty-word case, and the overlap bound
-- contradicts the `C'(1 / 8)` piece inequality.
/-- Theorem 5-9-3: if the relator set `R` satisfies `C'(1 / 8)` with respect to `basis`, and no
relator in `R` is trivial, then `R` satisfies Condition `J`; equivalently, no relator in `R` is
conjugate to its inverse. -/
theorem satisfiesConditionJ_of_condition_c_prime_one_eighth
    (basis : FreeGroupBasis X F) (R : Set F) (hR : C'((1 / 8 : ℝ))[basis, R])
    (hrel_ne_one : ∀ ⦃r : F⦄, r ∈ R → r ≠ 1) :
    J[R] := by
  intro r hr
  have _hr_ne_one : r ≠ 1 := hrel_ne_one hr
  sorry

end FreeGroupBasis

end

/-! ### Definition_5_9_7 (from Items/Chap05) -/
universe u

set_option autoImplicit false

section

variable {F : Type u} [Group F]

/-!
Primary domain: small-cancellation relator conditions stated via group conjugacy.

Layer triage:
- `source-facing`: a relator set `R : Set F` satisfying the textbook condition that no relator
  `r ∈ R` is conjugate in `F` to its inverse.
- `core/canonical`: `IsConj` is mathlib's owner relation for group conjugacy, and
  `ConjClasses.mk_eq_mk_iff_isConj` is the canonical conjugacy-class reformulation.
- `bridge/view`: the set-level predicate `Set.SatisfiesConditionJ` packages the source condition on
  `R` without adding auxiliary witness data.

Domain sampling:
1. `IsConj` from `Mathlib.Algebra.Group.Conj` is the canonical owner relation for conjugacy.
2. `isConj_iff` is the canonical witness-level expansion of `IsConj`.
3. `ConjClasses.mk_eq_mk_iff_isConj` shows the equivalent conjugacy-class view, but the source
   sentence is most faithful when stated directly with `IsConj`.
4. Project files such as Proposition `2-5-7` and Proposition `2-5-14` already phrase
   “conjugate to the inverse” directly via `IsConj _ _⁻¹`, so the chapter's owner vocabulary is
   already aligned with `IsConj`.

Primitive vs. derived:
- primitive public data: the relator set `R`;
- derived API: the membership consequence `¬ IsConj r r⁻¹` for each `r ∈ R`.
-/

namespace Set

/-- Definition 5-9-7: Condition `J` for a relator set `R` says that no relator in `R` is
conjugate to its inverse. -/
def SatisfiesConditionJ (R : Set F) : Prop :=
  ∀ ⦃r : F⦄, r ∈ R → ¬ IsConj r r⁻¹

end Set

notation:55 "J[" R "]" => Set.SatisfiesConditionJ R

namespace Set.SatisfiesConditionJ

/-- Any relator in a set satisfying Condition `J` is not conjugate to its inverse. -/
theorem not_isConj_inv {R : Set F} (hR : J[R]) {r : F} (hr : r ∈ R) :
    ¬ IsConj r r⁻¹ :=
  hR hr

end Set.SatisfiesConditionJ

end
