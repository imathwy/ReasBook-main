import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_2_5_24 (from Items/Chap02) -/
-- Primary domain: one-relator groups and subgroup structure under group laws.
-- Layer triage:
-- `source-facing`: a subgroup of a one-relator group satisfying a nontrivial law, together with
-- the torsion-free versus torsion dichotomy for the ambient one-relator group.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator owner,
-- `Subgroup` for the subgroup owner, `SatisfiesNontrivialLaw` for the intrinsic law hypothesis on
-- the subgroup type,
-- `IsMulTorsionFree` and `IsOfFinOrder` for the torsion split, `IsCyclic` for cyclicity, and
-- `DihedralGroup 0` for the infinite dihedral group. The exceptional Baumslag-Solitar branch is
-- source-facing through the named owner `BS(1, n)`.
-- `bridge/view`: a chosen presentation equivalence
-- `PresentedGroup ({r} : Set (FreeGroup X)) ≃* G` transports the canonical owner-level theorem to
-- an arbitrary ambient group `G`; the Baumslag-Solitar exceptional family is compared by
-- isomorphism with the named owner `BS(1, n)`.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the chapter owner abstraction for one-relator
--    groups throughout nearby propositions `2-5-25`, `2-5-26`, and `2-5-29`.
-- 2. Definition `2-1-1` uses `PresentedGroup R ≃* G` directly as presentation data, so a chosen
--    equivalence is the right bridge layer, not the main owner-level statement.
-- 3. A law is intrinsically a property of a group, so the subgroup hypothesis is best expressed
--    on the subgroup type `H` itself rather than as extra structure on the ambient `Subgroup G`.
-- 4. Nearby Theorem `2-2-5` packages `BS(2, 3)` in the source-facing owner namespace
--    `BaumslagSolitar23`, so the standard family `BS(1, n)` should likewise be named at the owner
--    level rather than exposed only through a raw presentation expression.
-- 5. Nearby Proposition `2-5-25` already renders “locally cyclic” directly as
--    `∀ K : Subgroup H, K.FG → IsCyclic K`, so that owner-level form is reused here.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the subgroup `H`, the law satisfied by `H`, and
-- the source-facing Baumslag-Solitar owner `BS(1, n)`; the locally cyclic, cyclic, and
-- infinite-dihedral alternatives are derived conclusions.

section

namespace BaumslagSolitarOne

/-- The relator `x⁻¹ y x y^{-n}` presenting the Baumslag-Solitar group `BS(1, n)`. -/
abbrev relator (n : ℤ) : FreeGroup (Fin 2) :=
  (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
    (FreeGroup.of (1 : Fin 2) ^ (-n))

/-- The Baumslag-Solitar group `BS(1, n)` presented by `⟨x, y | x⁻¹ y x = y^n⟩`. -/
abbrev Group (n : ℤ) : Type := PresentedGroup ({relator n} : Set (FreeGroup (Fin 2)))

end BaumslagSolitarOne

notation "BS(1," n ")" => BaumslagSolitarOne.Group n

/-- A group satisfies a nontrivial law when some nontrivial word in finitely many variables
vanishes under every evaluation into that group. -/
def SatisfiesNontrivialLaw (G : Type v) [Group G] : Prop :=
  ∃ n : ℕ, ∃ w : FreeGroup (Fin n),
    w ≠ 1 ∧ ∀ f : Fin n → G, FreeGroup.lift f w = 1

namespace SatisfiesNontrivialLaw

/-- A multiplicative equivalence preserves the property of satisfying a nontrivial law. -/
theorem iff_mulEquiv {G : Type v} [Group G] {G' : Type u} [Group G'] (e : G ≃* G') :
    SatisfiesNontrivialLaw G ↔ SatisfiesNontrivialLaw G' := by
  constructor
  · rintro ⟨n, w, hw, hlaw⟩
    refine ⟨n, w, hw, ?_⟩
    intro f
    have h := hlaw (fun i ↦ e.symm (f i))
    let e' : G →* G' := e.toMonoidHom
    have hcomp :
        e'.comp (FreeGroup.lift (fun i ↦ e.symm (f i))) = FreeGroup.lift f := by
      ext i
      simp [e']
    have hw' :
        e ((FreeGroup.lift (fun i ↦ e.symm (f i))) w) = FreeGroup.lift f w := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun g : FreeGroup (Fin n) →* G' ↦ g w) hcomp
    have h' : e ((FreeGroup.lift (fun i ↦ e.symm (f i))) w) = 1 := by
      simpa using congrArg e h
    exact hw'.symm.trans h'
  · rintro ⟨n, w, hw, hlaw⟩
    refine ⟨n, w, hw, ?_⟩
    intro f
    have h := hlaw (fun i ↦ e (f i))
    let e' : G' →* G := e.symm.toMonoidHom
    have hcomp :
        e'.comp (FreeGroup.lift (fun i ↦ e (f i))) = FreeGroup.lift f := by
      ext i
      simp [e']
    have hw' :
        e.symm ((FreeGroup.lift (fun i ↦ e (f i))) w) = FreeGroup.lift f w := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun g : FreeGroup (Fin n) →* G ↦ g w) hcomp
    have h' : e.symm ((FreeGroup.lift (fun i ↦ e (f i))) w) = 1 := by
      simpa using congrArg e.symm h
    exact hw'.symm.trans h'

/-- A solvable group satisfies a nontrivial law. -/
theorem of_isSolvable (G : Type*) [Group G] [IsSolvable G] :
    SatisfiesNontrivialLaw G := sorry

end SatisfiesNontrivialLaw

variable {X : Type u} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

private abbrev subgroupComapMulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) (K : Subgroup B) : K.comap e.toMonoidHom ≃* K :=
  (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e K)).trans
    (e.symm.subgroupMap K).symm

private theorem locallyCyclic_of_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    (∀ K : Subgroup A, K.FG → IsCyclic K) →
      ∀ K : Subgroup B, K.FG → IsCyclic K := by
  intro h K hK
  let K' : Subgroup A := K.comap e.toMonoidHom
  let eK : K' ≃* K := subgroupComapMulEquiv e K
  have hK' : K'.FG := by
    have hKG : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
    let f : K →* K' := eK.symm.toMonoidHom
    have hf : Function.Surjective f := eK.symm.surjective
    have hK'G : Group.FG K' := Group.fg_of_surjective hf
    exact (Group.fg_iff_subgroup_fg K').1 hK'G
  exact (MulEquiv.isCyclic eK).1 (h K' hK')

private theorem locallyCyclic_iff_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    (∀ K : Subgroup A, K.FG → IsCyclic K) ↔
      ∀ K : Subgroup B, K.FG → IsCyclic K :=
  ⟨locallyCyclic_of_mulEquiv e, locallyCyclic_of_mulEquiv e.symm⟩

private theorem isMulTorsionFree_of_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    IsMulTorsionFree A → IsMulTorsionFree B := by
  intro hA
  letI : IsMulTorsionFree A := hA
  exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

private theorem isMulTorsionFree_iff_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    IsMulTorsionFree A ↔ IsMulTorsionFree B :=
  ⟨isMulTorsionFree_of_mulEquiv e, isMulTorsionFree_of_mulEquiv e.symm⟩

private theorem exists_nontrivial_isOfFinOrder_of_mulEquiv
    {A : Type u} [Group A] {B : Type v} [Group B] (e : A ≃* B) :
    (∃ a : A, a ≠ 1 ∧ IsOfFinOrder a) →
      ∃ b : B, b ≠ 1 ∧ IsOfFinOrder b := by
  rintro ⟨a, ha, hfin⟩
  refine ⟨e a, ?_, e.toMonoidHom.isOfFinOrder hfin⟩
  · intro h
    apply ha
    exact e.injective (by simpa using h)

private theorem exists_nontrivial_isOfFinOrder_iff_mulEquiv
    {A : Type u} [Group A] {B : Type v} [Group B] (e : A ≃* B) :
    (∃ a : A, a ≠ 1 ∧ IsOfFinOrder a) ↔
      ∃ b : B, b ≠ 1 ∧ IsOfFinOrder b :=
  ⟨exists_nontrivial_isOfFinOrder_of_mulEquiv e,
    exists_nontrivial_isOfFinOrder_of_mulEquiv e.symm⟩

-- Proof sketch: combine the classical subgroup theorem for one-relator groups with law
-- hypotheses. In the torsion-free case, the theorem gives the locally cyclic alternative or a
-- Baumslag-Solitar presentation `BS(1, n)` for `H`. In the presence of a nontrivial finite-order
-- element of the ambient one-relator group, the corresponding classification reduces the
-- possibilities for `H` to cyclic or infinite dihedral.
/-- Proposition 2-5-24: if `H` is a subgroup of the one-relator group
`PresentedGroup ({r} : Set (FreeGroup X))` and `H` satisfies a nontrivial law, then the
torsion-free case forces `H` to be locally cyclic or of the form `⟨x, y | x⁻¹ y x = y^n⟩`, while
the presence of torsion in the ambient group forces `H` to be cyclic or infinite dihedral. -/
theorem subgroup_with_nontrivial_law_classification_in_one_relator_group
    (H : Subgroup Q)
    (hHlaw : SatisfiesNontrivialLaw H) :
    (IsMulTorsionFree Q →
      (∀ K : Subgroup H, K.FG → IsCyclic K) ∨
        ∃ n : ℤ, Nonempty (H ≃* BS(1, n))) ∧
    ((∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g) →
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0)) := sorry

variable {G : Type v} [Group G]

-- Proof sketch: transport the owner-level statement across the chosen presentation equivalence
-- from Definition `2-1-1`. The law hypothesis, the torsion/torsion-free predicates, and the
-- exceptional isomorphism alternatives are invariant under multiplicative equivalence.
/-- Bridge form of Proposition 2-5-24 for an arbitrary ambient group given by a chosen one-relator
presentation. -/
theorem subgroup_with_nontrivial_law_classification_of_presentation
    (P : Q ≃* G) (H : Subgroup G)
    (hHlaw : SatisfiesNontrivialLaw H) :
    (IsMulTorsionFree G →
      (∀ K : Subgroup H, K.FG → IsCyclic K) ∨
        ∃ n : ℤ, Nonempty (H ≃* BS(1, n))) ∧
    ((∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) →
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0)) := by
  let H' : Subgroup Q := H.comap P.toMonoidHom
  let eH : H' ≃* H := subgroupComapMulEquiv P H
  have hHlaw' : SatisfiesNontrivialLaw H' :=
    (SatisfiesNontrivialLaw.iff_mulEquiv eH).2 hHlaw
  have hQ :=
    subgroup_with_nontrivial_law_classification_in_one_relator_group r H' hHlaw'
  refine ⟨?_, ?_⟩
  · intro htf
    have htf' : IsMulTorsionFree Q := (isMulTorsionFree_iff_mulEquiv P).2 htf
    rcases hQ.1 htf' with hloc | ⟨n, hBS⟩
    · exact Or.inl ((locallyCyclic_iff_mulEquiv eH).1 hloc)
    · rcases hBS with ⟨eBS⟩
      exact Or.inr ⟨n, ⟨eH.symm.trans eBS⟩⟩
  · intro htors
    have htors' : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g :=
      (exists_nontrivial_isOfFinOrder_iff_mulEquiv P).2 htors
    rcases hQ.2 htors' with hcyc | hD
    · exact Or.inl ((MulEquiv.isCyclic eH).1 hcyc)
    · rcases hD with ⟨eD⟩
      exact Or.inr ⟨eH.symm.trans eD⟩

end

/-! ### Proposition_2_5_25 (from Items/Chap02) -/
universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `PresentedGroup ({r} : Set (FreeGroup X))` together with an
-- abelian subgroup or, in the torsion clause, a solvable subgroup.
-- `core/canonical`: `PresentedGroup` for the ambient one-relator group, `Subgroup.FG` and
-- `IsCyclic` for local cyclicity, `Multiplicative (FreeAbelianGroup (Fin 2))` for the free
-- abelian rank-two alternative, the explicit predicate `IsMulCommutative H` for the subgroup
-- abelianity hypothesis, `IsSolvable` for the solvable-subgroup hypothesis, and `DihedralGroup 0`
-- for the infinite dihedral group.
-- `bridge/view`: the textbook phrase “locally cyclic” is rendered directly as “every finitely
-- generated subgroup is cyclic”, while “with torsion” is rendered by the existence of a
-- nontrivial finite-order element in the ambient one-relator quotient.
-- Domain sampling:
-- 1. Nearby Chapter II items already use `PresentedGroup ({r} : Set (FreeGroup X))` as the
--    canonical owner for one-relator groups.
-- 2. `Subgroup.FG` and `IsCyclic` are mathlib's standard finite-generation and cyclicity
--    predicates for subgroup types.
-- 3. Nearby Proposition `2-5-23` records the “free abelian of rank `2`” alternative directly as
--    `Nonempty (H ≃* Multiplicative (FreeAbelianGroup (Fin 2)))`, so that is the best candidate
--    owner abstraction here as well.
-- 4. `IsMulCommutative H` is mathlib's canonical owner predicate for saying that the subgroup
--    `H` is abelian without introducing subgroup-specific instance plumbing.
-- 5. Nearby Proposition `2-5-24` is the chapter's owner theorem for one-relator subgroups
--    satisfying a nontrivial law, so the torsion/solvable clause here should specialize that
--    theorem rather than restate a parallel classification owner.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the chosen subgroup `H`, and the abelian or
-- solvable hypotheses on `H`; the classification alternatives are derived conclusions, so no new
-- wrapper structure for one-relator groups or for the classification is introduced, and the
-- rank-two free-abelian branch is stated directly in the chapter's canonical owner form.

variable {X : Type u} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 2-5-25 (1): if `H` is an abelian subgroup of a one-relator group, then either
every finitely generated subgroup of `H` is cyclic and each nontrivial element of `H` is a `p`th
power for only finitely many primes `p`, or `H` is free abelian of rank `2`. -/
-- Proof sketch: apply the classical classification of abelian subgroups of one-relator groups.
-- The non-free-abelian case is precisely the locally cyclic alternative together with the finite
-- prime-root condition, while the remaining possibility is that the subgroup is the canonical
-- rank-two free abelian group from Proposition `2-5-23`.
theorem abelian_subgroup_of_one_relator_group_classification
    (H : Subgroup Q) (hab : IsMulCommutative H) :
    ((∀ K : Subgroup H, K.FG → IsCyclic K) ∧
        (∀ g : H, g ≠ 1 →
          Set.Finite {p : ℕ | Nat.Prime p ∧ ∃ x : H, x ^ p = g})) ∨
      Nonempty (H ≃* RankTwoFreeAbelian) := sorry

/-- Proposition 2-5-25 (2): if a one-relator group has torsion, then every solvable subgroup is
either cyclic or infinite dihedral. -/
-- Proof sketch: use the one-relator-with-torsion structure theorem for solvable subgroups. The
-- torsion hypothesis rules out the torsion-free branches that occur in the general classification,
-- leaving only the cyclic case and the subgroup type isomorphic to the infinite dihedral group.
theorem solvable_subgroup_of_one_relator_group_with_torsion_classification
    (htorsion : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g) (H : Subgroup Q)
    (hsolv : IsSolvable H) :
    IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0) := by
  let _ : IsSolvable H := hsolv
  exact
    (subgroup_with_nontrivial_law_classification_in_one_relator_group r H
      (SatisfiesNontrivialLaw.of_isSolvable H)).2 htorsion

end

/-! ### Proposition_2_5_26 (from Items/Chap02) -/
universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group with all of its subgroups, together with the trichotomy
-- that each subgroup either contains a free subgroup of rank `2`, or else lies in the solvable /
-- cyclic / infinite-dihedral exceptional families.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for one-relator groups,
-- `Subgroup` for subgroup owners, the direct existential
-- `∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))` for the rank-two free branch,
-- `IsSolvable`, `IsCyclic`, and `DihedralGroup 0` for the exceptional subgroup types.
-- `bridge/view`: no extra public bridge is needed; the source phrase “contains a free subgroup of
-- rank `2`” is already expressed directly at the subgroup owner level.
--
-- Domain sampling / owner abstraction:
-- 1. `PresentedGroup (Set.singleton r)` is the established project owner for one-relator
--    groups in this chapter.
-- 2. `FreeGroup (Fin 2)` is the canonical owner for the free group of rank `2`, while any
--    `FreeGroupBasis (Fin 2) K` is only bridge data exhibiting a concrete basis.
-- 3. `IsSolvable` and `IsCyclic` are mathlib's owner predicates for the solvable and cyclic
--    alternatives.
-- 4. `DihedralGroup 0` is mathlib's canonical infinite dihedral group.
--
-- Primitive vs. derived:
-- the public primitive data are the relator `r`, a subgroup `H` of the one-relator quotient, and
-- in the torsion case a nontrivial finite-order element of the ambient quotient. The subgroup
-- alternatives are derived conclusions, so the free rank-two branch is stated directly rather than
-- through a parallel predicate.

variable {X : Type u}
variable (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

/-- Proposition 2-5-26 (1): every subgroup of a one-relator group either contains a free subgroup
of rank `2` or is solvable. -/
-- Proof sketch: this is the standard subgroup theorem for one-relator groups. Apply the
-- Freiheitssatz / JSJ-style analysis of subgroups of one-relator groups: a non-solvable subgroup
-- must contain a nonabelian free subgroup, and in the one-relator setting this can be chosen of
-- rank `2`; otherwise the subgroup lies in the solvable exceptional case.
theorem subgroup_of_oneRelator_contains_rankTwoFree_or_isSolvable
    (H : Subgroup Q) :
    (∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))) ∨ IsSolvable H := sorry

/-- Proposition 2-5-26 (2): if a one-relator group has a nontrivial finite-order element, then
every subgroup either contains a free subgroup of rank `2`, is cyclic, or is infinite dihedral. -/
-- Proof sketch: first apply clause `(1)`. If `H` already contains a free subgroup of rank `2`,
-- there is nothing to prove. Otherwise `H` is solvable, and Proposition `2-5-25 (2)` classifies
-- solvable subgroups of a torsion one-relator group as cyclic or infinite dihedral.
theorem subgroup_of_torsion_oneRelator_contains_rankTwoFree_or_isCyclic_or_isInfiniteDihedral
    (htorsion : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g)
    (H : Subgroup Q) :
    (∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))) ∨
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0) := by
  rcases subgroup_of_oneRelator_contains_rankTwoFree_or_isSolvable r H with hfree | hsolv
  · exact Or.inl hfree
  · exact Or.inr <|
      solvable_subgroup_of_one_relator_group_with_torsion_classification r htorsion H hsolv

end

/-! ### Proposition_2_5_27 (from Items/Chap02) -/
universe u

noncomputable section

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X

variable (s : FreeGroup X) (n : ℕ)

local notation "q" => PresentedGroup.mk (Set.singleton (s ^ n))

-- Layer triage:
-- `source-facing`: a one-relator quotient `G = (X; s ^ n)` with `s` cyclically reduced, together
-- with two free-group elements `u` and `v` that have the same image in `G`, and a basis letter
-- `x` that occurs in `u` but not in `v`.
-- `core/canonical`: `PresentedGroup (Set.singleton (s ^ n))` for the one-relator quotient, `q`
-- for the quotient
-- map, `List.IsInfix` for consecutive subwords of the canonical reduced words,
-- `basisLetterOccurs basis` for generator occurrence, and `FreeGroup.norm` for reduced-word
-- length.
-- `bridge/view`: the source phrase “the letter `x` occurs in `u` but not in `v`” is read through
-- the chapter's owner-side predicate `basisLetterOccurs` specialized to the canonical basis
-- `basis`, with no auxiliary presentation wrapper.
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for the
--    one-relator group on generators `X`.
-- 2. `PresentedGroup.mk` is the canonical map identifying when two ambient free-group elements
--    represent the same element of the quotient.
-- 3. `List.IsInfix` from mathlib is the owner predicate for a consecutive subword of a reduced
--    word.
-- 4. `basisLetterOccurs basis` from Proposition `1-7-4` is the chapter's owner-side occurrence
--    predicate for generators in the concrete free-group model.
-- 5. `FreeGroup.IsCyclicallyReduced` is the chapter's owner predicate for the cyclically reduced
--    root hypothesis needed by the Newman--Greendlinger conclusion for the relator `s ^ n`.
-- 6. `FreeGroup.norm` is the canonical reduced-word length on `FreeGroup X`, so the textbook
--    quantity `|s|` is rendered directly as `FreeGroup.norm s`.
-- Primitive vs. derived:
-- the primitive source data are the root word `s`, the exponent `n`, the two representative words
-- `u` and `v`, the cyclically reduced root hypothesis on `s`, and the letter-occurrence
-- discrepancy for `x`. The quotient equality and the long common subword with the relator or its
-- inverse are the derived owner-level conclusions.

/-- Proposition 2-5-27: if `u` and `v` represent the same element of the one-relator group
`PresentedGroup (Set.singleton (s ^ n))`, where `n > 1` and the root `s` is cyclically
reduced, and some generator `x` occurs in `u` but not in `v`, then `u` contains a consecutive
subword that is also a consecutive subword of the relator `s ^ n` or of its inverse, and whose
length is greater than `(n - 1) * |s|`. -/
-- Proof sketch: from the equality of the images of `u` and `v` in the quotient by `s ^ n`, form
-- a van Kampen diagram for `u * v⁻¹` over the single relator `s ^ n`. The disappearance of the
-- letter `x` from `v` forces one 2-cell labeled by the relator to share a long boundary segment
-- with the `u`-side of the diagram. Greendlinger's lemma for the proper-power relator `s ^ n`
-- applies because the root `s` is cyclically reduced, and it yields a common part with `s ^ n`
-- or `(s ^ n)⁻¹` of length strictly greater than `(n - 1) * FreeGroup.norm s`.
theorem exists_long_common_part_with_relator_of_eq_in_power_relator_quotient
    (u v : FreeGroup X) {x : X} (hn : 1 < n)
    (hs : FreeGroup.IsCyclicallyReduced s.toWord)
    (heq : q u = q v)
    (hxu : basisLetterOccurs basis x u)
    (hxv : ¬ basisLetterOccurs basis x v) :
    ∃ part : List (X × Bool),
      part <:+: u.toWord ∧
        (part <:+: (s ^ n).toWord ∨ part <:+: ((s ^ n)⁻¹).toWord) ∧
          part.length > (n - 1) * s.norm := by
  sorry

end

/-! ### Proposition_2_5_28 (from Items/Chap02) -/
universe u v

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance : DecidableEq X := Classical.decEq X

open Subgroup (normalClosure)

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a chosen free basis `basis : FreeGroupBasis X F`, a cyclically reduced relator
-- `r : F`, and an element `s : F` whose canonical reduced word is a nonempty proper consecutive
-- subword of the reduced word of `r`.
-- `core/canonical`: the owner namespace `FreeGroupBasis`, together with
-- `FreeGroup.IsCyclicallyReduced`, `Subgroup.normalClosure`, the reduced-word map
-- `FreeGroup.toWord`, and `List.IsInfix`.
-- `bridge/view`: the textbook phrase “proper subword of `r`” is read directly through the owner
-- reduced-word map `(basis.repr ·).toWord`, so no parallel wrapper around reduced words or normal
-- closures is introduced.
--
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the canonical owner abstraction for a chosen basis of a free group,
--    and nearby Chapter II Magnus theorems with basis data already live in
--    `namespace FreeGroupBasis`.
-- 2. `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced reduced words.
-- 3. `Subgroup.normalClosure` is the canonical owner for the normal closure of a relator.
-- 4. `FreeGroup.toWord` is the owner reduced-word API on the canonical free-group model.
-- 5. `List.IsInfix` from mathlib is the canonical consecutive-subword predicate on reduced words.
--
-- Primitive vs. derived:
-- the primitive public data are the basis `basis`, the relator `r`, the candidate subword list
-- `part`, and the corresponding free-group element `s`; “proper subword of `r`” is expressed
-- directly through the owner reduced-word equality `(basis.repr s).toWord = part`,
-- `List.IsInfix`, and the strict length inequality, so no extra wrapper predicate is kept.

/-- Proposition 2-5-28: if `r` is cyclically reduced with respect to the chosen basis
`basis : FreeGroupBasis X F`, then any proper subword of `r` lying in its singleton normal
closure is trivial. -/
-- Proof sketch: transport the statement through `basis.repr : F ≃* FreeGroup X` to the canonical
-- free-group model on `X`. There, Magnus's subword theorem rules out every nonempty proper
-- consecutive subword of a cyclically reduced relator from lying in the normal closure of the
-- whole relator. Hence any such element in the normal closure must equal `1`.
theorem eq_one_of_mem_normalClosure_singleton_of_hasPart_of_isCyclicallyReduced
    (basis : FreeGroupBasis X F) {r s : F} {part : List (X × Bool)}
    (hr : FreeGroup.IsCyclicallyReduced (basis.repr r).toWord)
    (hs_word : (basis.repr s).toWord = part)
    (hpart : part <:+: (basis.repr r).toWord)
    (hpart_ne : part ≠ [])
    (hproper : part.length < (basis.repr r).toWord.length)
    (hs : s ∈ normalClosure ({r} : Set F)) :
    s = 1 := sorry

end FreeGroupBasis

end

/-! ### Proposition_2_5_29 (from Items/Chap02) -/
universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)` together with the hypothesis that the
-- quotient has a nontrivial finite-order element, and a chosen nontrivial element whose
-- centralizer is under study.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator quotient,
-- `Subgroup.centralizer {g}` for the centralizer of an element, and `IsCyclic` for the conclusion
-- that this centralizer is cyclic.
-- `bridge/view`: the textbook phrase “one-relator group with torsion” is rendered directly as the
-- existence of a nontrivial finite-order element in the canonical quotient; no extra wrapper
-- predicate for torsion one-relator groups is introduced.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the established project owner for one-relator
--    groups in this chapter.
-- 2. `Subgroup.centralizer {g}` is mathlib's canonical subgroup-valued owner for the centralizer
--    of an element.
-- 3. `IsOfFinOrder` is mathlib's canonical predicate for a finite-order element.
-- 4. `IsCyclic` is mathlib's canonical predicate for cyclicity of a group or subgroup.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the torsion witness `htorsion`, and the
-- nontrivial element `g`; the cyclicity of its centralizer is the derived conclusion.

variable {X : Type u}
variable (r : FreeGroup X)

local notation "rels" => (Set.singleton r : Set (FreeGroup X))
local notation "Q" => PresentedGroup rels

/-- Proposition 2-5-29: if a one-relator group has torsion, then the centralizer of every
nontrivial element is cyclic.
For the canonical quotient `Q := PresentedGroup ({r} : Set (FreeGroup X))`, torsion is expressed
by a nontrivial finite-order element of `Q`. -/
-- Proof sketch: this is Newman's centralizer theorem for one-relator groups with torsion.
-- Starting from a nontrivial finite-order element in the quotient, one uses the structure theory
-- of torsion one-relator groups to show that the centralizer of any nontrivial element is forced
-- into the unique maximal cyclic subgroup containing that element.
theorem centralizer_nontrivial_isCyclic_of_torsion_oneRelator
    (htorsion : ∃ t : Q, t ≠ 1 ∧ IsOfFinOrder t) (g : Q) (hg : g ≠ 1) :
    IsCyclic (Subgroup.centralizer {g}) := sorry

end

/-! ### Proposition_2_5_30 (from Items/Chap02) -/
universe u

/-- The distinguished generators `a` and `b` of the two-generator presentation in
Proposition `2-5-30`. -/
inductive LargePowerFreeSubgroupGenerator
  | a
  | b
  deriving DecidableEq

section

open LargePowerFreeSubgroupGenerator

variable (s : FreeGroup LargePowerFreeSubgroupGenerator) {m : ℕ}

local notation "G" => PresentedGroup (Set.singleton (s ^ m))
local notation "gen" => (PresentedGroup.of : LargePowerFreeSubgroupGenerator → G)

-- Layer triage:
-- `source-facing`: the two-generator one-relator group `G = (a, b; s ^ m)` with `1 < m`, together
-- with the hypothesis that the relator root `s` is not conjugate to any power of `a` or of `b`,
-- and the conclusion that the pair `a, b ^ n` is eventually a basis for the subgroup it
-- generates.
-- `core/canonical`: `PresentedGroup (Set.singleton (s ^ m))`
-- for the one-relator quotient, `IsConj` for conjugacy in the ambient free group, and
-- `IsFreeGroupBasis` for the textbook basis claim inside the generated subgroup.
-- `bridge/view`: the textbook generators `a` and `b` are represented by the constructors of
-- `LargePowerFreeSubgroupGenerator`, and their images in the one-relator quotient are the
-- canonical elements `gen .a` and `gen .b`.
-- Domain sampling:
-- 1. `PresentedGroup` is the canonical owner for one-relator groups in this chapter.
-- 2. Because this proposition works directly in that canonical quotient, the owner-side generator
--    map is `PresentedGroup.of` itself rather than the later bridge API
--    `GroupPresentation.generatorImage` for an arbitrary chosen presentation equivalence.
-- 3. `IsConj` is mathlib's owner relation for conjugacy in a group.
-- 4. `IsFreeGroupBasis` is the project's source-faithful basis predicate for a subset of a group.
-- Primitive vs. derived:
-- the primitive public data are the relator root `s`, the exponent `m`, and the non-conjugacy
-- hypotheses excluding powers of `a` and of `b`; the subgroup generated by the images of `a` and
-- `b ^ n` is derived canonically from those elements.

/-- Proposition 2-5-30: let `G = (a, b; s ^ m)` with `1 < m`, where `s` is not conjugate in the
free group on `{a, b}` to any power of `a` or of `b`. Then for all sufficiently large `n`, the
pair consisting of the image of `a` and the image of `b ^ n` is a free basis of the subgroup of
`G` that it generates. -/
-- Proof sketch: this is Magnus's large-power freeness theorem for one-relator groups with
-- torsion. The hypotheses exclude the exceptional cases where the relator is supported on a
-- conjugate of one generator, so high powers of the second generator avoid the defining relation.
-- For all sufficiently large `n`, the subgroup generated by the images of `a` and `b ^ n`
-- therefore embeds in the one-relator quotient as a free subgroup on those two generators, which
-- is exactly the `IsFreeGroupBasis` conclusion below.
theorem exists_threshold_a_and_bpow_isFreeGroupBasis
    (s : FreeGroup LargePowerFreeSubgroupGenerator) {m : ℕ} (hm : 1 < m)
    (hsa : ∀ k : ℤ, ¬ IsConj s (FreeGroup.of a ^ k))
    (hsb : ∀ k : ℤ, ¬ IsConj s (FreeGroup.of b ^ k)) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        let Y : Set G := {gen a, gen b ^ n}
        IsFreeGroupBasis {g : Subgroup.closure Y | (g : G) ∈ Y} := sorry

end

/-! ### Proposition_2_5_31 (from Items/Chap02) -/
universe u v w

-- Layer triage:
-- `source-facing`: a one-relator group on generators `X` with defining relator `r`, together with
-- the hypothesis that `X` has cardinality at least three.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator owner,
-- `Cardinal.mk X` for the cardinality lower bound, `Subgroup G` for subgroup data, and quotient
-- groups `S ⧸ N`.
-- `bridge/view`: a chosen equivalence `PresentedGroup (Set.singleton r) ≃* G` transports
-- the owner-level `SQ`-universality statement to an arbitrary ambient group `G`.
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for a group with
--    generators `X` and a single defining relator `r`.
-- 2. `Cardinal.mk X` is the universe-stable way to encode “at least three generators”.
-- 3. `Subgroup G` and `S ⧸ N` are the canonical mathlib owners for subgroups and quotient groups.
-- 4. Definition `2-1-1` uses `PresentedGroup R ≃* G` directly as presentation data, so a chosen
--    equivalence belongs at the bridge layer rather than as primitive owner data for this item.
-- Primitive vs. derived:
-- the primitive owner-level data are only the relator `r` and the lower bound on the cardinality
-- of the generator type; `SQ`-universality is the derived property of admitting every countable
-- group as a subquotient, and invariance under multiplicative equivalence supplies the separate
-- bridge theorem for arbitrary isomorphic ambient groups.

/-- A group is `SQ`-universal when every countable group embeds in a quotient of one of its
subgroups. -/
def IsSQUniversal (G : Type u) [Group G] : Prop :=
  ∀ {H : Type w} [Group H] [Countable H],
    ∃ (S : Subgroup G) (N : Subgroup S) (_ : N.Normal) (φ : H →* S ⧸ N),
      Function.Injective φ

namespace IsSQUniversal

/-- `SQ`-universality is invariant under multiplicative equivalence. -/
theorem of_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G')
    (hG : IsSQUniversal.{u, w} G) : IsSQUniversal.{v, w} G' := by
  intro H _ _
  obtain ⟨S, N, hN, φ, hφ⟩ :
      ∃ (S : Subgroup G) (N : Subgroup S) (_ : N.Normal) (φ : H →* S ⧸ N),
        Function.Injective φ := hG
  let S' : Subgroup G' := S.map (e : G →* G')
  let N' : Subgroup S' := N.map (e.subgroupMap S : S →* S')
  let _ : N'.Normal := hN.map (e.subgroupMap S : S →* S') (e.subgroupMap S).surjective
  let eQ : S ⧸ N ≃* S' ⧸ N' := QuotientGroup.congr N N' (e.subgroupMap S) rfl
  exact ⟨S', N', inferInstance, eQ.toMonoidHom.comp φ, eQ.injective.comp hφ⟩

/-- `SQ`-universality is preserved and reflected by multiplicative equivalence. -/
theorem iff_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G') :
    IsSQUniversal.{u, w} G ↔ IsSQUniversal.{v, w} G' :=
  ⟨of_mulEquiv e, of_mulEquiv e.symm⟩

end IsSQUniversal

section

variable {X : Type v} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

-- Proof sketch: apply the classical Magnus--Lyndon theorem that a one-relator group with at least
-- three generators is `SQ`-universal directly to the canonical owner `Q`.
/-- Proposition 2-5-31: a one-relator group on at least three generators is `SQ`-universal. -/
theorem isSQUniversal_of_three_generator_one_relator_group (hX : 3 ≤ Cardinal.mk X) :
    IsSQUniversal Q := sorry

-- Proof sketch: transport Proposition `2-5-31` across the chosen presentation equivalence from
-- Definition `2-1-1`. The owner-level theorem stays canonical, and this lemma is only the bridge
-- to an arbitrary isomorphic ambient group.
/-- Transport form of Proposition 2-5-31 for a chosen one-relator presentation of an ambient
group. -/
theorem isSQUniversal_of_three_generator_one_relator_presentation
    {G : Type u} [Group G] (P : Q ≃* G) (hX : 3 ≤ Cardinal.mk X) :
    IsSQUniversal G := by
  exact IsSQUniversal.of_mulEquiv P
    (isSQUniversal_of_three_generator_one_relator_group r hX)

end
