import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_9_1 (from Items/Chap01) -/
universe u

open scoped Classical

noncomputable section

set_option autoImplicit false

section

variable {G : Type u} [Group G]

namespace FreeGroup

variable {α : Type u}

/-- The canonical reduced-word length on `FreeGroup α`, with the implementation-only
`DecidableEq α` dependency kept internal. -/
noncomputable abbrev reducedWordLength (x : FreeGroup α) : ℕ :=
  let _ : DecidableEq α := Classical.decEq α
  norm x

end FreeGroup

-- Layer triage:
-- `source-facing`: a group `G` equipped with an abstract length function satisfying the textbook
-- axioms `A0` through `A4`.
-- `core/canonical`: `IsFreeGroup G`, `FreeGroup X`, `FreeGroup.norm`, and the canonical free-group
-- basis carried by the generators of `FreeGroup X`.
-- `bridge/view`: `FreeGroup.reducedWordLength`, together with an injective homomorphism
-- `G →* FreeGroup X` whose pullback of that canonical reduced-word length agrees with the given
-- abstract length function on `G`.
-- Domain sampling:
-- 1. `IsFreeGroup G` is mathlib's owner abstraction for the conclusion that `G` is a free group.
-- 2. `FreeGroup X` is the canonical target free group in which the source embedding lands.
-- 3. `FreeGroup.norm` is the canonical reduced-word length relative to the standard basis of
--    `FreeGroup X`, while `FreeGroup.reducedWordLength` is the thin owner-level bridge that hides
--    the proof-only `DecidableEq` implementation detail from public theorem surfaces.
-- 4. `IsFreeGroup.toFreeGroup` is the standard bridge from an abstract free group to its canonical
--    free-group model, so the embedding conclusion is stated directly into `FreeGroup X`.

/-- The overlap term `c(g,h)` attached to a natural-number-valued group length function. -/
def commonInitialLength (length : G → ℕ) (g h : G) : ℕ :=
  (length g + length h - length (g * h⁻¹)) / 2

scoped[AbstractLengthFunction] notation "c[" length "](" g ", " h ")" =>
  commonInitialLength length g h

open scoped AbstractLengthFunction

namespace AbstractLengthFunction

@[simp] theorem commonInitialLength_def (length : G → ℕ) (g h : G) :
    c[length](g, h) = (length g + length h - length (g * h⁻¹)) / 2 :=
  rfl

end AbstractLengthFunction

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A1` through `A4` from
Section `9`. The primitive data is only the function `G → ℕ`; the axioms are recorded as the
owner predicate on that function. -/
class IsCoreAbstractLengthFunction (length : G → ℕ) : Prop where
  /-- Axiom `A1`: only the identity has length `0`. -/
  eq_zero_iff (g : G) : length g = 0 ↔ g = 1
  /-- Axiom `A2`: length is invariant under inversion. -/
  map_inv (g : G) : length g⁻¹ = length g
  /-- Axiom `A3`: the overlap term is integral and is given by the standard half-difference
  formula. -/
  overlap_eq (g h : G) :
    length g + length h = length (g * h⁻¹) + 2 * c[length](g, h)
  /-- Axiom `A4`: the overlap function satisfies the isosceles condition. -/
  overlap_isosceles (g h k : G) :
    c[length](g, h) > c[length](g, k) →
      c[length](h, k) = c[length](g, k)

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A0` through `A4` from
Section `9`. This is the free-group specialization of
`IsCoreAbstractLengthFunction`, obtained by adjoining the square-growth axiom `A0`. -/
class IsAbstractLengthFunction (length : G → ℕ) : Prop
    extends IsCoreAbstractLengthFunction length where
  /-- Axiom `A0`: taking squares strictly increases the length of every nonidentity element. -/
  pow_two_strict (g : G) : g ≠ 1 → length g < length (g ^ 2)

/-- Proposition 1-9-1 (1): a group carrying an abstract length function satisfying axioms `A0`
through `A4` is a free group. -/
-- Proof sketch: first realize the abstract length function as the restriction of the canonical
-- reduced-word length along the embedding provided by the second clause. The image subgroup of a
-- free group is then free by Nielsen-Schreier, and the injective homomorphism identifies `G`
-- with that free subgroup.
theorem isFreeGroup_of_abstractLengthFunction
    (length : G → ℕ) [IsAbstractLengthFunction length] :
    IsFreeGroup G := sorry

private theorem abstractLengthFunction_eq_reducedWordLength_toFreeGroup
    (length : G → ℕ) [IsAbstractLengthFunction length] (g : G) :
    letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
    length g = FreeGroup.reducedWordLength ((IsFreeGroup.toFreeGroup G) g) := sorry

/- The private bridge above identifies a Section `9` abstract length function with the canonical
reduced-word length on the owner free-group model
`FreeGroup (IsFreeGroup.Generators G)`. -/
-- Proof sketch: combine Proposition `1-9-1` (1) with the realization argument from clause (2),
-- then transport the resulting norm-preserving embedding across the canonical equivalence
-- `IsFreeGroup.toFreeGroup G`.
/-- Proposition 1-9-1 (2): an abstract length function satisfying axioms `A0` through `A4`
comes from restricting the canonical reduced-word length on some free group `FreeGroup X` to an
injective copy of `G`. -/
-- Proof sketch: use the canonical norm-preserving comparison with `IsFreeGroup.toFreeGroup G`,
-- then forget that this owner free-group model was canonical and package it as the existential
-- source-facing embedding requested by the textbook statement.
theorem exists_freeGroup_embedding_preserving_abstractLengthFunction
    (length : G → ℕ) [IsAbstractLengthFunction length] :
    ∃ X : Type u, ∃ φ : G →* FreeGroup X, Function.Injective φ ∧
      ∀ g : G, length g = FreeGroup.reducedWordLength (φ g) := by
  letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
  refine ⟨IsFreeGroup.Generators G, (IsFreeGroup.toFreeGroup G).toMonoidHom,
    (IsFreeGroup.toFreeGroup G).injective, ?_⟩
  intro g
  simpa using abstractLengthFunction_eq_reducedWordLength_toFreeGroup length g

end

/-! ### Proposition_1_9_2 (from Items/Chap01) -/
universe u v w

noncomputable section

set_option autoImplicit false

open scoped AbstractLengthFunction

namespace Monoid.CoprodI

section

variable {ι : Type u} {factors : ι → Type v} [∀ i, Group (factors i)]

/-- The syllable length of an element of an indexed free product, computed from its canonical
reduced word. -/
noncomputable abbrev syllableLength (g : CoprodI factors) : ℕ :=
  let _ : DecidableEq ι := Classical.decEq ι
  let _ : ∀ i, DecidableEq (factors i) := fun i ↦ Classical.decEq (factors i)
  (Word.equiv g).toList.length

end

end Monoid.CoprodI

section

variable {G : Type u} [Group G]

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A1` through `A5` from
Section `9`. This is the free-product specialization of the shared `A1`-through-`A4` owner
predicate from Proposition `1-9-1`, obtained by adjoining the free-product rigidity axiom
`A5`. -/
class IsFreeProductLengthFunction (length : G → ℕ) : Prop
    extends IsCoreAbstractLengthFunction length where
  /-- Axiom `A5`: if the forward and backward overlap terms sum to more than the common length,
  then the two elements coincide. -/
  overlap_rigidity :
    ∀ g h : G,
      c[length](g, h) + c[length](g⁻¹, h⁻¹) > length g →
        length g = length h →
          g = h

/-- Proposition 1-9-2: a group carrying a Section `9` length function satisfying axioms `A1`
through `A5` admits an injective homomorphism into a free product whose canonical syllable-length
restricts to the given length function. -/
-- Layer triage:
-- `source-facing`: a group `G` equipped with a natural-number-valued length function `length`
-- satisfying the Section 9 owner predicate `IsFreeProductLengthFunction length`.
-- `core/canonical`: `Monoid.CoprodI` and the reduced-word normal form `Word.equiv`.
-- `bridge/view`: an injective homomorphism from `G` into a chosen indexed free product whose
-- pullback of the owner syllable-length `Monoid.CoprodI.syllableLength` equals `length`.
-- Domain sampling:
-- 1. `Monoid.CoprodI` is mathlib's owner abstraction for indexed free products of groups.
-- 2. `Word.equiv` gives the canonical reduced-word representative of each element.
-- 3. `IsCoreAbstractLengthFunction length` from Proposition `1-9-1` is the chapter owner
--    predicate for the shared axioms `A1` through `A4`, so this file specializes that owner by
--    adding only the new source-facing axiom `A5` instead of duplicating the common data.
-- 4. `Monoid.CoprodI.syllableLength` is the owner derived API for the reduced word's list length,
--    so the theorem should expose that canonical declaration rather than repeating
--    `(Word.equiv g).toList.length` at the theorem surface.
-- 5. An embedding of groups is stated canonically as an injective `MonoidHom`.
-- Proof sketch: build the Lyndon-Chiswell tree associated to `length`, identify the induced
-- action of `G` with the Bass-LinearRepresentations_Serre_1977 action of a suitable indexed free product of vertex
-- stabilizers, and use the normal form theorem for free products to obtain an injective
-- homomorphism whose reduced-word syllable-length pulls back to `length`.
theorem exists_freeProduct_embedding_preserving_length
    (length : G → ℕ) [IsFreeProductLengthFunction length] :
    ∃ (ι : Type v) (factors : ι → Type w),
      ∃ _ : ∀ i, Group (factors i),
        ∃ φ : G →* Monoid.CoprodI factors,
          Function.Injective φ ∧
            ∀ g : G, length g = Monoid.CoprodI.syllableLength (φ g) := sorry

end

/-! ### Proposition_1_9_3 (from Items/Chap01) -/
universe u

section

open AddSubgroup
open scoped IsMulCommutative

variable {G : Type u} [Group G]

private theorem isCyclic_of_isMulCommutative_of_centralizer_le [IsFreeGroup G]
    {A : Subgroup G} (hA : IsMulCommutative A)
    (hcentralizer : Subgroup.centralizer (A : Set G) ≤ A) : IsCyclic A := by
  letI : IsMulCommutative A := hA
  rcases A.bot_or_exists_ne_one with hA_bot | ⟨a, ha, ha1⟩
  · subst hA_bot
    infer_instance
  let N : Subgroup G := Subgroup.normalizer (Subgroup.zpowers a : Set G)
  have hza : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 ha
  have hA_le_N : A ≤ N := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxA : x ∈ A := hza hx
      have hbx : b * x = x * b := setLike_mul_comm hb hxA
      simpa [mul_assoc, hbx]
        using hx
    · intro hx
      have hxA : b * x * b⁻¹ ∈ A := hza hx
      have hxA' : x ∈ A := by
        have : b⁻¹ * (b * x * b⁻¹) * b ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hb) hxA) hb
        simpa [mul_assoc] using this
      have hbx : b * x = x * b := setLike_mul_comm hb hxA'
      simpa [mul_assoc, hbx]
        using hx
  have hNcyc : IsCyclic N := by
    simpa [N] using normalizer_zpowers_isCyclic a ha1
  letI : IsCyclic N := hNcyc
  have hN_le_centralizer : N ≤ Subgroup.centralizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hbx : (⟨b, hb⟩ : N) * ⟨x, hA_le_N hx⟩ = ⟨x, hA_le_N hx⟩ * ⟨b, hb⟩ := by
      simpa using mul_comm (⟨b, hb⟩ : N) ⟨x, hA_le_N hx⟩
    exact (congrArg Subtype.val hbx).symm
  have hN_le_A : N ≤ A := fun b hb ↦ hcentralizer (hN_le_centralizer hb)
  have hNA : N = A := le_antisymm hN_le_A hA_le_N
  exact hNA ▸ hNcyc

/-- Proposition 1-9-3: in the abstract-length-function setting of Section `9`, every maximal
abelian subgroup is additively isomorphic to an additive subgroup of `ℝ`. -/
-- Layer triage:
-- `source-facing`: a maximal abelian subgroup `A` of a group carrying the Section `9` owner
-- predicate `IsAbstractLengthFunction length`.
-- `core/canonical`: `IsAbstractLengthFunction length`, `IsMulCommutative A` together with the
-- self-centralizing condition `Subgroup.centralizer (A : Set G) ≤ A`, the freeness bridge
-- `isFreeGroup_of_abstractLengthFunction`, the free-group cyclicity theorem
-- `normalizer_zpowers_isCyclic`, and the canonical additive embedding `Int.castAddHom ℝ`.
-- `bridge/view`: express maximal abelianity through the centralizer owner API, pass from the
-- Section `9` owner abstraction to the induced free-group structure on `G`, identify `A` with the
-- cyclic normalizer of a nontrivial element it contains, and compare the resulting cyclic additive
-- group with the image of `ℤ` in `ℝ`.
-- Domain sampling:
-- 1. `IsAbstractLengthFunction length` is the chapter owner abstraction for Section `9`, so the
--    proposition should consume it directly rather than primitive ordered-group hypotheses on `A`.
-- 2. `Subgroup.centralizer` together with
--    `Subgroup.le_centralizer_iff_isMulCommutative` is mathlib's owner API for subgroup abelianity
--    and self-centralizing maximality, so the local wrapper is redundant.
-- 3. `isFreeGroup_of_abstractLengthFunction` is the canonical upgrade from the Section `9`
--    hypotheses to the ambient free-group owner abstraction.
-- 4. `normalizer_zpowers_isCyclic` is the earlier Chapter `1` cyclicity result that captures the
--    free-group structure behind maximal abelian subgroups.
-- 5. `Int.castAddHom ℝ` is the canonical additive embedding of `ℤ` into `ℝ`, and
--    `AddSubgroup.equivMapOfInjective` is the owner bridge from a subgroup to its image.
-- Proof sketch: Proposition `1-9-1` upgrades the ambient group to a free group. In a free group,
-- an abelian self-centralizing subgroup agrees with the cyclic normalizer of any nontrivial
-- element it contains, so it is cyclic. A nontrivial cyclic subgroup of a free group is torsion
-- free, hence canonically isomorphic to `ℤ`; composing that isomorphism with the image of
-- `Int.castAddHom ℝ` yields the required additive subgroup of `ℝ`.
theorem maximal_abelian_subgroup_addEquiv_addSubgroup_real
    (length : G → ℕ) [IsAbstractLengthFunction length]
    (A : Subgroup G) (hA : IsMulCommutative A)
    (hcentralizer : Subgroup.centralizer (A : Set G) ≤ A) :
    ∃ H : AddSubgroup ℝ, Nonempty (Additive A ≃+ H) := by
  letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
  by_cases hA_bot : A = ⊥
  · haveI : Subsingleton A := by
      rw [hA_bot]
      infer_instance
    let e0 : Additive A →+ (⊥ : AddSubgroup ℝ) :=
      { toFun := fun _ ↦ 0
        map_zero' := rfl
        map_add' := fun _ _ ↦ by simp }
    refine ⟨⊥, ⟨AddEquiv.ofBijective e0 ?_⟩⟩
    constructor
    · intro x y hxy
      exact Subsingleton.elim x y
    · intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ y
  · have hcyc : IsCyclic A := isCyclic_of_isMulCommutative_of_centralizer_le hA hcentralizer
    haveI : IsAddCyclic (Additive A) := isAddCyclic_additive_iff.2 hcyc
    letI : IsFreeGroup A := subgroupIsFreeOfIsFree A
    letI : IsMulTorsionFree A := by
      let e := IsFreeGroup.toFreeGroup A
      exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective
    obtain ⟨g, hg⟩ : ∃ g : Additive A, AddSubgroup.zmultiples g = ⊤ :=
      isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
    have hA_nontrivial : Nontrivial A := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hA_bot with ⟨a, ha1⟩
      exact ⟨⟨a, 1, ha1⟩⟩
    letI : Nontrivial A := hA_nontrivial
    have hg0 : g ≠ 0 := by
      intro hg0
      rw [hg0, AddSubgroup.zmultiples_zero_eq_bot] at hg
      exact bot_ne_top hg
    have hginj : Function.Injective (zmultiplesHom (Additive A) g) := by
      have hgfin : ¬ IsOfFinAddOrder g := by
        have hg1 : Multiplicative.ofAdd g ≠ 1 := by
          simpa using hg0
        rw [← isOfFinOrder_ofAdd_iff]
        exact not_isOfFinOrder_of_isMulTorsionFree hg1
      have hginj' : Function.Injective (fun n : ℤ ↦ n • g) :=
        injective_zsmul_iff_not_isOfFinAddOrder.mpr hgfin
      intro m n hmn
      exact hginj' hmn
    have hgsurj : Function.Surjective (zmultiplesHom (Additive A) g) := by
      refine AddMonoidHom.range_eq_top.mp ?_
      simpa using hg
    let eA : ℤ ≃+ Additive A := AddEquiv.ofBijective (zmultiplesHom (Additive A) g) ⟨hginj, hgsurj⟩
    let H : AddSubgroup ℝ := (⊤ : AddSubgroup ℤ).map (Int.castAddHom ℝ)
    let eZ : ℤ ≃+ H :=
      (AddSubgroup.topEquiv : (⊤ : AddSubgroup ℤ) ≃+ ℤ).symm.trans
        ((⊤ : AddSubgroup ℤ).equivMapOfInjective (Int.castAddHom ℝ) Int.cast_injective)
    exact ⟨H, ⟨eA.symm.trans eZ⟩⟩

end

/-! ### Proposition_1_9_4 (from Items/Chap01) -/
universe u

section

open scoped IsMulCommutative

variable {G : Type u} [Group G]

/-- Proposition 1-9-4: in a group carrying an abstract length function from Section `9`, every
subgroup generated by two elements is free or abelian. -/
-- Layer triage:
-- `source-facing`: two elements `a, b : G`; their generated subgroup is the canonical owner
-- `Subgroup.closure ({a, b} : Set G)`.
-- `core/canonical`: `IsAbstractLengthFunction`, `IsFreeGroup G`, and `subgroupIsFreeOfIsFree`.
-- `bridge/view`: Proposition `1-9-1` upgrades the abstract-length-function hypotheses to the
-- ambient owner abstraction `IsFreeGroup G`, after which Nielsen-Schreier gives freeness of the
-- generated subgroup. The source-facing disjunction is therefore a corollary of the canonical
-- free-subgroup conclusion, not a second owner abstraction.
-- Domain sampling:
-- 1. `IsAbstractLengthFunction L` is the Section `9` owner predicate on the primitive data
--    `L : G → ℕ`.
-- 2. `isFreeGroup_of_abstractLengthFunction` is the chapter owner theorem upgrading those
--    hypotheses to `IsFreeGroup G`.
-- 3. `Subgroup.closure ({a, b} : Set G)` is the canonical subgroup generated by `a` and `b`.
-- 4. `subgroupIsFreeOfIsFree` is the canonical owner theorem for subgroup freeness.
/- Canonical strengthening of Proposition `1-9-4`: the subgroup generated by `a` and `b` is
itself free. The textbook disjunction is obtained by taking the left branch. -/
theorem two_generated_subgroup_isFreeGroup_of_abstractLengthFunction
    (L : G → ℕ) [IsAbstractLengthFunction L] (a b : G) :
    IsFreeGroup (Subgroup.closure ({a, b} : Set G)) := by
  letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction L
  exact subgroupIsFreeOfIsFree (Subgroup.closure ({a, b} : Set G))

theorem two_generated_subgroup_isFreeGroup_or_abelian_of_abstractLengthFunction
    (L : G → ℕ) [IsAbstractLengthFunction L] (a b : G) :
    IsFreeGroup (Subgroup.closure ({a, b} : Set G)) ∨
      IsMulCommutative (Subgroup.closure ({a, b} : Set G)) := by
  exact Or.inl <|
    two_generated_subgroup_isFreeGroup_of_abstractLengthFunction L a b

end
