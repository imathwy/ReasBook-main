import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_13_1_18 (from Chap13) -/
noncomputable section

universe v

namespace Representation

open scoped Pointwise
open scoped Representation
open Subgroup.CyclicConjClasses

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance : Fintype (Subgroup.CyclicConjClasses G) := Fintype.ofFinite _
local instance : Nonempty (Subgroup.CyclicConjClasses G) := ⟨mk ⟨⊥, inferInstance⟩⟩

-- Proof sketch: conjugate subgroups give isomorphic transitive `G`-sets `G / H`, so their induced
-- trivial characters coincide.
/-- Helper for Exercise 13-13.1-18: conjugating a subgroup does not change its subgroup
permutation character. -/
private theorem subgroupPermutationCharacter_eq_conj
    (H : Subgroup G) (g : ConjAct G) :
    (ℓ_{g • H}^G : G → ℚ) = (ℓ_{H}^G : G → ℚ) := by
  classical
  symm
  ext x
  have hcard : Nat.card ↥(g • H) = Nat.card H := by
    rw [Subgroup.pointwise_smul_def]
    exact Nat.card_congr
      (((MulAut.conj (ConjAct.ofConjAct g)).subgroupMap H).symm.toEquiv)
  rw [Subgroup.characterRingOverFieldInduction_apply,
    Subgroup.characterRingOverFieldInduction_apply]
  rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction, hcard]
  let c : G := ConjAct.ofConjAct g
  let φ : G → ℚ := fun s ↦
    if hs : s⁻¹ * x * s ∈ H then
      (1 : H → ℚ) ⟨s⁻¹ * x * s, hs⟩
    else 0
  let ψ : G → ℚ := fun t ↦
    if ht : t⁻¹ * x * t ∈ g • H then
      (1 : (↥(g • H) → ℚ)) ⟨t⁻¹ * x * t, ht⟩
    else 0
  have hmem : ∀ s : G,
      ((s * c⁻¹)⁻¹ * x * (s * c⁻¹) ∈ g • H) ↔ s⁻¹ * x * s ∈ H := by
    intro s
    -- Rewrite membership in the conjugated subgroup back to membership in the original subgroup.
    rw [Subgroup.pointwise_smul_def]
    constructor
    · rintro ⟨h, hhH, hh⟩
      have hh' : c * h * c⁻¹ = c * (s⁻¹ * x * s) * c⁻¹ := by
        simpa [c, ConjAct.smul_def, mul_assoc] using hh
      have hmul := congrArg (fun y : G ↦ c⁻¹ * y * c) hh'
      have hEq : h = s⁻¹ * x * s := by
        simpa [mul_assoc] using hmul
      simpa [hEq] using hhH
    · intro hs
      refine ⟨s⁻¹ * x * s, hs, ?_⟩
      simp [c, ConjAct.smul_def, mul_assoc]
  have hphi : ∑ s : G, φ s = ∑ t : G, ψ t := by
    -- Reindex the defining sum by right multiplication with the conjugating element.
    exact
      Fintype.sum_bijective
        (fun s : G ↦ s * c⁻¹)
        (Group.mulRight_bijective c⁻¹)
        φ ψ
        (fun s ↦ by
          dsimp [φ, ψ]
          by_cases hs : s⁻¹ * x * s ∈ H
          · rw [if_pos hs, if_pos ((hmem s).2 hs)]
          · have ht : ¬ ((s * c⁻¹)⁻¹ * x * (s * c⁻¹) ∈ g • H) :=
              fun h ↦ hs ((hmem s).1 h)
            rw [if_neg hs, if_neg ht])
  simpa [φ, ψ] using congrArg ((Nat.card H : ℚ)⁻¹ * ·) hphi

/-- Conjugate cyclic subgroups define the same subgroup permutation character. -/
theorem cyclicSubgroupPermutationCharacter_eq_of_isConj
    {H K : { H : Subgroup G // IsCyclic H }}
    (hHK : H.1.IsConj K.1) :
    (ℓ_{H.1}^G : G → ℚ) = (ℓ_{K.1}^G : G → ℚ) := by
  -- Unpack the conjugacy witness and then apply the direct conjugation-invariance lemma above.
  rw [Subgroup.isConj_iff_orbitRel, MulAction.orbitRel_apply] at hHK
  rcases hHK with ⟨g, hg⟩
  calc
    (ℓ_{H.1}^G : G → ℚ) = (ℓ_{g • K.1}^G : G → ℚ) := by rw [← hg]
    _ = (ℓ_{K.1}^G : G → ℚ) := subgroupPermutationCharacter_eq_conj K.1 g

/-- Helper for Exercise 13-13.1-18: conjugate cyclic subgroups have the same cardinality. -/
private theorem natCard_eq_of_isConj
    {H K : { H : Subgroup G // IsCyclic H }}
    (hHK : H.1.IsConj K.1) :
    Nat.card H.1 = Nat.card K.1 := by
  -- Unpack the conjugacy witness and transport cardinality across the conjugating automorphism.
  rw [Subgroup.isConj_iff_orbitRel, MulAction.orbitRel_apply] at hHK
  rcases hHK with ⟨g, hg⟩
  have hcard : Nat.card (g • K.1 : Subgroup G) = Nat.card K.1 := by
    rw [Subgroup.pointwise_smul_def]
    exact Nat.card_congr
      (((MulAut.conj (ConjAct.ofConjAct g)).subgroupMap K.1).symm.toEquiv)
  simpa [hg] using hcard

/-- Helper for Exercise 13-13.1-18: the size of a cyclic subgroup class is well defined on the
quotient by conjugacy. -/
def cyclicConjClass_natCard (c : Subgroup.CyclicConjClasses G) : ℕ :=
  Quotient.lift
    (fun H : { H : Subgroup G // IsCyclic H } ↦ Nat.card H.1)
    (fun _ _ hHK ↦
      natCard_eq_of_isConj
        (Subgroup.CyclicConjClasses.mk_eq_mk_iff_isConj.1 (Quotient.sound hHK)))
    c

@[simp] theorem cyclicConjClass_natCard_mk
    (H : { H : Subgroup G // IsCyclic H }) :
    cyclicConjClass_natCard (mk H) = Nat.card H.1 := by
  rfl

/-- The subgroup permutation character attached to a conjugacy class of cyclic subgroups. -/
def cyclicConjClassPermutationCharacter (c : Subgroup.CyclicConjClasses G) :
    ℚ ⊗R[ℚ](G) :=
  Quotient.lift
    (fun H : { H : Subgroup G // IsCyclic H } ↦
      ⟨(ℓ_{H.1}^G : G → ℚ),
        mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
          ((ℓ_{H.1}^G : R[ℚ](G)).property)⟩)
    (fun _ _ hHK ↦
      Subtype.ext <|
        cyclicSubgroupPermutationCharacter_eq_of_isConj
          (Subgroup.CyclicConjClasses.mk_eq_mk_iff_isConj.1 (Quotient.sound hHK)))
    c

@[simp] theorem cyclicConjClassPermutationCharacter_mk
    (H : { H : Subgroup G // IsCyclic H }) :
    (cyclicConjClassPermutationCharacter (mk H) : G → ℚ) = (ℓ_{H.1}^G : G → ℚ) := by
  change
    ((⟨(ℓ_{H.1}^G : G → ℚ),
        mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
          ((ℓ_{H.1}^G : R[ℚ](G)).property)⟩ :
      ℚ ⊗R[ℚ](G)) : G → ℚ) = (ℓ_{H.1}^G : G → ℚ)
  rfl

/-- Helper for Exercise 13-13.1-18: the quotient-indexed cyclic permutation characters still span
the whole rational character ring. -/
private theorem top_le_span_cyclicConjClassPermutationCharacter :
    (⊤ : Submodule ℚ (ℚ ⊗R[ℚ](G))) ≤
      Submodule.span ℚ (Set.range cyclicConjClassPermutationCharacter) := by
  -- Start from the raw cyclic-subgroup spanning theorem and lift each raw generator to the
  -- quotient-indexed family via `cyclicConjClassPermutationCharacter (mk H)`.
  intro θ _
  let Sraw : Submodule ℚ (G → ℚ) :=
    Submodule.span ℚ
      (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ))
  let Squot : Submodule ℚ (ℚ ⊗R[ℚ](G)) :=
    Submodule.span ℚ (Set.range cyclicConjClassPermutationCharacter)
  have hraw : (θ : G → ℚ) ∈ Sraw := by
    change (θ : G → ℚ) ∈
      Submodule.span ℚ (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ))
    have hspan :
        ℚ ⊗R[ℚ](G) =
          Submodule.span ℚ
            (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ)) :=
      by simpa using
        (characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ
          (G := G))
    exact
      hspan ▸ θ.property
  have hlift :
      ∀ {f : G → ℚ}, f ∈ Sraw →
        ∃ η : ℚ ⊗R[ℚ](G), η ∈ Squot ∧ (η : G → ℚ) = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ hψ =>
        rcases hψ with ⟨H, rfl⟩
        let Hc : { H : Subgroup G // IsCyclic H } := ⟨H.1, (Subgroup.mem_cyclicSubgroups.1 H.2)⟩
        refine ⟨cyclicConjClassPermutationCharacter (mk Hc), ?_, ?_⟩
        · exact Submodule.subset_span ⟨mk Hc, rfl⟩
        · exact cyclicConjClassPermutationCharacter_mk Hc
    | zero =>
        exact ⟨0, Submodule.zero_mem Squot, rfl⟩
    | add f g _ _ hf hg =>
        rcases hf with ⟨ηf, hηf, rfl⟩
        rcases hg with ⟨ηg, hηg, rfl⟩
        exact ⟨ηf + ηg, Submodule.add_mem Squot hηf hηg, rfl⟩
    | smul a f _ hf =>
        rcases hf with ⟨η, hη, rfl⟩
        exact ⟨a • η, Submodule.smul_mem Squot a hη, rfl⟩
  rcases hlift hraw with ⟨η, hη, hη_eq⟩
  have : η = θ := Subtype.ext hη_eq
  simpa [Squot, this] using hη

/-- Helper for Exercise 13-13.1-18: a cyclic subgroup permutation character is nonzero at `x`
exactly when some conjugate of `x` lies in the subgroup. -/
theorem subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
    {K : Subgroup G} {x : G} :
    (ℓ_{K}^G : G → ℚ) x ≠ 0 ↔ ∃ s : G, s⁻¹ * x * s ∈ K := by
  classical
  let _ : DecidablePred fun s : G ↦ s⁻¹ * x * s ∈ K := Classical.decPred _
  let S : Finset G := Finset.univ.filter fun s : G ↦ s⁻¹ * x * s ∈ K
  have happly :
      (ℓ_{K}^G : G → ℚ) x =
        (Nat.card K : ℚ)⁻¹ * ∑ s : G, if s⁻¹ * x * s ∈ K then (1 : ℚ) else 0 := by
    -- Unfold induction from the trivial character and simplify the trivial summand.
    rw [Subgroup.characterRingOverFieldInduction_apply, Subgroup.inducedClassFunction]
    simp
  have hsum :
      ∑ s : G, (if s⁻¹ * x * s ∈ K then (1 : ℚ) else 0) = (S.card : ℚ) := by
    -- The induced sum is the cardinality of the witness set.
    simp [S]
  rw [happly]
  constructor
  · intro hne
    have hcard_ne : (S.card : ℚ) ≠ 0 := by
      intro hzero
      apply hne
      rw [hsum, hzero]
      simp
    have hcard_nat : S.card ≠ 0 := Nat.cast_ne_zero.mp hcard_ne
    rcases Finset.card_ne_zero.mp hcard_nat with ⟨s, hs⟩
    exact ⟨s, (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨s, hs⟩ hzero
    have hSin : s ∈ S := by
      simp [S, hs]
    have hcard_nat : S.card ≠ 0 := Finset.card_ne_zero.mpr ⟨s, hSin⟩
    have hcard_ne : (S.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard_nat
    have hinv : ((Nat.card K : ℚ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    apply hcard_ne
    exact (mul_eq_zero.mp (by rw [hsum] at hzero; exact hzero)).resolve_left hinv

/-- Helper for Exercise 13-13.1-18: if a cyclic subgroup sits inside a conjugate of another cyclic
subgroup and has at least the same cardinality, then the two cyclic subgroups are conjugate. -/
theorem isConj_of_le_smul_of_natCard_le
    {H K : { H : Subgroup G // IsCyclic H }}
    (g : ConjAct G)
    (hHK : H.1 ≤ (g • K.1 : Subgroup G))
    (hcard : Nat.card K.1 ≤ Nat.card H.1) :
    H.1.IsConj K.1 := by
  -- Compare the subgroup cardinalities inside the conjugate copy `g • K`.
  have hcard_smul : Nat.card (g • K.1 : Subgroup G) = Nat.card K.1 := by
    rw [Subgroup.pointwise_smul_def]
    exact Nat.card_congr
      (((MulAut.conj (ConjAct.ofConjAct g)).subgroupMap K.1).symm.toEquiv)
  have hle_card : Nat.card H.1 ≤ Nat.card (g • K.1 : Subgroup G) := by
    exact Nat.card_le_card_of_injective
      (fun h : H.1 ↦ ⟨h.1, hHK h.2⟩)
      (fun a b hab ↦ by simpa using congrArg Subtype.val hab)
  have hcard_eq : Nat.card H.1 = Nat.card (g • K.1 : Subgroup G) := by
    apply le_antisymm hle_card
    rw [hcard_smul]
    exact hcard
  have htop_card :
      Nat.card ((H.1).subgroupOf (g • K.1 : Subgroup G)) =
        Nat.card (g • K.1 : Subgroup G) := by
    -- Equality of cardinalities forces the subgroup-of inclusion to be all of `g • K`.
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hHK).toEquiv), hcard_eq]
  have htop : (H.1).subgroupOf (g • K.1 : Subgroup G) = ⊤ := by
    exact
      (Subgroup.card_eq_iff_eq_top ((H.1).subgroupOf (g • K.1 : Subgroup G))).mp
        htop_card
  have hEq : H.1 = (g • K.1 : Subgroup G) := by
    exact le_antisymm hHK (Subgroup.subgroupOf_eq_top.mp htop)
  -- Once `H = g • K`, the original conjugacy witness gives the required orbit relation.
  rw [hEq]
  rw [Subgroup.isConj_iff_orbitRel, MulAction.orbitRel_apply]
  exact ⟨g, rfl⟩

-- Proof sketch: if a finite `ℚ`-linear relation among the quotient-indexed family vanished, then
-- after pulling it back to cyclic subgroups and pairing with the subgroup sums from
-- Theorem `13-13.1-7`, all coefficients vanish.
/-- The quotient-indexed family of cyclic subgroup permutation characters
is linearly independent. -/
theorem linearIndependent_cyclicConjClassPermutationCharacter :
    LinearIndependent ℚ
      (cyclicConjClassPermutationCharacter : Subgroup.CyclicConjClasses G → ℚ ⊗R[ℚ](G)) := by
  classical
  -- Route correction: the stable proof here is source-faithful maximal-support elimination, not a
  -- separate finrank bridge through Chapter `12`.
  rw [linearIndependent_iff]
  intro l hl
  by_cases hzero : l = 0
  · exact hzero
  · exfalso
    have hsupp : l.support.Nonempty :=
      Finsupp.support_nonempty_iff.2 hzero
    obtain ⟨cmax, hcmax, hmax⟩ :=
      Finset.exists_max_image l.support cyclicConjClass_natCard hsupp
    rcases Quotient.exists_rep cmax with ⟨Hmax, rfl⟩
    rcases (Subgroup.isCyclic_iff_exists_zpowers_eq_top Hmax.1).1 Hmax.2 with ⟨x, hx⟩
    have hsum_zero :
        l.sum
            (fun c a ↦ a * ((cyclicConjClassPermutationCharacter c : G → ℚ) x)) =
          0 := by
      -- Evaluate the vanished relation at a generator of the maximal cyclic subgroup.
      have hsum :
          l.sum (fun c a ↦ a • cyclicConjClassPermutationCharacter c) = 0 := by
        simpa [Finsupp.linearCombination_apply] using hl
      have hfun :=
        congrArg (fun θ : ℚ ⊗R[ℚ](G) ↦ (θ : G → ℚ) x) hsum
      rw [Finsupp.sum] at hfun
      simpa [Pi.smul_apply] using hfun
    have hoff :
        ∀ c ∈ l.support,
          c ≠ mk Hmax →
            ((cyclicConjClassPermutationCharacter c : G → ℚ) x) = 0 := by
      intro c hc hne
      rcases Quotient.exists_rep c with ⟨K, rfl⟩
      by_contra hvalue
      have hvalueK : (ℓ_{K.1}^G : G → ℚ) x ≠ 0 := by
        simpa using hvalue
      rcases
          (subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
            (K := K.1) (x := x)).1 hvalueK with
        ⟨s, hs⟩
      have hx_smul : x ∈ (ConjAct.toConjAct s) • K.1 := by
        rw [Subgroup.pointwise_smul_def]
        refine ⟨s⁻¹ * x * s, hs, ?_⟩
        simp [ConjAct.toConjAct_smul, mul_assoc]
      have hle : Hmax.1 ≤ (ConjAct.toConjAct s) • K.1 := by
        rw [← hx]
        exact Subgroup.zpowers_le.2 hx_smul
      have hcard_le : Nat.card K.1 ≤ Nat.card Hmax.1 := by
        have := hmax (mk K) (by simpa using hc)
        simpa using this
      have hconj : Hmax.1.IsConj K.1 :=
        isConj_of_le_smul_of_natCard_le (g := ConjAct.toConjAct s) hle hcard_le
      exact hne (Subgroup.CyclicConjClasses.mk_eq_mk_iff_isConj.2 hconj).symm
    have hdiag :
        ((cyclicConjClassPermutationCharacter (mk Hmax) : G → ℚ) x) ≠ 0 := by
      have hx_mem : x ∈ Hmax.1 := by
        exact hx ▸ Subgroup.mem_zpowers x
      have hnonzero : (ℓ_{Hmax.1}^G : G → ℚ) x ≠ 0 := by
        exact
          (subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
            (K := Hmax.1) (x := x)).2
            ⟨1, by simpa using hx_mem⟩
      simpa using hnonzero
    have hsum_single :
        l.sum
            (fun c a ↦ a * ((cyclicConjClassPermutationCharacter c : G → ℚ) x)) =
          l (mk Hmax) *
            ((cyclicConjClassPermutationCharacter (mk Hmax) : G → ℚ) x) := by
      -- Maximality shows every other support term vanishes at the chosen generator.
      simp only [Finsupp.sum]
      exact
        Finset.sum_eq_single_of_mem
          (mk Hmax)
          (by simpa using hcmax)
          (fun c hc hne ↦ by simp [hoff c hc hne])
    have hcoeff_zero : l (mk Hmax) = 0 := by
      rw [hsum_single] at hsum_zero
      exact (mul_eq_zero.mp hsum_zero).resolve_right hdiag
    exact (Finsupp.mem_support_iff.1 (by simpa using hcmax)) hcoeff_zero

-- Proof sketch: Theorem `13-13.1-6` gives that the permutation characters `ℓ_C^G` induced from
-- cyclic subgroups span `ℚ⊗R[ℚ](G)`. Conjugate subgroups give the same permutation character, so
-- the cyclic-subgroup conjugacy classes form the canonical owner indexing set for the basis. The
-- direct maximal-support argument above gives linear independence, so `Module.Basis.mk` finishes
-- from the spanning theorem already proved.
/-- Exercise 13-13.1-18: the permutation characters `ℓ_C^G = Ind_C^G(1_C)`, indexed by the
conjugacy classes of cyclic subgroups `C ≤ G`, form a basis of `ℚ⊗R[ℚ](G)`. -/
noncomputable def rational_character_ring_basis_of_cyclic_subgroup_conjugacy_classes :
    Module.Basis (Subgroup.CyclicConjClasses G) ℚ (ℚ ⊗R[ℚ](G)) :=
  Module.Basis.mk
    linearIndependent_cyclicConjClassPermutationCharacter
    top_le_span_cyclicConjClassPermutationCharacter

@[simp] theorem rational_character_ring_basis_of_cyclic_subgroup_conjugacy_classes_apply
    (H : { H : Subgroup G // IsCyclic H }) :
    (rational_character_ring_basis_of_cyclic_subgroup_conjugacy_classes (mk H) :
      G → ℚ) = (ℓ_{H.1}^G : G → ℚ) := by
  -- `Module.Basis.mk` evaluates to the generating family by `Module.Basis.mk_apply`.
  simp [rational_character_ring_basis_of_cyclic_subgroup_conjugacy_classes]

-- Proof sketch: reindex the canonical basis on `Subgroup.CyclicConjClasses G` along the bijection
-- `i ↦ [C i]`.
/-- Exercise 13-13.1-18, representative-family bridge: if `C : ι → { H : Subgroup G // IsCyclic H }`
is a system of
representatives for the conjugacy classes of cyclic subgroups of `G`, then the permutation
characters `ℓ_{C_i}^G = Ind_{C_i}^G(1_{C_i})`, viewed in `ℚ⊗R[ℚ](G)`, form a basis of
`ℚ⊗R[ℚ](G)`. The representative condition is
encoded by requiring the induced map `i ↦ [C i]` to the canonical quotient
`Subgroup.CyclicConjClasses G` to be bijective. -/
noncomputable def rational_character_ring_basis_of_cyclic_subgroup_class_representatives
    {ι : Type v}
    (C : ι → { H : Subgroup G // IsCyclic H })
    (hC : Function.Bijective fun i ↦ mk (C i)) :
    Module.Basis ι ℚ (ℚ ⊗R[ℚ](G)) :=
  rational_character_ring_basis_of_cyclic_subgroup_conjugacy_classes.reindex
    (Equiv.ofBijective (fun i ↦ mk (C i)) hC).symm

@[simp] theorem rational_character_ring_basis_of_cyclic_subgroup_class_representatives_apply
    {ι : Type v}
    (C : ι → { H : Subgroup G // IsCyclic H })
    (hC : Function.Bijective fun i ↦ mk (C i))
    (i : ι) :
    (rational_character_ring_basis_of_cyclic_subgroup_class_representatives
        C hC i : G → ℚ) =
      (ℓ_{(C i).1}^G : G → ℚ) := by
  simp [rational_character_ring_basis_of_cyclic_subgroup_class_representatives]

end

end Representation

/-! ### Remark_13_13_1_10 (from Chap13) -/
universe u

open Representation

open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]

/- Remark 13-13.1-10: LinearRepresentations_Serre_1977 applies Theorem `13-13.1-6` to a finite Galois group `G = Gal(F / E)`
and a character `χ` realizable over `ℚ` to express the corresponding Artin `L`-function as a
product of fractional powers of Dedekind zeta functions of the fixed fields attached to cyclic
subgroups. In the current API this remark is a direct recall of the source-facing bridge theorem,
rather than a separate string-valued wrapper. -/
recall characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ

end
