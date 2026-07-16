import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleEquivTransport
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleCompleteness
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SymmetricAugmentation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.CharThreeRegularCount

/-!
# Completeness of the four irreducible `S₄`-models in characteristic `3` (support 18.5.2)

In the modular characteristic-`3` branch of Exercise 18.5.2, `k[S₄]` is not semisimple, so the
semisimple completeness criterion (sum of square degrees `= |G|`) is unavailable.  Instead we count
simple modules through Brauer's theorem: over an algebraically closed field of characteristic `p`
the number of simple `k[G]`-modules equals the number of `p`-regular conjugacy classes
(`Corollary_18_18_2_5`).  For `G = S₄`, `p = 3` this number is `4`
(`nat_card_pRegularConjClass_s4_three`): the four cycle types of order prime to `3`
(`1`, transpositions, double transpositions, `4`-cycles).

We then show the four explicit models — trivial, sign, the degree-`3` standard (augmentation) module,
and `sgn ⊗ std` — are simple (the degree-`3` cases use the modular-robust augmentation irreducibility
`permutationAugmentationRepresentation_isIrreducible_of_perm_overField`) and pairwise nonisomorphic
(transposition character values, char-uniform).  Four pairwise-nonisomorphic simples in a category
with exactly four simple isomorphism classes form a complete family.
-/

attribute [-instance] Field.henselian

noncomputable section

open CategoryTheory
open Representation

namespace Representation

universe u uA uB

/-! ### `p`-regular conjugacy classes transport along a group isomorphism -/

theorem isConj_orderOf_eq {G : Type*} [Group G] {y z : G} (h : IsConj y z) :
    orderOf y = orderOf z := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [← MulEquiv.orderOf_eq (MulAut.conj c) y]; rfl

theorem pRegular_carrier_map {A : Type uA} {B : Type uB} [Group A] [Group B]
    (ψ : A ≃* B) (p : ℕ) (c : ConjClasses A) (hc : ∀ x ∈ c.carrier, IsPRegular p x) :
    ∀ y ∈ (ConjClasses.map ψ.toMonoidHom c).carrier, IsPRegular p y := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
  intro y hy
  rw [show ConjClasses.map ψ.toMonoidHom (ConjClasses.mk a) = ConjClasses.mk (ψ a) from rfl,
    ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hy
  have ha : IsPRegular p a := hc a ConjClasses.mem_carrier_mk
  have horder : orderOf y = orderOf a :=
    (isConj_orderOf_eq hy).trans (MulEquiv.orderOf_eq ψ a)
  unfold IsPRegular at ha ⊢; rwa [horder]

/-- The number of `p`-regular conjugacy classes is invariant under a group isomorphism. -/
theorem nat_card_pRegularConjClass_congr {G : Type uA} {H : Type uB} [Group G] [Group H]
    (φ : G ≃* H) (p : ℕ) :
    Nat.card (Representation.PRegularConjClass G p)
      = Nat.card (Representation.PRegularConjClass H p) := by
  refine Nat.card_congr ?_
  refine {
    toFun := fun c => ⟨ConjClasses.map φ.toMonoidHom c.1, pRegular_carrier_map φ p c.1 c.2⟩
    invFun := fun c => ⟨ConjClasses.map φ.symm.toMonoidHom c.1, pRegular_carrier_map φ.symm p c.1 c.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨c, hc⟩
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    apply Subtype.ext
    show ConjClasses.map φ.symm.toMonoidHom (ConjClasses.map φ.toMonoidHom (ConjClasses.mk a))
      = ConjClasses.mk a
    rw [show ConjClasses.map φ.toMonoidHom (ConjClasses.mk a) = ConjClasses.mk (φ a) from rfl,
      show ConjClasses.map φ.symm.toMonoidHom (ConjClasses.mk (φ a))
        = ConjClasses.mk (φ.symm (φ a)) from rfl, MulEquiv.symm_apply_apply]
  · rintro ⟨c, hc⟩
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    apply Subtype.ext
    show ConjClasses.map φ.toMonoidHom (ConjClasses.map φ.symm.toMonoidHom (ConjClasses.mk a))
      = ConjClasses.mk a
    rw [show ConjClasses.map φ.symm.toMonoidHom (ConjClasses.mk a)
          = ConjClasses.mk (φ.symm a) from rfl,
      show ConjClasses.map φ.toMonoidHom (ConjClasses.mk (φ.symm a))
        = ConjClasses.mk (φ (φ.symm a)) from rfl, MulEquiv.apply_symm_apply]

/-! ### Existence of a complete pairwise-nonisomorphic simple family (characteristic free) -/

/-- Every finite group over a field admits a complete pairwise nonisomorphic family of simple
finite-dimensional representations (no semisimplicity / order-invertibility hypothesis).  Reproved
locally to keep this file independent of Exercise 18.3.3. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_modular
    {F : Type u} [Field F] {H : Type u} [Group H] [Finite H] :
    ∃ (κ : Type (u + 1)) (π : κ → FDRep F H),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F H // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by rcases hab with ⟨e⟩; exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩; rcases hbc with ⟨ebc⟩; exact ⟨eab.trans ebc⟩⟩ }
  let κ : Type (u + 1) := Quotient r
  let π : κ → FDRep F H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : κ) = (⟦Quotient.out q'⟧ : κ) := by
      apply Quotient.sound; exact ⟨e⟩
    apply hqq'
    calc q = (⟦Quotient.out q⟧ : κ) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : κ) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨fun q => (Quotient.out q).2, ?_⟩
    intro τ hτ
    refine ⟨⟦⟨τ, hτ⟩⟧, ?_⟩
    have hq : Nonempty (((Quotient.out (⟦⟨τ, hτ⟩⟧ : κ)).1) ≅ τ) :=
      Quotient.exact (Quotient.out_eq (⟦⟨τ, hτ⟩⟧ : κ))
    rcases hq with ⟨e⟩
    exact ⟨e.symm⟩
  exact ⟨κ, π, hπ_pairwise, hπ_complete⟩

/-! ### Completeness via the Brauer count -/

/-- A pairwise-nonisomorphic family of `n` simple finite-dimensional `k[G]`-representations is
complete as soon as `n` equals the number of `p`-regular conjugacy classes of `G` (over an
algebraically closed field of characteristic `p`).  This is the modular replacement for the
semisimple "sum of square degrees `= |G|`" completeness criterion. -/
theorem isCompleteIrreducibleFamily_of_card_eq_pRegular
    {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    {G : Type u} [Group G] [Finite G] {n : ℕ} (D : Fin n → FDRep k G)
    (hsimple : ∀ i, Simple (D i)) (hpair : PairwiseNonisomorphic D)
    (hcard : Nat.card (Representation.PRegularConjClass G p) = n) :
    IsCompleteIrreducibleFamily D := by
  classical
  -- a complete pairwise-nonisomorphic simple family `E`
  obtain ⟨κ, E, hE_pair, hE_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_modular (F := k) (H := G)
  -- the Brauer count: `#κ = #(p-regular classes) = n`
  have hκcard : Nat.card κ = n := by
    rw [card_eq_card_pRegularConjugacyClasses_of_complete_simple_family (p := p) E hE_pair
      hE_complete, hcard]
  -- `κ` is finite of cardinality `n`
  letI : Fintype (Representation.PRegularConjClass G p) :=
    Fintype.ofFinite (Representation.PRegularConjClass G p)
  let b := irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
    (p := p) (k := k) (K := k) (primeToPRoots p k).subtype
    (Subgroup.subtype_injective (primeToPRoots p k)) E hE_pair hE_complete
  letI : Module.Finite k (Representation.PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (Representation.PRegularConjClass G p))
  letI : Finite κ := Module.Finite.finite_basis b
  letI : Fintype κ := Fintype.ofFinite κ
  -- each `D i` is isomorphic to some `E (f i)`
  have hex : ∀ i, ∃ j, Nonempty (D i ≅ E j) := fun i =>
    hE_complete.exists_iso (D i) (hsimple i)
  choose f hf using hex
  -- `f` is injective (both families pairwise nonisomorphic)
  have hf_inj : Function.Injective f := by
    intro i i' hii
    by_contra hne
    apply hpair hne
    rcases hf i with ⟨ei⟩
    rcases hf i' with ⟨ei'⟩
    exact ⟨ei.trans (hii ▸ ei'.symm)⟩
  -- `f : Fin n → κ` injective between finite types of equal cardinality, hence surjective
  have hcardκ : Fintype.card κ = Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hκcard]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcardκ.symm⟩
  refine ⟨hsimple, ?_⟩
  intro τ hτ
  obtain ⟨j, ⟨eτ⟩⟩ := hE_complete.exists_iso τ hτ
  obtain ⟨i, rfl⟩ := hf_bij.surjective j
  rcases hf i with ⟨ei⟩
  exact ⟨i, ⟨eτ.trans ei.symm⟩⟩

/-! ### The four explicit characteristic-`3` models form a complete family -/

section
local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The index map selecting the four characteristic-`3` slots of `s4_explicit_family`:
`0 ↦ 1` (trivial), `1 ↦ sgn`, `2 ↦ std`, `3 ↦ sgn ⊗ std`.  The degree-`2` quotient model (slot `2`
of the five) is omitted (it is reducible in characteristic `3`). -/
def charThreeSlot : Fin 4 → Fin 5 := ![0, 1, 3, 4]

theorem charThreeSlot_injective : Function.Injective charThreeSlot := by
  decide

/-- The four explicit `S₄`-models surviving in characteristic `3`, as an `ULift`-lifted family. -/
def s4_char_three_family (k : Type u) [Field k] : Fin 4 → FDRep k (ULift.{u} S4) :=
  fun i => s4_explicit_family k (charThreeSlot i)

theorem s4_char_three_family_simple [Invertible (Nat.card (Fin 4) : k)]
    (i : Fin 4) : Simple (s4_char_three_family k i) := by
  -- the standard module is irreducible by the modular-robust augmentation criterion
  haveI hstd : (s4_standard_augmentation_representation k).IsIrreducible :=
    permutationAugmentationRepresentation_isIrreducible_of_perm_overField
      (k := k) (X := Fin 4)
  fin_cases i <;>
    simp only [s4_char_three_family, charThreeSlot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    dsimp [s4_explicit_family]
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_trivial_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_sign_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2 hstd)
  · refine @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2 ?_)
    letI : (s4_standard_augmentation_representation k).IsIrreducible := hstd
    simpa [s4_sign_standard_tensor_representation, s4_sign_representation] using
      (tprod_unitCharacter_preserves_isIrreducible_overField
        (β := s4_sign_character k) (σ := s4_standard_augmentation_representation k))

theorem s4_char_three_family_pairwiseNonisomorphic
    [Invertible (Nat.card (Fin 4) : k)] (h2 : (2 : k) ≠ 0) :
    PairwiseNonisomorphic (s4_char_three_family k) := by
  intro i j hij
  exact s4_explicit_family_pairwiseNonisomorphic h2 (charThreeSlot_injective.ne hij)

/-- **Completeness of the four explicit `S₄`-models in characteristic `3`.** -/
theorem s4_char_three_family_isCompleteIrreducibleFamily
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) = 0) :
    IsCompleteIrreducibleFamily (s4_char_three_family k) := by
  haveI : CharP k (ringChar k) := ringChar.charP k
  have hrc3 : ringChar k = 3 := by
    have hdvd : ringChar k ∣ 3 := ringChar.dvd (by exact_mod_cast h3)
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  haveI : CharP k 3 := hrc3 ▸ (ringChar.charP k)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Invertible (Nat.card (Fin 4) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin],
      show ((4 : ℕ) : k) = (2 : k) * (2 : k) by push_cast; ring]
    exact mul_ne_zero h2 h2)
  refine isCompleteIrreducibleFamily_of_card_eq_pRegular (p := 3)
    (s4_char_three_family k)
    (fun i => s4_char_three_family_simple i)
    (s4_char_three_family_pairwiseNonisomorphic h2) ?_
  -- count: `#(3-regular classes of ULift S₄) = #(3-regular classes of S₄) = 4`
  rw [nat_card_pRegularConjClass_congr (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4) 3]
  exact nat_card_pRegularConjClass_s4_three

end

end Representation
