import Mathlib
import Serre.Chap07.Exercise_7_7_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation

local notation "A4" => alternatingGroup (Fin 4)
local notation "S4" => Equiv.Perm (Fin 4)

local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

namespace Representation

/-- Helper for Exercise 16-16.4-4: an irreducible finite-dimensional complex representation of a
finite group has defect zero at `p` when the `p`-part of the group order divides its degree. -/
class HasDefectZero {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [FiniteDimensional k V] (p : ℕ) [Finite G] [Fact p.Prime] :
    Prop where
  isIrreducible : ρ.IsIrreducible
  dvd_finrank : p ^ Nat.factorization (Nat.card G) p ∣ Module.finrank k ρ.asModule

end Representation

/-- Helper for Exercise 16-16.4-4: an irreducible complex representation has a nontrivial
underlying vector space. -/
lemma nontrivial_of_isIrreducible
    {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] : Nontrivial V := by
  -- If the space were trivial, the zero and whole subrepresentations would coincide.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Exercise 16-16.4-4: a doubly pretransitive finite action has irreducible complex
augmentation representation. -/
lemma permutation_augmentation_isIrreducible_of_two_pretransitive
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [Nontrivial X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2) :
    (Representation.permutationAugmentationRepresentation ℂ G X).IsIrreducible := by
  -- Chapter 7 turns double transitivity into the character criterion for augmentation
  -- irreducibility.
  letI : MulAction.IsMultiplyPretransitive G X 2 := h2
  letI : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive (G := G) (α := X)
  have hpair :=
    (Representation.isTwoPretransitive_iff_pairActionHasDiagonalOrbits
      (G := G) (X := X)).mp h2
  have hsq :=
    (Representation.pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two
      (G := G) (X := X)).mp hpair
  exact
    (Representation.character_square_pairing_eq_two_iff_augmentation_isIrreducible
      (G := G) (X := X)).mp hsq

/-- Helper for Exercise 16-16.4-4: the augmentation constituent of the natural action on four
letters has degree `3`. -/
lemma fin_four_permutation_augmentation_finrank_three
    {G : Type} [Group G] [MulAction G (Fin 4)] :
    Module.finrank ℂ
      (Representation.permutationAugmentationSubrepresentation ℂ G (Fin 4)).toSubmodule = 3 := by
  letI : Invertible (Nat.card (Fin 4) : ℂ) := invertibleOfNonzero (by norm_num)
  -- Evaluate the permutation/augmentation character splitting at the identity.
  have hχ :=
    Representation.permutation_character_eq_trivial_add_augmentation
      (k := ℂ) (G := G) (X := Fin 4)
  have h1 : (4 : ℂ) = 1 + Representation.permutationAugmentationCharacter ℂ G (Fin 4) 1 := by
    simpa [Representation.char_one] using congrFun hχ 1
  have h2 := congrArg (fun z : ℂ => z - 1) h1
  norm_num at h2
  have hchar :
      (Representation.permutationAugmentationRepresentation ℂ G (Fin 4)).character 1 = 3 := by
    simpa [Representation.permutationAugmentationCharacter] using h2.symm
  -- The identity character value is the dimension of the representation.
  have hone :=
    Representation.char_one
      (ρ := Representation.permutationAugmentationRepresentation ℂ G (Fin 4))
  rw [hchar] at hone
  exact_mod_cast hone.symm

/-- Helper for Exercise 16-16.4-4: an irreducible finite-dimensional complex representation has
degree at most `√|G|`. -/
lemma fdrep_finrank_sq_le_card
    {G : Type} [Group G] [Finite G] (V : FDRep ℂ G)
    (hirr : Representation.IsIrreducible V.ρ) :
    Module.finrank ℂ V.V ^ 2 ≤ Nat.card G := by
  -- Turn the character orthogonality relation into a sum of nonnegative norm squares.
  letI : Representation.IsIrreducible V.ρ := hirr
  letI : CategoryTheory.Simple V := FDRep.simple_of_isIrreducible V
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  have hsum : ∑ g : G, Complex.normSq (V.character g) = Nat.card G := by
    have hterm :
        Finset.univ.sum (fun g : G ↦ (Complex.normSq (V.character g) : ℂ)) =
          Finset.univ.sum (fun g : G ↦ V.character g * V.character g⁻¹) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      calc
        (Complex.normSq (V.character g) : ℂ) = V.character g * star (V.character g) := by
          simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj' (V.character g)).symm
        _ = V.character g * V.character g⁻¹ := by
          have hstar : star (V.character g) = V.character g⁻¹ := by
            simpa using
              (Representation.char_inv_eq_star_of_isOfFinOrder
                (ρ := V.ρ) g (isOfFinOrder_of_finite g)).symm
          rw [hstar]
    apply Complex.ofReal_injective
    calc
      ((∑ g : G, Complex.normSq (V.character g) : ℝ) : ℂ)
          = ∑ g : G, V.character g * V.character g⁻¹ := by
              simpa using hterm
      _ = Nat.card G := (FDRep.simple_iff_char_is_norm_one (k := ℂ) V).mp inferInstance
  have hle_real : (Module.finrank ℂ V.V ^ 2 : ℝ) ≤ Nat.card G := by
    have hnonneg :
        0 ≤ (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) := by
      exact Finset.sum_nonneg fun g _ ↦ Complex.normSq_nonneg (V.character g)
    have hsplit :=
      Finset.sum_erase_add (a := (1 : G)) (s := Finset.univ)
        (f := fun g : G ↦ Complex.normSq (V.character g)) (by simp)
    have hone : V.character 1 = Module.finrank ℂ V.V := by
      exact Representation.char_one (ρ := V.ρ)
    have hchar_one : Complex.normSq (V.character 1) = Module.finrank ℂ V.V ^ 2 := by
      rw [hone, Complex.normSq_eq_norm_sq]
      norm_num
    calc
      (Module.finrank ℂ V.V ^ 2 : ℝ) = Complex.normSq (V.character 1) := by
        symm
        exact hchar_one
      _ ≤ Complex.normSq (V.character 1) +
            (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) := by
          exact le_add_of_nonneg_right hnonneg
      _ = ∑ g : G, Complex.normSq (V.character g) := by
          calc
            Complex.normSq (V.character 1) +
                (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) =
              (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) +
                Complex.normSq (V.character 1) := by
                  rw [add_comm]
            _ = ∑ g : G, Complex.normSq (V.character g) := hsplit
      _ = Nat.card G := hsum
  exact_mod_cast hle_real

/- Domain-style sampling for this item:
* primary domain: defect-zero finite-dimensional complex representations of the finite groups
  `A₄` and `S₄`;
* relevant owner declarations inspected in this domain:
  `Representation.HasDefectZero`,
  `StableLattice.reduction_irreducible_of_defect_zero`,
  `character_eq_zero_of_not_isPRegular_of_defect_zero`,
  `simple_finiteRep_projective_defect_zero_and_cartan_tfae`;
* best owner abstraction: the bundled owner `FDRep ℂ G` together with the chapter-level owner
  predicate `HasDefectZero (V.ρ) p` on the underlying irreducible representation of `V`;
* source/core/bridge triage:
  source-facing: these four existence and nonexistence assertions for the concrete groups `A₄`
    and `S₄`;
  core/canonical: `FDRep ℂ G`, `Simple V`, and `Representation.HasDefectZero`;
  bridge/view: the passage from a bundled `FDRep` object `V` to its underlying representation
    `V.ρ`.

Primitive data vs derived API:
* primitive data: an actual finite-dimensional complex representation `V : FDRep ℂ G`;
* derived API: simplicity of `V`, already encoded inside the defect-zero owner
  `HasDefectZero (V.ρ) p`.

No new owner or wrapper is needed here: the exercise should stay source-facing, stated directly
in terms of the existing chapter owner `HasDefectZero (V.ρ) p` rather than through a parallel
local alias or package.
-/

-- Proof sketch: use the character table of `A₄`, whose irreducible complex degrees are
-- `1, 1, 1, 3`; none of these is divisible by the `2`-part `4` of `|A₄| = 12`.
/-- Exercise 16-16.4-4 (1): for `A₄`, there is no irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 2`, i.e. no simple object of the canonical owner
`FDRep ℂ A₄` has defect zero at `2`. -/
theorem alternatingGroup_four_not_exists_irreducible_complex_representation_of_defect_zero_at_two :
    ¬ ∃ V : FDRep ℂ A4, HasDefectZero (V.ρ) 2 := by
  rintro ⟨V, hdefect⟩
  let n := Module.finrank ℂ (Representation.asModule V.ρ)
  letI : Representation.IsIrreducible V.ρ := hdefect.isIrreducible
  letI : Nontrivial V.V := nontrivial_of_isIrreducible (ρ := V.ρ)
  -- Character orthogonality gives the generic bound `n² ≤ |A₄| = 12`.
  have hbound : n ^ 2 ≤ 12 := by
    have hsq := fdrep_finrank_sq_le_card V hdefect.isIrreducible
    simpa [n, alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)] using hsq
  -- Defect zero at `2` forces the `2`-part `4` of `|A₄|` to divide `n`.
  have hdvd : 4 ∣ n := by
    have hdvd' := hdefect.dvd_finrank
    rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)] at hdvd'
    have hpow : 2 ^ Nat.factorization 12 2 = 4 := by
      native_decide
    rw [hpow] at hdvd'
    simpa [n] using hdvd'
  have hpos : 0 < n := by
    simpa [n] using (Module.finrank_pos (R := ℂ) (M := V.V))
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hbound hpos
  have hkpos : 0 < k := by
    omega
  nlinarith [hbound, hkpos]

-- Proof sketch: use the standard degree-three irreducible representation of `A₄`, for example
-- the tetrahedral representation, and note that `3` is exactly the `3`-part of `|A₄| = 12`.
/-- Exercise 16-16.4-4 (2): for `A₄`, there is an irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 3`, i.e. a simple object of the canonical owner
`FDRep ℂ A₄` with defect zero at `3`. -/
theorem alternatingGroup_four_exists_irreducible_complex_representation_of_defect_zero_at_three :
    ∃ V : FDRep ℂ A4, HasDefectZero (V.ρ) 3 := by
  let ρ := Representation.permutationAugmentationRepresentation ℂ A4 (Fin 4)
  let V : FDRep ℂ A4 := FDRep.of ρ
  have h2 : MulAction.IsMultiplyPretransitive A4 (Fin 4) 2 := by
    simpa using alternatingGroup.isMultiplyPretransitive (α := Fin 4)
  have hirr : ρ.IsIrreducible :=
    permutation_augmentation_isIrreducible_of_two_pretransitive h2
  have hdim :
      Module.finrank ℂ
        (Representation.permutationAugmentationSubrepresentation ℂ A4 (Fin 4)).toSubmodule = 3 :=
    fin_four_permutation_augmentation_finrank_three
  refine ⟨V, ?_⟩
  -- The standard augmentation representation has degree `3`, exactly the `3`-part of `|A₄|`.
  refine ⟨?_, ?_⟩
  · simpa [V, ρ] using hirr
  · rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)]
    have hpow : 3 ^ Nat.factorization 12 3 = 3 := by
      native_decide
    have hdimV : Module.finrank ℂ (Representation.asModule V.ρ) = 3 := by
      simpa [V, ρ] using hdim
    rw [hpow, hdimV]

-- Proof sketch: use the character table of `S₄`, whose irreducible complex degrees are
-- `1, 1, 2, 3, 3`; none of these is divisible by the `2`-part `8` of `|S₄| = 24`.
/-- Exercise 16-16.4-4 (3): for `S₄`, there is no irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 2`, i.e. no simple object of the canonical owner
`FDRep ℂ S₄` has defect zero at `2`. -/
theorem symmetricGroup_four_not_exists_irreducible_complex_representation_of_defect_zero_at_two :
    ¬ ∃ V : FDRep ℂ S4, HasDefectZero (V.ρ) 2 := by
  rintro ⟨V, hdefect⟩
  let n := Module.finrank ℂ (Representation.asModule V.ρ)
  letI : Representation.IsIrreducible V.ρ := hdefect.isIrreducible
  letI : Nontrivial V.V := nontrivial_of_isIrreducible (ρ := V.ρ)
  have hcard : Nat.card S4 = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  -- The same orthogonality bound now gives `n² ≤ |S₄| = 24`.
  have hbound : n ^ 2 ≤ 24 := by
    have hsq := fdrep_finrank_sq_le_card V hdefect.isIrreducible
    simpa [n, hcard] using hsq
  -- Defect zero at `2` forces the `2`-part `8` of `|S₄|` to divide `n`.
  have hdvd : 8 ∣ n := by
    have hdvd' := hdefect.dvd_finrank
    rw [hcard] at hdvd'
    have hpow : 2 ^ Nat.factorization 24 2 = 8 := by
      native_decide
    rw [hpow] at hdvd'
    simpa [n] using hdvd'
  have hpos : 0 < n := by
    simpa [n] using (Module.finrank_pos (R := ℂ) (M := V.V))
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hbound hpos
  have hkpos : 0 < k := by
    omega
  nlinarith [hbound, hkpos]

-- Proof sketch: use either of the standard degree-three irreducible representations of `S₄`,
-- such as the quotient of the permutation representation by the diagonal line; its degree is
-- divisible by the `3`-part of `|S₄| = 24`.
/-- Exercise 16-16.4-4 (4): for `S₄`, there is an irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 3`, i.e. a simple object of the canonical owner
`FDRep ℂ S₄` with defect zero at `3`. -/
theorem symmetricGroup_four_exists_irreducible_complex_representation_of_defect_zero_at_three :
    ∃ V : FDRep ℂ S4, HasDefectZero (V.ρ) 3 := by
  let ρ := Representation.permutationAugmentationRepresentation ℂ S4 (Fin 4)
  let V : FDRep ℂ S4 := FDRep.of ρ
  have h2 : MulAction.IsMultiplyPretransitive S4 (Fin 4) 2 := by
    simpa using Equiv.Perm.isMultiplyPretransitive (α := Fin 4) 2
  have hirr : ρ.IsIrreducible :=
    permutation_augmentation_isIrreducible_of_two_pretransitive h2
  have hdim :
      Module.finrank ℂ
        (Representation.permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule = 3 :=
    fin_four_permutation_augmentation_finrank_three
  have hcard : Nat.card S4 = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  refine ⟨V, ?_⟩
  -- The same standard augmentation constituent has degree `3`, the `3`-part of `|S₄|`.
  refine ⟨?_, ?_⟩
  · simpa [V, ρ] using hirr
  · rw [hcard]
    have hpow : 3 ^ Nat.factorization 24 3 = 3 := by
      native_decide
    have hdimV : Module.finrank ℂ (Representation.asModule V.ρ) = 3 := by
      simpa [V, ρ] using hdim
    rw [hpow, hdimV]
