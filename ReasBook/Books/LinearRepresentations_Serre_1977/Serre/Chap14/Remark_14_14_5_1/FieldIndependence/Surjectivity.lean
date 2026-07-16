import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.FieldIndependence.AbsoluteIrreducibleAscends

/-!
# Surjectivity of scalar extension on irreducible characters (Brick — `⊇` direction)

For algebraically closed characteristic-`0` fields `L ⊆ E` and a finite group `G`, every irreducible
`E`-representation `T` is, up to isomorphism, the scalar extension of an irreducible
`L`-representation. Consequently `T.character` lies in the coefficientwise image of `R[L](G)`.

The argument is the Wedderburn count over both fields: pick a complete pairwise nonisomorphic family
`π` of simple `L`-representations; scalar extension `π'ᵢ := π'(πᵢ)` is again simple (Brick 1) and
pairwise nonisomorphic (characters are coefficientwise images of distinct `L`-characters, and the
coefficient map is injective), with the same dimensions. The identity `∑ dᵢ² = |G|` transports from
`L` to `E`, which forces `π'` to be a complete family over `E` — so `T` is isomorphic to some `π'ᵢ`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation

open CategoryTheory

namespace Representation

variable {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
variable {E : Type u} [Field E] [Algebra L E] [IsAlgClosed E]
variable {G : Type u} [Group G] [Finite G]

/-- Characteristic `0` passes from `L` to any field extension `E ⊇ L` (the coefficient embedding
`algebraMap L E` is injective). -/
private theorem charZero_extension (L : Type u) [Field L] [CharZero L] (E : Type u) [Field E]
    [Algebra L E] : CharZero E :=
  ⟨fun {a b} h => by
    have h' : algebraMap L E (a : L) = algebraMap L E (b : L) := by
      rw [map_natCast, map_natCast]; exact h
    exact Nat.cast_injective ((algebraMap L E).injective h')⟩

omit [CharZero L] [IsAlgClosed L] [IsAlgClosed E] [Finite G] in
/-- The character of the scalar extension of a finite-dimensional `L`-representation is the
coefficientwise image of the original character. -/
private theorem scalarExtension_character_eq
    {W : Type u} [AddCommGroup W] [Module L W] [FiniteDimensional L W] (ρ : Representation L G W) :
    (Representation.scalarExtension (k := E) ρ).character
      = fun g ↦ algebraMap L E (ρ.character g) := by
  ext g
  exact LinearMap.trace_baseChange (ρ g) E

/-- **The target (`⊇` content).** Every irreducible `E`-representation has its character in the
coefficientwise image of `R[L](G)`. -/
theorem irreducible_rep_character_mem_characterRingOverFieldInExtension
    {WT : Type u} [AddCommGroup WT] [Module E WT] [FiniteDimensional E WT]
    (T : Representation E G WT) (hT : T.IsIrreducible) :
    T.character ∈ characterRingOverFieldInExtension L E G := by
  classical
  haveI : CharZero E := charZero_extension L E
  haveI : NeZero (Nat.card G : E) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- Step 1: a complete pairwise nonisomorphic family of simple `L`-representations.
  obtain ⟨ιL, hfin, π, hπ_pw, hπ_comp⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := L) (G := G)
  have hπ_simple : ∀ i, Simple (π i) := fun i => hπ_comp.isSimple i
  -- Step 2: scalar extension of the family to `E`.
  let π' : ιL → FDRep E G := fun i ↦ FDRep.scalarExtension (π i)
  -- Step 3: each `π' i` is simple.
  have hπ'_simple : ∀ i, Simple (π' i) := by
    intro i
    letI : Simple (π i) := hπ_simple i
    letI hirr : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π' i).ρ :=
      isIrreducible_scalarExtension_of_isAlgClosed_base (E := E) (π i).ρ hirr
    exact FDRep.simple_of_isIrreducible (π' i)
  -- Step 4: pairwise nonisomorphic. The characters are coefficientwise images of distinct
  -- `L`-characters and the coefficient embedding is injective.
  have hπ'_char : ∀ i, (π' i).character = fun g ↦ algebraMap L E ((π i).character g) := by
    intro i
    exact scalarExtension_character_eq (π i).ρ
  have hπ_char_inj : Function.Injective fun i ↦ (π i).character := by
    have hli := linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
      L π hπ_simple hπ_pw
    have hinj := hli.injective
    intro i j hij
    apply hinj
    apply Subtype.ext
    funext g
    rw [FDRep.irreducibleCharacter_apply L (π i) g, FDRep.irreducibleCharacter_apply L (π j) g]
    exact congrFun hij g
  have hπ'_pw : PairwiseNonisomorphic π' := by
    intro i j hij he
    apply hij
    rcases he with ⟨e⟩
    have hce : (π' i).character = (π' j).character := FDRep.char_iso e
    rw [hπ'_char i, hπ'_char j] at hce
    have hbase : (π i).character = (π j).character := by
      funext g
      exact (algebraMap L E).injective (congrFun hce g)
    exact hπ_char_inj hbase
  -- Step 5: dimensions are preserved by scalar extension.
  have hdim : ∀ i, Module.finrank E (π' i) = Module.finrank L (π i) := by
    intro i
    exact Module.finrank_baseChange (R := E) (S := L) (M' := (π i))
  -- Step 6: the square-degree sum transports from `L` to `E`, and Step 7: the `E`-family is
  -- complete. We feed the transported identity directly to the completeness criterion, matching its
  -- ambient `Fintype` instance via `Finset.sum_congr`.
  have hπ'_comp : IsCompleteIrreducibleFamily π' := by
    refine isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card (K := E) π' hπ'_simple hπ'_pw ?_
    rw [← sum_sq_degree_eq_card_of_complete_irreducible_family (K := L) π hπ_comp hπ_pw]
    exact Finset.sum_congr rfl fun i _ => by rw [hdim i]
  -- Step 8: locate `T` in the family.
  obtain ⟨i, ⟨e⟩⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation π' hπ'_comp T hT
  -- Step 9: `T.character = (π' i).character` is the coefficientwise image of `(π i).character`.
  have hTchar : T.character = fun g ↦ algebraMap L E ((π i).character g) := by
    have h1 : (FDRep.of T).character = (π' i).character := FDRep.char_iso e
    have h2 : (FDRep.of T).character = T.character := rfl
    rw [← h2, h1, hπ'_char i]
  -- Step 10/11: `(π i).character ∈ R[L](G)`, and its image is `T.character`.
  letI : Simple (π i) := hπ_simple i
  refine Subalgebra.mem_map.2
    ⟨(π i).character, FDRep.character_mem_characterRingOverField L (π i), ?_⟩
  rw [hTchar]
  rfl

end Representation
