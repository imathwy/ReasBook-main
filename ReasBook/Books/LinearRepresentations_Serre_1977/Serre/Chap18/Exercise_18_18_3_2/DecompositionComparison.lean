import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterSpan

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section LocalChapter18Comparisons

variable {p : ℕ}
variable {B : Type u} [CommRing B] [IsLocalRing B]
variable {K : Type u} [Field K] [Algebra B K] [IsFractionRing B K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain B] [IsDiscreteValuationRing B]
variable [IsAlgClosed (IsLocalRing.ResidueField B)] [CharP (IsLocalRing.ResidueField B) p]

local notation "k" => IsLocalRing.ResidueField B

/-- Helper for Exercise 18-18.3-2: temporary local decomposition-compatibility bridge for virtual
modular characters. -/
theorem virtualModularCharacter_decomposition_eq_character_restriction
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : B,
      algebraMap B K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue B a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (y : R₀[K](G)) :
    _root_.Representation.virtualModularCharacter
        (PrimeToPRoot.toFieldLift lift) ((decompositionHom B K G) y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  -- Route correction: descend Serre's stable-lattice comparison through the Grothendieck quotient,
  -- matching the Chapter `18.3.1` regular-branch proof route.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is sent to the zero character on both sides.
    ext s
    simp
  · intro E
    obtain ⟨L⟩ := Representation.exists_stableLattice B E.ρ
    -- On a generator `[E]₀`, evaluate `decompositionHom` using a stable lattice and apply the
    -- source comparison between its reduced modular character and the ordinary character upstairs.
    ext s
    change
      (_root_.Representation.virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom B K G) [E]₀)) s =
        ((finiteRepGrothendieckCharacter K G [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := B) (K := K) (G := G) E L,
      _root_.Representation.virtualModularCharacter_class, finiteRepGrothendieckCharacter_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := B) (K := K) (G := G) lift hred E.ρ L s (hω s.1 s.2))
  · intro a ha
    -- Additive functoriality transports the established equality through negation.
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    -- Additive functoriality transports the established equality through sums.
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

end LocalChapter18Comparisons

end Representation
