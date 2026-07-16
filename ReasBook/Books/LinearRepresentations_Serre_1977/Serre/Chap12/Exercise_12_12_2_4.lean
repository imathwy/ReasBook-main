import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_4_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap05.Exercise_5_5_7_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MonoidAlgebra
open scoped SubgroupInduction

namespace Representation

/-- Helper for Exercise 12-12.2-4: the family Wedderburn map attached to a family of
representations. -/
private abbrev familyEndAlgHom
    {k ι G : Type*} [CommSemiring k] [Monoid G] (π : ι → Rep k G) :
    k[G] →ₐ[k] Π i, Module.End k (π i) :=
  Pi.algHom k (fun i ↦ Module.End k (π i)) fun i ↦ (π i).ρ.asAlgebraHom

local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)

private local instance : Fintype A4 := Fintype.ofFinite A4

private local instance : (V4).Normal :=
  alternatingGroup.normal_kleinFour (show Nat.card (Fin 4) = 4 by simp)

/-- Helper for Exercise 12-12.2-4: the canonical Klein four subgroup of `A₄` has quotient of
order `3`. -/
private lemma a4_quotient_by_kleinFour_card :
    Nat.card (A4 ⧸ V4) = 3 := by
  -- Compare the order of `A₄` with the order of its canonical Klein four subgroup.
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hV4 : Nat.card V4 = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul : Nat.card A4 = Nat.card (A4 ⧸ V4) * Nat.card V4 := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A4) V4)
  rw [hA4, hV4] at hmul
  omega

/-- Helper for Exercise 12-12.2-4: the abelianization `A₄/V₄` is the cyclic group of order
`3`. -/
private lemma a4_quotient_by_kleinFour_mulEquiv_c3 :
    Nonempty ((A4 ⧸ V4) ≃* Multiplicative (ZMod 3)) := by
  -- Groups of the same prime cardinality are canonically isomorphic up to choice.
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ⟨mulEquivOfPrimeCardEq
    (G := A4 ⧸ V4)
    (G' := Multiplicative (ZMod 3))
    a4_quotient_by_kleinFour_card
    (by simp)⟩

/-- Helper for Exercise 12-12.2-4: the complex linear characters of `A₄/V₄` form the dual group
that supplies the three degree-`1` complex constituents of `A₄`. -/
private abbrev a4_linearCharacters :=
  (A4 ⧸ V4) →* ℂˣ

/-- Helper for Exercise 12-12.2-4: via the quotient `A₄/V₄ ≃ C₃`, the linear-character group of
`A₄/V₄` identifies with the linear-character group of `C₃`. -/
private noncomputable def a4_linearCharacters_mulEquiv_c3Dual :
    a4_linearCharacters ≃* ((Multiplicative (ZMod 3)) →* ℂˣ) := by
  -- Precompose characters with the chosen quotient isomorphism.
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  exact eQ.monoidHomCongrLeft

/-- Helper for Exercise 12-12.2-4: the complex linear-character group of `A₄/V₄` has order
`3`. -/
private lemma a4_linearCharacters_card :
    Nat.card a4_linearCharacters = 3 := by
  -- Finite abelian duality turns the `C₃`-dual into another copy of `C₃`.
  have hC3 :
      Nat.card ((Multiplicative (ZMod 3)) →* ℂˣ) = 3 := by
    simpa using
      (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact
    (Nat.card_congr a4_linearCharacters_mulEquiv_c3Dual.toEquiv).trans hC3

private local instance : Finite a4_linearCharacters := by
  -- Transport finiteness from the cyclic group `C₃`.
  let eDual :
      ((Multiplicative (ZMod 3)) →* ℂˣ) ≃* Multiplicative (ZMod 3) :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact
    Finite.of_equiv (Multiplicative (ZMod 3))
      (a4_linearCharacters_mulEquiv_c3Dual.trans eDual).symm.toEquiv

private noncomputable local instance : Fintype a4_linearCharacters :=
  Fintype.ofFinite a4_linearCharacters

/-- Helper for Exercise 12-12.2-4: each complex linear character of `A₄/V₄` pulls back along the
quotient map to a degree-`1` complex representation of `A₄`. -/
private abbrev a4_linearCharacterFamily (χ : a4_linearCharacters) : Rep ℂ A4 :=
  Rep.of ((χ.comp (QuotientGroup.mk' V4)).toRepresentation)

/-- Helper for Exercise 12-12.2-4: distinct complex linear characters of `A₄/V₄` stay
nonisomorphic after pullback to `A₄`. -/
private lemma a4_linearCharacterFamily_pairwise :
    CategoryTheory.PairwiseNonisomorphic a4_linearCharacterFamily := by
  intro χ ψ hχψ hiso
  rcases hiso with ⟨e⟩
  -- An isomorphism would identify the pulled-back characters pointwise on `A₄`.
  have hchar :
      ((χ.comp (QuotientGroup.mk' V4)).toRepresentation).character =
        ((ψ.comp (QuotientGroup.mk' V4)).toRepresentation).character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hχeqψ : χ = ψ := by
    -- The quotient map is surjective, so equality after pullback forces equality on `A₄/V₄`.
    ext q
    rcases QuotientGroup.mk'_surjective V4 q with ⟨g, hg⟩
    have hval : (χ (QuotientGroup.mk' V4 g) : ℂ) = (ψ (QuotientGroup.mk' V4 g) : ℂ) := by
      simpa [MonoidHom.toRepresentation_character_apply] using congrFun hchar g
    simpa [hg] using hval
  exact hχψ hχeqψ

/-- Helper for Exercise 12-12.2-4: the three linear characters of `A₄/V₄` already form the
complete irreducible family for the cyclic quotient `A₄/V₄ ≃ C₃`. -/
lemma a4_quotient_linearCharacterFamily_complete :
    IsCompleteIrreducibleFamily
      (fun χ : a4_linearCharacters ↦
        FDRep.of (χ.toRepresentation)) := by
  -- The quotient-side family is entirely degree `1`, so the sum-of-squares criterion reduces to
  -- the cardinality computation `3 = |A₄/V₄|`.
  letI : NeZero (Nat.card (A4 ⧸ V4) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hsimple :
      ∀ χ : a4_linearCharacters, CategoryTheory.Simple (FDRep.of χ.toRepresentation) := by
    intro χ
    have hχirr : Representation.IsIrreducible (FDRep.of χ.toRepresentation).ρ := by
      simpa using (MonoidHom.toRepresentation_isIrreducible χ)
    letI : Representation.IsIrreducible (FDRep.of χ.toRepresentation).ρ := hχirr
    exact FDRep.simple_of_isIrreducible (FDRep.of χ.toRepresentation)
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic
        (fun χ : a4_linearCharacters ↦ FDRep.of χ.toRepresentation) := by
    intro χ ψ hχψ hiso
    rcases hiso with ⟨e⟩
    have hchar : χ.toRepresentation.character = ψ.toRepresentation.character :=
      FDRep.char_iso e
    have hχeqψ : χ = ψ := by
      ext q
      simpa [MonoidHom.toRepresentation_character_apply] using congrFun hchar q
    exact hχψ hχeqψ
  refine
    Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      (π := fun χ : a4_linearCharacters ↦ FDRep.of χ.toRepresentation)
      hsimple hpairwise ?_
  -- Every member has degree `1`, so the sum is just the cardinality of the dual group.
  have hsum :
      ∑ χ : a4_linearCharacters, Module.finrank ℂ (FDRep.of χ.toRepresentation) ^ 2 =
        Fintype.card a4_linearCharacters := by
    simp
  rw [hsum, ← Nat.card_eq_fintype_card, a4_linearCharacters_card, a4_quotient_by_kleinFour_card]

/-- Helper for Exercise 12-12.2-4: the quadratic cyclotomic field `ℚ(ω)` has `ℚ`-dimension
`2`. -/
lemma finrank_cyclotomicField_three :
    Module.finrank ℚ (CyclotomicField 3 ℚ) = 2 := by
  -- This is the standard cyclotomic-degree formula `φ(3)=2`.
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := 3) (K := ℚ)
  simpa using IsCyclotomicExtension.Rat.finrank 3 (CyclotomicField 3 ℚ)

/-- Helper for Exercise 12-12.2-4: the source group algebra `ℚ[A₄]` has dimension `12`. -/
lemma a4_groupAlgebra_finrank_twelve :
    Module.finrank ℚ ℚ[A4] = 12 := by
  -- The group algebra is the `ℚ`-space of finitely supported functions on a `12`-element group.
  have hfinrank_finsupp : Module.finrank ℚ (A4 →₀ ℚ) = Fintype.card A4 := by
    exact Module.finrank_finsupp_self (R := ℚ) (ι := A4)
  calc
    Module.finrank ℚ ℚ[A4] = Fintype.card A4 := by
      change Module.finrank ℚ (A4 →₀ ℚ) = Fintype.card A4
      exact hfinrank_finsupp
    _ = 12 := by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)

/-- Helper for Exercise 12-12.2-4: the proposed target algebra has total `ℚ`-dimension `12`. -/
lemma a4_target_finrank_twelve :
    Module.finrank ℚ (ℚ × CyclotomicField 3 ℚ × Matrix (Fin 3) (Fin 3) ℚ) = 12 := by
  -- Add the dimensions of the trivial, cyclotomic, and matrix factors.
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, finrank_cyclotomicField_three,
    Module.finrank_matrix]
  norm_num

/-- Helper for Exercise 12-12.2-4: Serre's induced nonlinear constituent of `A₄`. -/
private abbrev a4_augmentationRepresentation :
    Representation ℂ A4 (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
  ind (Subgroup.subtype V4) a4_theta.toRepresentation

/-- Helper for Exercise 12-12.2-4: the nonlinear `3`-dimensional complex constituent of `A₄`
coming from Serre's induced character `θ` is irreducible. -/
private lemma a4_augmentation_representation_isIrreducible :
    a4_augmentationRepresentation.IsIrreducible := by
  -- Route correction: use the earlier Chapter 5 induced-model proof of the nonlinear constituent,
  -- rather than a later Chapter 12 classification or a fresh orbit calculation here.
  simpa [a4_augmentationRepresentation] using a4_induced_theta_isIrreducible

/-- Helper for Exercise 12-12.2-4: the induced nonlinear constituent is finite-dimensional. -/
private local instance a4_augmentationRepresentation_moduleFinite :
    Module.Finite ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) := by
  -- Finite groups force irreducible complex representations to be finite-dimensional.
  letI : a4_augmentationRepresentation.IsIrreducible :=
    a4_augmentation_representation_isIrreducible
  letI : FiniteDimensional ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
    IsIrreducible.finiteDimensional_of_finite a4_augmentationRepresentation
  infer_instance

/-- Helper for Exercise 12-12.2-4: the nonlinear augmentation constituent has degree `3`. -/
private lemma a4_augmentationRepresentation_finrank_three :
    Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) = 3 := by
  -- Evaluate the known Chapter 5 character formula at the identity.
  have hchar' := congrFun a4_induced_theta_character_eq_psi 1
  change (a4_augmentationRepresentation.character 1 : ℂ) =
      (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 at hchar'
  have hfinrank_complex :
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) = 3 := by
    calc
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) =
          a4_augmentationRepresentation.character 1 := by
            symm
            exact Representation.char_one a4_augmentationRepresentation
      _ = (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 := hchar'
      _ = 3 := by
            norm_num [Representation.char_one]
  exact_mod_cast hfinrank_complex

/-- Helper for Exercise 12-12.2-4: no pulled-back linear character of `A₄/V₄` is isomorphic to
the nonlinear augmentation constituent. -/
private lemma a4_linearCharacterFamily_not_isomorphic_augmentation
    (χ : a4_linearCharacters) :
    ¬ Nonempty
      (a4_linearCharacterFamily χ ≅
        Rep.of a4_augmentationRepresentation) := by
  intro hiso
  rcases hiso with ⟨e⟩
  -- Compare the two characters at the identity: the linear slot has degree `1`, while the
  -- augmentation constituent has degree `3`.
  have hchar :
      (a4_linearCharacterFamily χ).ρ.character = a4_augmentationRepresentation.character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hdeg :
      ((a4_linearCharacterFamily χ).ρ.character) 1 =
        a4_augmentationRepresentation.character 1 := by
    exact congrFun hchar 1
  have hdeg' : (1 : ℂ) = 3 := by
    have hdeg'' := hdeg
    simp [a4_linearCharacterFamily, a4_augmentationRepresentation_finrank_three,
      Representation.char_one] at hdeg''
  norm_num at hdeg'

/-- Helper for Exercise 12-12.2-4: after choosing an ordering of the three linear characters of
`A₄/V₄`, the four complex irreducible constituents of `A₄` can be indexed by `Fin 4`. -/
private noncomputable def a4_explicitComplexFamily
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Fin 4 → Rep ℂ A4
  | ⟨0, _⟩ => a4_linearCharacterFamily (eLin 0)
  | ⟨1, _⟩ => a4_linearCharacterFamily (eLin 1)
  | ⟨2, _⟩ => a4_linearCharacterFamily (eLin 2)
  | ⟨3, _⟩ => Rep.of a4_augmentationRepresentation

private local instance a4_explicitComplexFamily_moduleFinite
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.Finite ℂ (a4_explicitComplexFamily eLin i) := by
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact a4_augmentationRepresentation_moduleFinite

/-- Helper for Exercise 12-12.2-4: the explicit complex family, viewed in the canonical
finite-dimensional owner `FDRep`, is indexed literally by `Fin 4`. -/
abbrev a4_explicitFDRepFamily
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Fin 4 → FDRep ℂ A4 :=
  fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)

/-- Helper for Exercise 12-12.2-4: the explicit `Fin 4`-indexed complex family for `A₄`
is pairwise nonisomorphic. -/
private lemma a4_explicit_complex_family_pairwise
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    CategoryTheory.PairwiseNonisomorphic (a4_explicitComplexFamily eLin) := by
  intro i j hij hij_iso
  -- There are only four slots: three linear characters and the augmentation constituent.
  fin_cases i <;> fin_cases j
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) hij_iso
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) ⟨h.symm⟩
  · contradiction

/-- Helper for Exercise 12-12.2-4: the four members of the explicit complex family have degrees
`1, 1, 1, 3`. -/
private lemma a4_explicit_complex_family_degree
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 1
      | 3 => 3 := by
  -- Enumerate the four slots and reduce each degree to the linear or augmentation computation.
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · simpa using a4_augmentationRepresentation_finrank_three

/-- Helper for Exercise 12-12.2-4: the explicit `Fin 4`-indexed complex family consisting of the
three linear characters and the augmentation representation is complete. -/
private lemma a4_explicit_complex_family_complete
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    IsCompleteIrreducibleFamily
      (a4_explicitFDRepFamily eLin) := by
  -- Route correction: freeze the complete family as a literal `Fin 4 → FDRep ℂ A4` before
  -- invoking the later rational comparison. For the completeness proof itself, we first work
  -- with the underlying `Rep` family and then transport the result back to the named adapter.
  letI : NeZero (Nat.card A4 : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hlinear_simple :
      ∀ χ : a4_linearCharacters,
        CategoryTheory.Simple (FDRep.of ((a4_linearCharacterFamily χ).ρ)) := by
    intro χ
    have hχirr : Representation.IsIrreducible ((a4_linearCharacterFamily χ).ρ) := by
      -- Each quotient character gives a one-dimensional irreducible constituent after pullback.
      simpa [a4_linearCharacterFamily] using
        (MonoidHom.toRepresentation_isIrreducible (χ.comp (QuotientGroup.mk' V4)))
    letI : Representation.IsIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ)).ρ := by
      simpa using hχirr
    -- A one-dimensional character gives a simple finite-dimensional representation.
    exact FDRep.simple_of_isIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ))
  have haugmentation_simple :
      CategoryTheory.Simple (FDRep.of a4_augmentationRepresentation) := by
    letI : Representation.IsIrreducible (FDRep.of a4_augmentationRepresentation).ρ := by
      simpa using a4_augmentation_representation_isIrreducible
    -- The nonlinear slot is simple because the imported induced constituent is irreducible.
    exact FDRep.simple_of_isIrreducible (FDRep.of a4_augmentationRepresentation)
  have hcomplete :
      IsCompleteIrreducibleFamily
        (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
    have hsimple :
        ∀ i, CategoryTheory.Simple (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
      intro i
      -- Enumerate the four constituents and dispatch to the linear or augmentation cases.
      fin_cases i <;> dsimp [a4_explicitComplexFamily]
      · exact hlinear_simple (eLin 0)
      · exact hlinear_simple (eLin 1)
      · exact hlinear_simple (eLin 2)
      · simpa using haugmentation_simple
    have hpairwise :
        CategoryTheory.PairwiseNonisomorphic
          (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
      intro i j hij hij_iso
      rcases hij_iso with ⟨e⟩
      exact
        a4_explicit_complex_family_pairwise eLin hij
          ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
    refine
      Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
        (π := fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ))
        hsimple hpairwise ?_
    -- The explicit degree table is `1, 1, 1, 3`, so the sum of squares is `12 = |A₄|`.
    rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)]
    have hdeg :
        ∀ i : Fin 4,
          Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V ^ 2 =
            (match i with
            | 0 => 1
            | 1 => 1
            | 2 => 1
            | 3 => 3) ^ 2 := by
      intro i
      rw [a4_explicit_complex_family_degree]
    -- Rewrite each summand to the explicit degree table and finish by arithmetic.
    simp_rw [hdeg]
    change ((@Finset.univ (Fin 4) (instFintypeOfFinite (Fin 4))).sum fun x : Fin 4 =>
      (match x with
      | 0 => 1
      | 1 => 1
      | 2 => 1
      | 3 => 3) ^ 2) = 12
    have huniv :
        (@Finset.univ (Fin 4) (instFintypeOfFinite (Fin 4))) =
          (@Finset.univ (Fin 4) (Fin.fintype 4)) := by
      ext x
      simp
    rw [huniv]
    decide
  simpa [a4_explicitFDRepFamily] using hcomplete

/-- Helper for Exercise 12-12.2-4: the quotient `A₄/V₄` also has a distinguished nontrivial
`ℚ(ω)`-valued linear character, obtained by transporting a generator of the dual cyclic group
through finite abelian duality. -/
local instance cyclotomicField_three_hasEnoughRootsOfUnity :
    HasEnoughRootsOfUnity (CyclotomicField 3 ℚ) 3 := by
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := 3) (K := ℚ)
  refine ⟨?_, inferInstance⟩
  exact ⟨IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ),
    IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)⟩

/-- Helper for Exercise 12-12.2-4: the quotient character is obtained from the primitive cubic
root in `CyclotomicField 3 ℚ`. -/
noncomputable def a4_cyclotomic_quotient_character :
    (A4 ⧸ V4) →* (CyclotomicField 3 ℚ)ˣ := by
  -- Choose the quotient identification `A₄/V₄ ≃ C₃` and pull back the standard nontrivial dual
  -- character of `C₃`.
  letI : HasEnoughRootsOfUnity (CyclotomicField 3 ℚ) (Nat.card (Multiplicative (ZMod 3))) := by
    simpa using
      (cyclotomicField_three_hasEnoughRootsOfUnity :
        HasEnoughRootsOfUnity (CyclotomicField 3 ℚ) 3)
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  let eDual :
      ((Multiplicative (ZMod 3)) →* (CyclotomicField 3 ℚ)ˣ) ≃*
        Multiplicative (ZMod 3) :=
    (IsCyclic.monoidHom_equiv_self
      (Multiplicative (ZMod 3)) (CyclotomicField 3 ℚ)).some
  exact (eQ.monoidHomCongrLeft).symm (eDual.symm (Multiplicative.ofAdd (1 : ZMod 3)))

/-- Helper for Exercise 12-12.2-4: the cyclotomic factor gives a one-dimensional
`ℚ(ω)`-representation of `A₄` after pullback along the quotient map. -/
noncomputable def a4_cyclotomic_group_character :
    A4 →* (CyclotomicField 3 ℚ)ˣ :=
  a4_cyclotomic_quotient_character.comp (QuotientGroup.mk' V4)

/-- Helper for Exercise 12-12.2-4: Serre's rational degree-`3` constituent is the augmentation
representation for the natural action of `A₄` on `Fin 4`. -/
abbrev a4_rational_augmentationRepresentation :
    Representation ℚ A4
      (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule :=
  permutationAugmentationRepresentation ℚ A4 (Fin 4)

/-- Helper for Exercise 12-12.2-4: the rational augmentation representation has degree `3`. -/
lemma a4_rational_augmentationRepresentation_finrank_three :
    Module.finrank ℚ
      (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule = 3 := by
  -- Compute the kernel dimension from the surjective augmentation map on the permutation module.
  let ε : (Fin 4 →₀ ℚ) →ₗ[ℚ] ℚ := permutationAugmentationLinearMap ℚ (Fin 4)
  have hrange : LinearMap.range ε = ⊤ := by
    -- A basis vector maps to `1`, so every scalar is hit.
    rw [LinearMap.range_eq_top]
    intro q
    refine ⟨Finsupp.single 0 q, ?_⟩
    simp [ε, permutationAugmentationLinearMap]
  have hsplit := LinearMap.finrank_range_add_finrank_ker ε
  have hrange_finrank : Module.finrank ℚ (LinearMap.range ε) = 1 := by
    rw [hrange]
    simp
  have hdomain_finrank : Module.finrank ℚ (Fin 4 →₀ ℚ) = 4 := by
    simp
  have hker_finrank : Module.finrank ℚ (LinearMap.ker ε) = 3 := by
    linarith [hsplit, hrange_finrank, hdomain_finrank]
  simpa [ε, permutationAugmentationSubrepresentation, permutationAugmentation] using hker_finrank

/-- Helper for Exercise 12-12.2-4: choose a `Fin 3` basis on the rational augmentation
representation so that its endomorphism algebra becomes `M₃(ℚ)`. -/
noncomputable def a4_rational_augmentationBasis :
    Module.Basis (Fin 3) ℚ
      (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule :=
  Module.finBasisOfFinrankEq ℚ
    (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule
    a4_rational_augmentationRepresentation_finrank_three

/-- Helper for Exercise 12-12.2-4: the trivial constituent of `A₄` gives the usual augmentation
map from `ℚ[A₄]` to `ℚ`. -/
abbrev a4_trivial_algHom : ℚ[A4] →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ A4 (1 : A4 →* ℚ)

/-- Helper for Exercise 12-12.2-4: the cyclotomic quotient character extends to a
`ℚ`-algebra map from `ℚ[A₄]` to `ℚ(ω)`. -/
abbrev a4_cyclotomic_algHom :
    ℚ[A4] →ₐ[ℚ] CyclotomicField 3 ℚ :=
  MonoidAlgebra.lift ℚ (CyclotomicField 3 ℚ) A4
    ((Units.coeHom (CyclotomicField 3 ℚ)).comp
      a4_cyclotomic_group_character)

/-- Helper for Exercise 12-12.2-4: after choosing a basis on the rational augmentation factor,
its group-algebra action becomes a matrix-valued algebra map. -/
noncomputable def a4_rational_augmentation_matrixAlgHom :
    ℚ[A4] →ₐ[ℚ] Matrix (Fin 3) (Fin 3) ℚ :=
  ((LinearMap.toMatrixAlgEquiv a4_rational_augmentationBasis).toAlgHom).comp
    a4_rational_augmentationRepresentation.asAlgebraHom

/-- Helper for Exercise 12-12.2-4: the explicit rational Artin-Wedderburn comparison map with
slots `ℚ`, `ℚ(ω)`, and `M₃(ℚ)`. -/
noncomputable def a4_rational_decomposition_algHom :
    ℚ[A4] →ₐ[ℚ] ℚ × CyclotomicField 3 ℚ × Matrix (Fin 3) (Fin 3) ℚ :=
  a4_trivial_algHom.prod (a4_cyclotomic_algHom.prod a4_rational_augmentation_matrixAlgHom)

/-- Helper for Exercise 12-12.2-4: scalar extension carries the group-algebra action to the
coefficientwise image in the scalar-extended representation. -/
lemma scalar_extension_asAlgebraHom_map
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ G V) (x : ℚ[G]) :
    (Representation.scalarExtension ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) x) =
      LinearMap.baseChange ℂ (ρ.asAlgebraHom x) := by
  -- Route correction: instead of an arbitrary-element tensor induction, compare the scalar-extended
  -- action with base change on the monoid-algebra generators and then extend linearly.
  refine MonoidAlgebra.induction_on
    (p := fun y : ℚ[G] ↦
      (Representation.scalarExtension ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) y) =
        LinearMap.baseChange ℂ (ρ.asAlgebraHom y))
    x ?_ ?_ ?_
  · intro g
    -- On a group element, scalar extension is definitionally `Module.End.baseChangeHom`.
    simp [MonoidAlgebra.of, Representation.scalarExtension]
    rfl
  · intro a b ha hb
    -- Both sides are additive in the group-algebra variable.
    simp [ha, hb]
  · intro r a ha
    -- Coefficient scalars commute with both `mapRingHom` and `LinearMap.baseChange`.
    have hmap :
        MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) (r • a) =
          (algebraMap ℚ ℂ r) • MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) a := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
    rw [hmap, AlgHom.map_smul_of_tower, ha]
    change r • LinearMap.baseChange ℂ (ρ.asAlgebraHom a) =
      LinearMap.baseChange ℂ (ρ.asAlgebraHom (r • a))
    rw [← LinearMap.baseChange_smul]
    simp

/-- Helper for Exercise 12-12.2-4: for a one-dimensional complex character, the complexified
group-algebra action is scalar multiplication by the corresponding scalar algebra map. -/
lemma monoid_character_asAlgebraHom_map
    {G : Type*} [Group G] (β : G →* ℂˣ) (x : ℚ[G]) :
    (MonoidHom.toRepresentation β).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) x) =
      (MonoidAlgebra.lift ℚ ℂ G ((Units.coeHom ℂ).comp β) x) • LinearMap.id := by
  -- Again it is enough to check the formula on basis elements of the group algebra.
  refine MonoidAlgebra.induction_on
    (p := fun y : ℚ[G] ↦
      (MonoidHom.toRepresentation β).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) y) =
        (MonoidAlgebra.lift ℚ ℂ G ((Units.coeHom ℂ).comp β) y) • LinearMap.id)
    x ?_ ?_ ?_
  · intro g
    -- On a group element, the one-dimensional representation acts by scalar multiplication.
    ext
    simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro r a ha
    simp [Algebra.smul_def, ha, mul_assoc]

/-- Helper for Exercise 12-12.2-4: a representation equivalence intertwines the group-algebra
actions as well as the underlying group actions. -/
lemma equiv_comp_asAlgebraHom
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (x : ℂ[G]) :
    e.toLinearMap.comp (ρ.asAlgebraHom x) = (σ.asAlgebraHom x).comp e.toLinearMap := by
  -- Extend the intertwining identity from group elements to the whole group algebra.
  refine MonoidAlgebra.induction_on
    (p := fun y : ℂ[G] ↦
      e.toLinearMap.comp (ρ.asAlgebraHom y) = (σ.asAlgebraHom y).comp e.toLinearMap)
    x ?_ ?_ ?_
  · intro g
    simpa [Representation.asAlgebraHom_single_one] using e.isIntertwining' g
  · intro a b ha hb
    ext v
    simp [ha, hb, LinearMap.comp_add]
  · intro r a ha
    ext v
    have hv := LinearMap.congr_fun ha v
    simpa [Algebra.smul_def, mul_assoc] using congrArg (fun w ↦ r • w) hv

/-- Helper for Exercise 12-12.2-4: if a complex number is fixed by conjugation and satisfies
`z^3 = 1`, then it is the trivial cube root `1`. -/
lemma eq_one_of_real_cube_root
    {z : ℂ} (hfix : star z = z) (hpow : z ^ 3 = 1) :
    z = 1 := by
  -- Conjugation invariance forces `z` to be real, and the only real cube root of `1` is `1`.
  have him' : -z.im = z.im := by
    simpa using congrArg Complex.im hfix
  have him : z.im = 0 := by
    linarith
  have hre : z.re ^ 3 = 1 := by
    simpa [pow_three, Complex.mul_re, Complex.mul_im, him] using congrArg Complex.re hpow
  have hfac : (z.re - 1) * (z.re ^ 2 + z.re + 1) = 0 := by
    nlinarith [hre]
  have hpos : 0 < z.re ^ 2 + z.re + 1 := by
    nlinarith [sq_nonneg (z.re + 1 / 2 : ℝ)]
  have hzre : z.re = 1 := by
    nlinarith [hfac, hpos]
  apply Complex.ext <;> simp [hzre, him]

/-- Helper for Exercise 12-12.2-4: the distinguished quotient character is nontrivial. -/
lemma a4_cyclotomic_quotient_character_ne_one :
    a4_cyclotomic_quotient_character ≠ 1 := by
  -- Apply the chosen duality equivalence and note that we selected the nonidentity element
  -- `1 ∈ ZMod 3`.
  letI : HasEnoughRootsOfUnity (CyclotomicField 3 ℚ) (Nat.card (Multiplicative (ZMod 3))) := by
    simpa using
      (cyclotomicField_three_hasEnoughRootsOfUnity :
        HasEnoughRootsOfUnity (CyclotomicField 3 ℚ) 3)
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  let eDual :
      ((Multiplicative (ZMod 3)) →* (CyclotomicField 3 ℚ)ˣ) ≃*
        Multiplicative (ZMod 3) :=
    (IsCyclic.monoidHom_equiv_self
      (Multiplicative (ZMod 3)) (CyclotomicField 3 ℚ)).some
  have hdual :
      eDual.symm (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by
    intro h
    have h' := congrArg eDual h
    simp at h'
  intro h
  apply hdual
  ext z
  have hz := congrArg (fun χ : (A4 ⧸ V4) →* (CyclotomicField 3 ℚ)ˣ ↦ χ (eQ.symm z)) h
  simpa [a4_cyclotomic_quotient_character, eQ, eDual] using hz

/-- Helper for Exercise 12-12.2-4: every element of the quotient `A₄/V₄ ≃ C₃` has cube `1`. -/
lemma a4_quotient_cube_eq_one (q : A4 ⧸ V4) :
    q ^ 3 = 1 := by
  -- Transport the claim across the chosen quotient identification with `C₃`.
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  apply eQ.injective
  simpa using (pow_card_eq_one (x := eQ q))

/-- Helper for Exercise 12-12.2-4: the standard embedding of `ℚ(ω)` into `ℂ`. -/
noncomputable abbrev a4_cyclotomic_complexEmbedding :
    CyclotomicField 3 ℚ →+* ℂ :=
  NumberField.ComplexEmbedding.lift (CyclotomicField 3 ℚ) (algebraMap ℚ ℂ)

/-- Helper for Exercise 12-12.2-4: the conjugate embedding of `ℚ(ω)` into `ℂ`. -/
noncomputable abbrev a4_cyclotomic_conjugateEmbedding :
    CyclotomicField 3 ℚ →+* ℂ :=
  NumberField.ComplexEmbedding.conjugate a4_cyclotomic_complexEmbedding

/-- Helper for Exercise 12-12.2-4: the nontrivial complex linear character obtained by
specializing the cyclotomic quotient character along the standard embedding. -/
noncomputable abbrev a4_specialized_cyclotomic_linearCharacter :
    a4_linearCharacters :=
  (Units.map a4_cyclotomic_complexEmbedding.toMonoidHom).comp
    a4_cyclotomic_quotient_character

/-- Helper for Exercise 12-12.2-4: the conjugate nontrivial complex linear character obtained by
specializing along the conjugate embedding. -/
noncomputable abbrev a4_conjugate_cyclotomic_linearCharacter :
    a4_linearCharacters :=
  (Units.map a4_cyclotomic_conjugateEmbedding.toMonoidHom).comp
    a4_cyclotomic_quotient_character

/-- Helper for Exercise 12-12.2-4: any complex specialization of the cyclotomic quotient
character stays nontrivial because a field embedding is injective. -/
lemma a4_cyclotomic_specialization_ne_one
    (σ : CyclotomicField 3 ℚ →+* ℂ) :
    ((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character) ≠ 1 := by
  -- Descend a hypothetical trivial specialization back through the injective field embedding.
  intro h
  have hqall : ∀ q : A4 ⧸ V4, a4_cyclotomic_quotient_character q = 1 := by
    intro q
    apply Units.ext
    apply RingHom.injective σ
    have hq := congrArg (fun χ : a4_linearCharacters ↦ ((χ q : ℂˣ) : ℂ)) h
    simpa using hq
  exact a4_cyclotomic_quotient_character_ne_one (MonoidHom.ext hqall)

/-- Helper for Exercise 12-12.2-4: the standard complex specialization of the cyclotomic
character remains nontrivial. -/
lemma a4_specialized_cyclotomic_linearCharacter_ne_one :
    a4_specialized_cyclotomic_linearCharacter ≠ 1 := by
  -- This is the generic specialization-nontriviality statement at the standard embedding.
  simpa [a4_specialized_cyclotomic_linearCharacter] using
    a4_cyclotomic_specialization_ne_one a4_cyclotomic_complexEmbedding

/-- Helper for Exercise 12-12.2-4: the conjugate complex specialization of the cyclotomic
character is also nontrivial. -/
lemma a4_conjugate_cyclotomic_linearCharacter_ne_one :
    a4_conjugate_cyclotomic_linearCharacter ≠ 1 := by
  -- The same descent works for the conjugate embedding.
  simpa [a4_conjugate_cyclotomic_linearCharacter] using
    a4_cyclotomic_specialization_ne_one a4_cyclotomic_conjugateEmbedding

/-- Helper for Exercise 12-12.2-4: the two complex specializations of the cyclotomic character
are distinct. -/
lemma a4_specialized_cyclotomic_linearCharacters_ne :
    a4_conjugate_cyclotomic_linearCharacter ≠ a4_specialized_cyclotomic_linearCharacter := by
  -- Choose a quotient element on which the cyclotomic character is nontrivial.
  have hq_exists : ∃ q : A4 ⧸ V4, a4_cyclotomic_quotient_character q ≠ 1 := by
    by_contra hq_exists
    have hqall : ∀ q : A4 ⧸ V4, a4_cyclotomic_quotient_character q = 1 := by
      intro q
      exact not_not.mp (not_exists.mp hq_exists q)
    exact a4_cyclotomic_quotient_character_ne_one (MonoidHom.ext hqall)
  rcases hq_exists with ⟨q, hq_nontriv⟩
  intro hchars
  have hfix :
      star
          (a4_cyclotomic_complexEmbedding
            (a4_cyclotomic_quotient_character q : CyclotomicField 3 ℚ)) =
        a4_cyclotomic_complexEmbedding
          (a4_cyclotomic_quotient_character q : CyclotomicField 3 ℚ) := by
    -- Equality of the two specialized characters says the chosen value is fixed by conjugation.
    have hq := congrArg (fun χ : a4_linearCharacters ↦ ((χ q : ℂˣ) : ℂ)) hchars
    simpa [a4_conjugate_cyclotomic_linearCharacter, a4_specialized_cyclotomic_linearCharacter,
      NumberField.ComplexEmbedding.conjugate_coe_eq] using hq
  have hpow :
      (a4_cyclotomic_complexEmbedding
          (a4_cyclotomic_quotient_character q : CyclotomicField 3 ℚ)) ^ 3 =
        1 := by
    -- The quotient has exponent `3`, so the chosen cyclotomic value is a cube root of unity.
    have hpow_units : a4_cyclotomic_quotient_character q ^ 3 = 1 := by
      simpa using congrArg a4_cyclotomic_quotient_character (a4_quotient_cube_eq_one q)
    have hpow_field :
        ((a4_cyclotomic_quotient_character q : CyclotomicField 3 ℚ) ^ 3 :
          CyclotomicField 3 ℚ) = 1 := by
      simpa using
        congrArg (fun u : (CyclotomicField 3 ℚ)ˣ ↦ (u : CyclotomicField 3 ℚ)) hpow_units
    simpa [map_pow] using congrArg a4_cyclotomic_complexEmbedding hpow_field
  have hroot :
      a4_cyclotomic_complexEmbedding
          (a4_cyclotomic_quotient_character q : CyclotomicField 3 ℚ) = 1 :=
    eq_one_of_real_cube_root hfix hpow
  have hq_one : a4_cyclotomic_quotient_character q = 1 := by
    -- Injectivity of the standard embedding descends the equality back to `ℚ(ω)`.
    apply Units.ext
    apply RingHom.injective a4_cyclotomic_complexEmbedding
    simpa using hroot
  exact hq_nontriv hq_one

/-- Helper for Exercise 12-12.2-4: every complex linear character of `A₄/V₄` is either trivial,
the standard cyclotomic specialization, or its conjugate. -/
lemma a4_linear_character_cases_from_cyclotomic
    (χ : a4_linearCharacters) :
    χ = 1 ∨
      χ = a4_specialized_cyclotomic_linearCharacter ∨
        χ = a4_conjugate_cyclotomic_linearCharacter := by
  -- Package the three displayed characters into an injective map `Fin 3 → a4_linearCharacters`.
  let e : Fin 3 → a4_linearCharacters
    | 0 => 1
    | 1 => a4_specialized_cyclotomic_linearCharacter
    | 2 => a4_conjugate_cyclotomic_linearCharacter
  have he_inj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact a4_specialized_cyclotomic_linearCharacter_ne_one (by simpa [e] using hij.symm)
    · exfalso
      exact a4_conjugate_cyclotomic_linearCharacter_ne_one (by simpa [e] using hij.symm)
    · exfalso
      exact a4_specialized_cyclotomic_linearCharacter_ne_one (by simpa [e] using hij)
    · rfl
    · exfalso
      exact a4_specialized_cyclotomic_linearCharacters_ne (by simpa [e] using hij.symm)
    · exfalso
      exact a4_conjugate_cyclotomic_linearCharacter_ne_one (by simpa [e] using hij)
    · exfalso
      exact a4_specialized_cyclotomic_linearCharacters_ne (by simpa [e] using hij)
    · rfl
  have he_bij : Function.Bijective e := by
    refine (Fintype.bijective_iff_injective_and_card e).2 ⟨he_inj, ?_⟩
    have hcard_chars : Fintype.card a4_linearCharacters = 3 :=
      Fintype.card_eq_nat_card.trans a4_linearCharacters_card
    simp [Fintype.card_fin, hcard_chars]
  rcases he_bij.2 χ with ⟨i, rfl⟩
  fin_cases i <;> simp [e]

/-- Helper for Exercise 12-12.2-4: the pullback of a quotient character acts on the complexified
group algebra by the corresponding scalar algebra map. -/
lemma a4_linearCharacterFamily_asAlgebraHom_map
    (χ : a4_linearCharacters) (x : ℚ[A4]) :
    ((a4_linearCharacterFamily χ).ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x)) =
      (MonoidAlgebra.lift ℚ ℂ A4
          ((Units.coeHom ℂ).comp (χ.comp (QuotientGroup.mk' V4))) x) • LinearMap.id := by
  -- This is the one-dimensional action formula specialized to the pulled-back quotient character.
  simpa [a4_linearCharacterFamily] using
    monoid_character_asAlgebraHom_map (β := χ.comp (QuotientGroup.mk' V4)) x

/-- Helper for Exercise 12-12.2-4: the trivial linear slot vanishes when the rational trivial
slot vanishes. -/
lemma a4_trivial_linear_slot_zero
    (x : ℚ[A4]) (hx : a4_trivial_algHom x = 0) :
    ((a4_linearCharacterFamily (1 : a4_linearCharacters)).ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x)) = 0 := by
  -- Rewrite the pulled-back trivial character slot as scalar multiplication by the trivial
  -- augmentation value.
  rw [a4_linearCharacterFamily_asAlgebraHom_map]
  change
    (MonoidAlgebra.lift ℚ ℂ A4
        ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) x) •
      LinearMap.id = 0
  have hscalar :
      MonoidAlgebra.lift ℚ ℂ A4
          ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) x =
        algebraMap ℚ ℂ (a4_trivial_algHom x) := by
    -- Both sides are the same trivial-character algebra map after changing coefficients.
    refine MonoidAlgebra.induction_on
      (p := fun y : ℚ[A4] ↦
        MonoidAlgebra.lift ℚ ℂ A4
            ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) y =
          algebraMap ℚ ℂ (a4_trivial_algHom y))
      x ?_ ?_ ?_
    · intro g
      simp [a4_trivial_algHom, MonoidAlgebra.of]
    · intro a b ha hb
      calc
        MonoidAlgebra.lift ℚ ℂ A4
            ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) (a + b)
            = MonoidAlgebra.lift ℚ ℂ A4
                ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) a
              + MonoidAlgebra.lift ℚ ℂ A4
                  ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4)))
                  b := by
                  simp
        _ = algebraMap ℚ ℂ (a4_trivial_algHom a) + algebraMap ℚ ℂ (a4_trivial_algHom b) := by
              rw [ha, hb]
        _ = algebraMap ℚ ℂ (a4_trivial_algHom (a + b)) := by
              simp [a4_trivial_algHom]
    · intro r a ha
      calc
        MonoidAlgebra.lift ℚ ℂ A4
            ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4))) (r • a)
            = algebraMap ℚ ℂ r *
                MonoidAlgebra.lift ℚ ℂ A4
                  ((Units.coeHom ℂ).comp ((1 : a4_linearCharacters).comp (QuotientGroup.mk' V4)))
                  a := by
                  simp [Algebra.smul_def]
        _ = algebraMap ℚ ℂ r * algebraMap ℚ ℂ (a4_trivial_algHom a) := by
              rw [ha]
        _ = algebraMap ℚ ℂ (a4_trivial_algHom (r • a)) := by
              simp [a4_trivial_algHom, Algebra.smul_def]
  rw [hscalar, hx]
  simp

/-- Helper for Exercise 12-12.2-4: specializing the cyclotomic scalar slot along an embedding to
`ℂ` agrees with applying that embedding to `a4_cyclotomic_algHom`. -/
lemma a4_cyclotomic_specialization_lift_eq_comp
    (σ : CyclotomicField 3 ℚ →+* ℂ) (x : ℚ[A4]) :
    MonoidAlgebra.lift ℚ ℂ A4
        ((Units.coeHom ℂ).comp
          (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
            (QuotientGroup.mk' V4))) x =
      σ (a4_cyclotomic_algHom x) := by
  -- Compare the specialized lift with `σ ∘ a4_cyclotomic_algHom` on monoid generators and then
  -- extend across the group algebra.
  refine MonoidAlgebra.induction_on
    (p := fun y : ℚ[A4] ↦
      MonoidAlgebra.lift ℚ ℂ A4
          ((Units.coeHom ℂ).comp
            (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
              (QuotientGroup.mk' V4))) y =
        σ (a4_cyclotomic_algHom y))
    x ?_ ?_ ?_
  · intro g
    -- On a group element, both sides are the same specialized quotient-character value.
    simp [a4_cyclotomic_algHom, a4_cyclotomic_group_character, MonoidAlgebra.of]
  · intro a b ha hb
    -- Both maps are additive in the group-algebra element.
    calc
      MonoidAlgebra.lift ℚ ℂ A4
          ((Units.coeHom ℂ).comp
            (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
              (QuotientGroup.mk' V4))) (a + b)
          = MonoidAlgebra.lift ℚ ℂ A4
              ((Units.coeHom ℂ).comp
                (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
                  (QuotientGroup.mk' V4))) a
            + MonoidAlgebra.lift ℚ ℂ A4
                ((Units.coeHom ℂ).comp
                  (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
                    (QuotientGroup.mk' V4))) b := by
                    simp
      _ = σ (a4_cyclotomic_algHom a) + σ (a4_cyclotomic_algHom b) := by
            rw [ha, hb]
      _ = σ (a4_cyclotomic_algHom (a + b)) := by
            simp [a4_cyclotomic_algHom]
  · intro r a ha
    -- Both maps are `ℚ`-linear, with the right side gaining the same scalar through `σ`.
    calc
      MonoidAlgebra.lift ℚ ℂ A4
          ((Units.coeHom ℂ).comp
            (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
              (QuotientGroup.mk' V4))) (r • a)
          = algebraMap ℚ ℂ r *
              MonoidAlgebra.lift ℚ ℂ A4
                ((Units.coeHom ℂ).comp
                  (((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character).comp
                    (QuotientGroup.mk' V4))) a := by
                    simp [Algebra.smul_def]
      _ = algebraMap ℚ ℂ r * σ (a4_cyclotomic_algHom a) := by
            rw [ha]
      _ = σ (a4_cyclotomic_algHom (r • a)) := by
            simp [a4_cyclotomic_algHom, Algebra.smul_def]

/-- Helper for Exercise 12-12.2-4: each complex specialization of the cyclotomic slot vanishes
once the rational cyclotomic slot vanishes. -/
lemma a4_cyclotomic_specialization_linear_slot_zero
    (σ : CyclotomicField 3 ℚ →+* ℂ) (x : ℚ[A4]) (hx : a4_cyclotomic_algHom x = 0) :
    ((a4_linearCharacterFamily
          ((Units.map σ.toMonoidHom).comp a4_cyclotomic_quotient_character)).ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x)) = 0 := by
  -- Rewrite the one-dimensional slot as scalar multiplication by the specialized cyclotomic
  -- value.
  rw [a4_linearCharacterFamily_asAlgebraHom_map]
  rw [a4_cyclotomic_specialization_lift_eq_comp]
  simp [hx]

/-- Helper for Exercise 12-12.2-4: vanishing of the rational trivial and cyclotomic slots forces
vanishing on every complex linear constituent. -/
lemma a4_trivial_and_cyclotomic_zero_implies_all_linear_slots_zero
    (x : ℚ[A4]) (htriv : a4_trivial_algHom x = 0) (hcyclo : a4_cyclotomic_algHom x = 0)
    (χ : a4_linearCharacters) :
    ((a4_linearCharacterFamily χ).ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x)) = 0 := by
  -- Split the complex linear character into the trivial, standard cyclotomic, and conjugate
  -- cyclotomic cases.
  rcases a4_linear_character_cases_from_cyclotomic χ with hχ | hχ | hχ
  · simpa [hχ] using a4_trivial_linear_slot_zero x htriv
  · simpa [hχ, a4_specialized_cyclotomic_linearCharacter] using
      a4_cyclotomic_specialization_linear_slot_zero
        a4_cyclotomic_complexEmbedding x hcyclo
  · simpa [hχ, a4_conjugate_cyclotomic_linearCharacter] using
      a4_cyclotomic_specialization_linear_slot_zero
        a4_cyclotomic_conjugateEmbedding x hcyclo

/-- Helper for Exercise 12-12.2-4: scalar extension transports characters by the coefficient map
`ℚ → ℂ`. -/
lemma a4_scalarExtension_character_eq_map
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : Representation ℚ G V) :
    (Representation.scalarExtension ρ).character =
      fun g ↦ algebraMap ℚ ℂ (ρ.character g) := by
  -- Traces commute with base change.
  ext g
  exact LinearMap.trace_baseChange (ρ g) ℂ

/-- Helper for Exercise 12-12.2-4: the rational augmentation character equals the permutation
character minus the trivial character. -/
lemma a4_rational_augmentation_character_eq_permutation_sub_one
    (g : A4) :
    a4_rational_augmentationRepresentation.character g =
      (ofMulAction ℚ A4 (Fin 4)).character g - 1 := by
  -- The Chapter 7 augmentation splitting formula is valid over `ℚ`.
  letI : Invertible (Nat.card (Fin 4) : ℚ) := invertibleOfNonzero (by norm_num)
  have hsplit := congrFun
    (Representation.permutation_character_eq_trivial_add_augmentation
      (k := ℚ) (G := A4) (X := Fin 4)) g
  have htriv : (Representation.trivial ℚ A4 ℚ).character g = 1 := by
    simp [Representation.character]
  have hsplit' :
      (ofMulAction ℚ A4 (Fin 4)).character g =
        1 + a4_rational_augmentationRepresentation.character g := by
    simpa [Pi.add_apply, permutationAugmentationCharacter, htriv] using hsplit
  linarith

/-- Helper for Exercise 12-12.2-4: scalar extension identifies the rational augmentation
representation with the complex augmentation constituent. -/
lemma a4_rational_augmentation_scalarExtension_equiv :
    Nonempty
      ((Representation.scalarExtension a4_rational_augmentationRepresentation).Equiv
        a4_augmentationRepresentation) := by
  -- Compare both characters with the same permutation-minus-trivial formula.
  let ρ := Representation.scalarExtension (k₀ := ℚ) (k := ℂ)
    a4_rational_augmentationRepresentation
  let σ := a4_augmentationRepresentation
  letI : NeZero (Nat.card A4 : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card A4 : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  letI : σ.IsIrreducible := a4_augmentation_representation_isIrreducible
  have hchar :
      ρ.character = σ.character := by
    ext g
    calc
      ρ.character g =
          algebraMap ℚ ℂ (a4_rational_augmentationRepresentation.character g) := by
            simpa using
              congrFun
                (a4_scalarExtension_character_eq_map
                  a4_rational_augmentationRepresentation) g
      _ = algebraMap ℚ ℂ ((ofMulAction ℚ A4 (Fin 4)).character g - 1) := by
            rw [a4_rational_augmentation_character_eq_permutation_sub_one]
      _ = algebraMap ℚ ℂ ((ofMulAction ℚ A4 (Fin 4)).character g) - 1 := by
            simp
      _ = (ofMulAction ℂ A4 (Fin 4)).character g - 1 := by
            rw [ofMulAction_character_eq_ncard_fixedBy, ofMulAction_character_eq_ncard_fixedBy]
            simp
      _ = σ.character g := by
            symm
            exact congrFun a4_induced_theta_character_eq_psi g
  have hself :
      ⟪ρ.character, ρ.character⟫ = (1 : ℂ) := by
    rw [hchar]
    exact (Representation.self_character_pairing_eq_one_iff_isIrreducible σ).2 inferInstance
  have hρirr : ρ.IsIrreducible :=
    (Representation.self_character_pairing_eq_one_iff_isIrreducible ρ).mp hself
  by_contra hρσ
  letI : ρ.IsIrreducible := hρirr
  have hzero :
      ⟪ρ.character, σ.character⟫ = (0 : ℂ) := by
    have hsub : Subsingleton (Representation.IntertwiningMap ρ σ) := by
      refine ⟨fun f g ↦ ?_⟩
      rw [Representation.intertwiningMap_eq_zero_of_not_isomorphic
            (ρ1 := ρ) (ρ2 := σ) f hρσ]
      rw [Representation.intertwiningMap_eq_zero_of_not_isomorphic
            (ρ1 := ρ) (ρ2 := σ) g hρσ]
    have hpair_finrank :
        ⟪ρ.character, σ.character⟫ = Module.finrank ℂ (ρ.IntertwiningMap σ) := by
      rw [Representation.groupFunctionPairing_comm]
      rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
      simpa [Nat.card_eq_fintype_card] using
        (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := σ))
    letI : Subsingleton (Representation.IntertwiningMap ρ σ) := hsub
    rw [hpair_finrank, Module.finrank_zero_of_subsingleton]
    norm_num
  have hone :
      ⟪ρ.character, σ.character⟫ = (1 : ℂ) := by
    rw [hchar]
    exact (Representation.self_character_pairing_eq_one_iff_isIrreducible σ).2 inferInstance
  have : (0 : ℂ) = 1 := by
    rw [← hzero, hone]
  exact zero_ne_one this

/-- Helper for Exercise 12-12.2-4: if two complex representations are equivalent, then the zero
group-algebra action transports across the equivalence. -/
lemma zero_asAlgebraHom_of_equiv_zero
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (x : ℂ[G]) (hx : ρ.asAlgebraHom x = 0) :
    σ.asAlgebraHom x = 0 := by
  -- Apply the intertwining identity to vectors of the form `e.symm w`.
  have hcomp := equiv_comp_asAlgebraHom e x
  ext w
  let v := e.symm w
  have hv := LinearMap.congr_fun hcomp v
  change e ((ρ.asAlgebraHom x) v) = (σ.asAlgebraHom x) (e v) at hv
  rw [hx] at hv
  simpa [v] using hv.symm

/-- Helper for Exercise 12-12.2-4: for a module viewed through `Representation.ofModule'`, the
associated group-algebra operator is the original group-algebra scalar action. -/
private lemma ofModule'_asAlgebraHom_apply
    {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
    (r : ℂ[G]) (m : M) :
    ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials.
  refine MonoidAlgebra.induction_on (p := fun a : ℂ[G] =>
    ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom a) m = a • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 12-12.2-4: the owner module of `Representation.ofModule' M` is
canonically the original `ℂ[G]`-module `M`. -/
private lemma nonempty_ofModule'_asModuleLinearEquiv
    {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] :
    Nonempty ((Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M) := by
  -- Use the standard `asModuleEquiv` and verify that it respects the owner `ℂ[G]`-action.
  let toFun : (Representation.ofModule' (k := ℂ) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := ℂ) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : ℂ[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x) := by
                exact
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := ℂ) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x := by
            simp [ofModule'_asAlgebraHom_apply]
  refine ⟨?_⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }

/-- Helper for Exercise 12-12.2-4: a simple left ideal, viewed as `Representation.ofModule'`, is
an irreducible representation. -/
private lemma ofModule'_isIrreducible_of_isSimpleModule
    {G : Type*} [Group G] (S : Submodule ℂ[G] ℂ[G]) (hS : IsSimpleModule ℂ[G] S) :
    (Representation.ofModule' (k := ℂ) (G := G) S).IsIrreducible := by
  -- Transfer simplicity across the canonical owner-module equivalence and then use the
  -- irreducibility/simple-module bridge.
  rcases nonempty_ofModule'_asModuleLinearEquiv (G := G) (M := S) with ⟨eS⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := ℂ) (G := G) S)).2
      (@IsSimpleModule.congr (ℂ[G]) inferInstance
        ((Representation.ofModule' (k := ℂ) (G := G) S).asModule)
        (Representation.ofModule' (k := ℂ) (G := G) S).instAddCommGroupAsModule
        (Representation.ofModule' (k := ℂ) (G := G) S).instModuleMonoidAlgebraAsModule
        S S.addCommGroup S.module eS hS)

/-- Helper for Exercise 12-12.2-4: if an element of `ℂ[G]` kills every simple left ideal, then
its left-multiplication operator on `ℂ[G]` is zero. -/
private lemma left_mul_eq_zero_of_zero_on_all_simple_submodules
    {G : Type*} [Group G] [Finite G] [Invertible (Nat.card G : ℂ)]
    {x : ℂ[G]}
    (hx : ∀ (S : Submodule ℂ[G] ℂ[G]), IsSimpleModule ℂ[G] S →
      ∀ ⦃y : ℂ[G]⦄, y ∈ S → x * y = 0) :
    Algebra.lmul ℂ (ℂ[G]) x = 0 := by
  letI : IsSemisimpleModule ℂ[G] ℂ[G] := inferInstance
  have htop :
      (⨆ (S : Submodule ℂ[G] ℂ[G]) (_ : IsSimpleModule ℂ[G] S), S) = ⊤ := by
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_eq_top (R := ℂ[G]) (M := ℂ[G]))
  have htopK :
      (⨆ (S : Submodule ℂ[G] ℂ[G]) (_ : IsSimpleModule ℂ[G] S), S.restrictScalars ℂ) = ⊤ := by
    simpa using congrArg (Submodule.restrictScalars ℂ) htop
  have hspan :
      Submodule.span ℂ
          (Set.iUnion fun S : Submodule ℂ[G] ℂ[G] ↦
            Set.iUnion fun _ : IsSimpleModule ℂ[G] S ↦
              ((S.restrictScalars ℂ : Submodule ℂ ℂ[G]) : Set ℂ[G])) =
        ⊤ := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] ℂ[G] ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S)]
    exact htopK
  apply LinearMap.ext
  intro y
  have hy_span :
      y ∈ Submodule.span ℂ
        (Set.iUnion fun S : Submodule ℂ[G] ℂ[G] ↦
          Set.iUnion fun _ : IsSimpleModule ℂ[G] S ↦
            ((S.restrictScalars ℂ : Submodule ℂ ℂ[G]) : Set ℂ[G])) := by
    rw [hspan]
    simp
  refine Submodule.span_induction
    (p := fun z _ ↦ (Algebra.lmul ℂ (ℂ[G]) x) z = 0) ?_ ?_ ?_ ?_ hy_span
  · intro z hz
    rcases Set.mem_iUnion.1 hz with ⟨S, hz⟩
    rcases Set.mem_iUnion.1 hz with ⟨hS, hz⟩
    simpa using hx S hS hz
  · simp
  · intro z w hz hw hzh hwh
    calc
      ((Algebra.lmul ℂ (ℂ[G]) x) (z + w))
          = ((Algebra.lmul ℂ (ℂ[G]) x) z) + ((Algebra.lmul ℂ (ℂ[G]) x) w) := by
              exact LinearMap.map_add (Algebra.lmul ℂ (ℂ[G]) x) z w
      _ = 0 := by
            rw [hzh, hwh]
            simp
  · intro a z hz hzh
    calc
      ((Algebra.lmul ℂ (ℂ[G]) x) (a • z)) = a • ((Algebra.lmul ℂ (ℂ[G]) x) z) := by
        exact LinearMap.map_smul (Algebra.lmul ℂ (ℂ[G]) x) a z
      _ = 0 := by
            rw [hzh]
            simp

/-- Helper for Exercise 12-12.2-4: the explicit `Fin 4`-indexed complex family detects every
element of `ℂ[A₄]`. -/
lemma a4_explicit_familyEndAlgHom_injective
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Function.Injective (familyEndAlgHom (π := a4_explicitComplexFamily eLin)) := by
  intro x y hxy
  have hxy_zero :
      familyEndAlgHom (π := a4_explicitComplexFamily eLin) (x - y) = 0 := by
    simp [map_sub, hxy]
  have hleft_zero : Algebra.lmul ℂ (ℂ[A4]) (x - y) = 0 := by
    letI : Invertible (Nat.card A4 : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
    refine left_mul_eq_zero_of_zero_on_all_simple_submodules (G := A4) ?_
    intro S hS z hz
    let τS : Representation ℂ A4 S := Representation.ofModule' (k := ℂ) (G := A4) S
    have hτS : τS.IsIrreducible := by
      simpa [τS] using ofModule'_isIrreducible_of_isSimpleModule (G := A4) S hS
    letI : τS.IsIrreducible := hτS
    rcases IsCompleteIrreducibleFamily.exists_iso_of_representation
        (π := a4_explicitFDRepFamily eLin)
        (a4_explicit_complex_family_complete eLin) τS inferInstance with ⟨i, hi⟩
    have hslot_zero :
        ((a4_explicitComplexFamily eLin i).ρ).asAlgebraHom (x - y) = 0 := by
      simpa [familyEndAlgHom] using congrFun hxy_zero i
    rcases hi with ⟨eFD⟩
    let e : τS.Equiv ((a4_explicitComplexFamily eLin i).ρ) :=
      Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso eFD)
    have hτS_zero : τS.asAlgebraHom (x - y) = 0 := by
      exact zero_asAlgebraHom_of_equiv_zero e.symm _ hslot_zero
    have hz_zero :
        ((Representation.ofModule' (k := ℂ) (G := A4) S).asAlgebraHom (x - y)) ⟨z, hz⟩ = 0 := by
      simpa [τS] using LinearMap.congr_fun hτS_zero ⟨z, hz⟩
    have hz_val :
        (((Representation.ofModule' (k := ℂ) (G := A4) S).asAlgebraHom (x - y)) ⟨z, hz⟩ : ℂ[A4]) =
          0 := by
      simpa using congrArg Subtype.val hz_zero
    simpa [τS, ofModule'_asAlgebraHom_apply, sub_mul] using hz_val
  exact sub_eq_zero.mp <|
    (Algebra.lmul_injective (R := ℂ) (A := ℂ[A4])) (by simpa using hleft_zero)

/-- Helper for Exercise 12-12.2-4: vanishing of the rational matrix slot forces vanishing on the
complex augmentation constituent. -/
lemma a4_rational_augmentation_slot_zero_implies_complex_augmentation_zero
    (x : ℚ[A4]) (hx : a4_rational_augmentation_matrixAlgHom x = 0) :
    a4_augmentationRepresentation.asAlgebraHom
        (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x) = 0 := by
  -- First forget the chosen basis: the matrix slot is zero exactly when the rational
  -- augmentation action itself is zero.
  have hrational_zero :
      a4_rational_augmentationRepresentation.asAlgebraHom x = 0 := by
    have hx' := hx
    change
      LinearMap.toMatrixAlgEquiv a4_rational_augmentationBasis
          (a4_rational_augmentationRepresentation.asAlgebraHom x) = 0 at hx'
    have hlin :=
      congrArg (Matrix.toLinAlgEquiv a4_rational_augmentationBasis) hx'
    rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at hlin
    have hzero :
        Matrix.toLinAlgEquiv a4_rational_augmentationBasis (0 : Matrix (Fin 3) (Fin 3) ℚ) = 0 := by
      simpa using
        (LinearMap.map_zero (Matrix.toLinAlgEquiv a4_rational_augmentationBasis).toLinearMap)
    rw [hzero] at hlin
    exact hlin
  have hscalar_zero :
      (Representation.scalarExtension a4_rational_augmentationRepresentation).asAlgebraHom
          (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) x) = 0 := by
    -- Scalar extension turns the rational augmentation action into the complexified one.
    rw [scalar_extension_asAlgebraHom_map, hrational_zero]
    simpa using
      (LinearMap.baseChange_zero
        (R := ℚ) (A := ℂ)
        (M := (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule)
        (N := (permutationAugmentationSubrepresentation ℚ A4 (Fin 4)).toSubmodule))
  rcases a4_rational_augmentation_scalarExtension_equiv with ⟨e⟩
  -- Transport the vanishing across the chosen equivalence with the complex augmentation slot.
  exact zero_asAlgebraHom_of_equiv_zero e _ hscalar_zero

/-- Helper for Exercise 12-12.2-4: the only remaining structural step is to prove that the
explicit rational comparison map has zero kernel by comparing its complexification with the
complete complex family `{1, χ, χ̄, ψ}`. -/
lemma a4_rational_decomposition_algHom_injective :
    Function.Injective a4_rational_decomposition_algHom := by
  intro x y hxy
  let z : ℚ[A4] := x - y
  have hz_slots : a4_rational_decomposition_algHom z = 0 := by
    -- Pass to the difference so that all three rational slots vanish simultaneously.
    simp [z, map_sub, hxy]
  have htriv : a4_trivial_algHom z = 0 := by
    simpa [a4_rational_decomposition_algHom] using congrArg Prod.fst hz_slots
  have hcyclo : a4_cyclotomic_algHom z = 0 := by
    simpa [a4_rational_decomposition_algHom] using congrArg (fun t ↦ t.2.1) hz_slots
  have haug : a4_rational_augmentation_matrixAlgHom z = 0 := by
    simpa [a4_rational_decomposition_algHom] using congrArg (fun t ↦ t.2.2) hz_slots
  let eLin : Fin 3 ≃ a4_linearCharacters := by
    -- Choose an ordering of the three linear characters so the complete family is indexed by
    -- `Fin 4`.
    refine (Finite.equivFinOfCardEq (α := a4_linearCharacters) ?_).symm
    exact a4_linearCharacters_card
  have hfamily_zero :
      familyEndAlgHom (π := a4_explicitComplexFamily eLin)
          (MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) z) = 0 := by
    -- Check the four complex irreducible slots one by one.
    ext i v
    fin_cases i
    · simpa [eLin, a4_explicitComplexFamily] using
        LinearMap.congr_fun
          (a4_trivial_and_cyclotomic_zero_implies_all_linear_slots_zero z htriv hcyclo (eLin 0)) v
    · simpa [eLin, a4_explicitComplexFamily] using
        LinearMap.congr_fun
          (a4_trivial_and_cyclotomic_zero_implies_all_linear_slots_zero z htriv hcyclo (eLin 1)) v
    · simpa [eLin, a4_explicitComplexFamily] using
        LinearMap.congr_fun
          (a4_trivial_and_cyclotomic_zero_implies_all_linear_slots_zero z htriv hcyclo (eLin 2)) v
    · simpa [eLin, a4_explicitComplexFamily] using
        LinearMap.congr_fun
          (a4_rational_augmentation_slot_zero_implies_complex_augmentation_zero z haug) v
  have hmap_zero :
      MonoidAlgebra.mapRingHom A4 (algebraMap ℚ ℂ) z = 0 := by
    have hinj_complex :
        Function.Injective (familyEndAlgHom (π := a4_explicitComplexFamily eLin)) :=
      a4_explicit_familyEndAlgHom_injective eLin
    exact hinj_complex (by simpa using hfamily_zero)
  have hz_zero : z = 0 := by
    -- Descend the zero equality coefficientwise through the injective scalar map `ℚ → ℂ`.
    ext g
    have hg0 := congrArg (fun w : ℂ[A4] ↦ w g) hmap_zero
    change algebraMap ℚ ℂ (z g) = 0 at hg0
    exact RingHom.injective (algebraMap ℚ ℂ) (by simpa using hg0)
  exact sub_eq_zero.mp (by simpa [z] using hz_zero)

/- Domain-style sampling for this item:
* `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` is the mathlib
  `core/canonical` Wedderburn-Artin owner for semisimple algebras.
* `Serre.Chap06.Proposition_6_6_2_1.irreducibleFamilyEndAlgEquiv` is the project's explicit
  decomposition owner once a complete irreducible family has been fixed.
* `Serre.Chap12.Corollary_12_12_2_2.IsQuasisplitGroupAlgebra` is derived Chapter 12 input
  controlling why the simple factors of `ℚ[A₄]` split over the stated fields.

This exercise remains `source-facing`: its primitive public data are the stated Artin-Wedderburn
factors themselves. The existential `Nonempty` shape is retained because the source asks for the
existence of an algebra decomposition, not for a canonically distinguished equivalence. -/
-- Proof sketch: by Exercise `12-12.2-3`, every irreducible complex character of `A₄` has
-- Schur index `1`, so Corollary `12-12.2-2` identifies `ℚ[A₄]` as quasisplit. The Chapter 5
-- character table then determines the simple Artin-Wedderburn factors: three one-dimensional
-- components with character field `ℚ(ω) = CyclotomicField 3 ℚ`, grouped as `ℚ × ℚ(ω)`, and one
-- degree-three component giving `M₃(ℚ)`.
/-- Exercise 12-12.2-4: the rational group algebra of `A₄` decomposes as the product of the
trivial factor `ℚ`, the quadratic cyclotomic field `CyclotomicField 3 ℚ = ℚ(ω)`, and the
three-by-three matrix algebra over `ℚ`. -/
theorem a4_rational_group_algebra_decomposition :
    Nonempty
      (ℚ[A4] ≃ₐ[ℚ] ℚ × CyclotomicField 3 ℚ × Matrix (Fin 3) (Fin 3) ℚ) := by
  -- Route correction: the theorem is reduced to the explicit rational comparison map `Φ`.
  let Φ := a4_rational_decomposition_algHom
  have hinj : Function.Injective Φ := a4_rational_decomposition_algHom_injective
  have hdim :
      Module.finrank ℚ ℚ[A4] =
        Module.finrank ℚ (ℚ × CyclotomicField 3 ℚ × Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [a4_groupAlgebra_finrank_twelve, a4_target_finrank_twelve]
  have hsurj : Function.Surjective Φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

end Representation
