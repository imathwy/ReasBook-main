import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2.FiniteRepTensorRing
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1

noncomputable section

universe u

open CategoryTheory
open scoped Representation TensorProduct SubgroupInduction

namespace Representation

section

variable {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G] [Finite G]
variable {ι : Type*} [Fintype ι] (π : ι → FDRep K G)
variable (hpw : PairwiseNonisomorphic π) (hc : IsCompleteIrreducibleFamily π)

omit [CharZero K] [Finite G] in
/-- On a simple class `[V]₀`, the Grothendieck-group character map agrees with the irreducible
character `χ_V ∈ R[K](G)`: both are the underlying function `V.character`. -/
@[simp] lemma finiteRepGrothendieckCharacter_class_irreducibleCharacter
    (V : FDRep K G) [Simple V] :
    finiteRepGrothendieckCharacter K G [V]₀ = FDRep.irreducibleCharacter K V := by
  apply Subtype.ext; funext g
  simp [finiteRepGrothendieckCharacter_class]

include hpw hc in
/-- Over a characteristic-zero field `K`, the Grothendieck-group character map
`R₀[K](G) → R[K](G)` is injective: it sends the simple-class basis (Proposition 14-14.1-1) to the
linearly independent simple characters (Proposition 12-12.1-1), so it has trivial kernel.
(The data of a complete pairwise-nonisomorphic irreducible family witnesses the simple-class
basis; injectivity itself does not depend on the choice.) -/
theorem finiteRepGrothendieckCharacter_injective :
    Function.Injective (finiteRepGrothendieckCharacter K G) := by
  classical
  letI : ∀ i, Simple (π i) := hc.isSimple
  let b := simple_finiteRep_classes_basis_of_complete_family π hpw hc
  have hbi : ∀ i,
      finiteRepGrothendieckCharacter K G (b i) = FDRep.irreducibleCharacter K (π i) := by
    intro i
    rw [simple_finiteRep_classes_basis_of_complete_family_apply]
    exact finiteRepGrothendieckCharacter_class_irreducibleCharacter (π i)
  have hli : LinearIndependent ℤ (fun i ↦ FDRep.irreducibleCharacter K (π i)) :=
    linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
      (π := π) (hπ_simple := hc.isSimple) (hπ_pairwise := hpw)
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro x hx
  have hsum : ∑ i, (b.repr x i) • FDRep.irreducibleCharacter K (π i) = 0 := by
    have hxe : finiteRepGrothendieckCharacter K G x
        = ∑ i, (b.repr x i) • finiteRepGrothendieckCharacter K G (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]; simp only [map_zsmul]
    rw [hx] at hxe
    simp only [hbi] at hxe
    exact hxe.symm
  have hzero : ∀ i, b.repr x i = 0 :=
    Fintype.linearIndependent_iff.mp hli (fun i ↦ b.repr x i) hsum
  rw [← b.sum_repr x]
  simp only [hzero, zero_smul, Finset.sum_const_zero]

include hc in
/-- Over a characteristic-zero field `K`, the Grothendieck-group character map
`R₀[K](G) → R[K](G)` is surjective: by Proposition 12-12.1-1 the irreducible characters of a complete
family span `R[K](G)`, and each such character `χ_{π i}` is the image of the class `[π i]₀`. -/
theorem finiteRepGrothendieckCharacter_surjective :
    Function.Surjective (finiteRepGrothendieckCharacter K G) := by
  classical
  letI : ∀ i, Simple (π i) := hc.isSimple
  intro y
  have hy : y ∈ Submodule.span ℤ (Set.range fun i ↦
      letI := hc.isSimple i; FDRep.irreducibleCharacter K (π i)) := by
    rw [span_irreducible_characters_eq_top_of_complete_family K π hc]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨[π i]₀, by simp⟩
  | zero => exact ⟨0, map_zero _⟩
  | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha; obtain ⟨w, hw⟩ := hb
      exact ⟨x + w, by rw [map_add, hx, hw]⟩
  | smul n a _ ha =>
      obtain ⟨x, hx⟩ := ha
      exact ⟨n • x, by rw [map_zsmul, hx]⟩

include hpw hc in
/-- Over a characteristic-zero field `K`, the Grothendieck-group character map
`R₀[K](G) → R[K](G)` is bijective. -/
theorem finiteRepGrothendieckCharacter_bijective :
    Function.Bijective (finiteRepGrothendieckCharacter K G) :=
  ⟨finiteRepGrothendieckCharacter_injective π hpw hc,
   finiteRepGrothendieckCharacter_surjective π hc⟩

/-- The Grothendieck-group character map packaged as an additive equivalence `R₀[K](G) ≃+ R[K](G)`,
given a complete irreducible family witnessing the simple-class basis. -/
noncomputable def finiteRepGrothendieckCharacterAddEquiv :
    R₀[K](G) ≃+ R[K](G) :=
  AddEquiv.ofBijective (finiteRepGrothendieckCharacter K G)
    (finiteRepGrothendieckCharacter_bijective π hpw hc)

@[simp] theorem finiteRepGrothendieckCharacterAddEquiv_apply (x : R₀[K](G)) :
    finiteRepGrothendieckCharacterAddEquiv π hpw hc x
      = finiteRepGrothendieckCharacter K G x := rfl

end

section

variable {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G] [Finite G]

open MonoidalCategory in
omit [CharZero K] in
/-- The Grothendieck-group character map sends the unit class `1 = [𝟙]₀` to the unit `1` of the
character ring (the constant function `1`): the monoidal unit is the one-dimensional trivial
representation, whose character is constantly `1`. -/
theorem finiteRepGrothendieckCharacter_one :
    finiteRepGrothendieckCharacter K G 1 = 1 := by
  show finiteRepGrothendieckCharacter K G [(𝟙_ (FDRep K G))]₀ = 1
  apply Subtype.ext; funext g
  rw [finiteRepGrothendieckCharacter_class]
  show (𝟙_ (FDRep K G)).character g = ((1 : R[K](G)) : G → K) g
  rw [show ((1 : R[K](G)) : G → K) = (1 : G → K) from rfl]
  simp only [Pi.one_apply]
  have hg1 : (𝟙_ (FDRep K G)).character g = (𝟙_ (FDRep K G)).character 1 := by
    rw [FDRep.character, FDRep.character]; congr 1
  have hfr : Module.finrank K (𝟙_ (FDRep K G)) = 1 := by
    change Module.finrank K K = 1; exact Module.finrank_self K
  rw [hg1, FDRep.char_one, hfr]
  simp

/-- Generator case of `ch ∘ Ind = Ind ∘ ch`: on a class `[V]₀` the Grothendieck-group character
map intertwines subgroup induction on `R₀` with induction on the character ring `R[K]`. The
underlying functions agree because the character of an induced representation is the induced
character (Proposition 7-7.2-1). -/
theorem fdRep_subgroupInduction_character_eq_characterRingOverFieldInduction
    {H : Subgroup G} (V : FDRep K H) :
    finiteRepGrothendieckCharacter K G
        [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
      H.characterRingOverFieldInduction K
        (finiteRepGrothendieckCharacter K H [V]₀) := by
  ext g
  letI : NeZero (Nat.card H : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hpoint :
      finiteRepGrothendieckCharacter K G
          [FDRep.subgroupInduction (k := K) (G := G) V]₀ g =
        (Ind[H]((finiteRepGrothendieckCharacter K H [V]₀ : H → K))) g := by
    calc
      finiteRepGrothendieckCharacter K G
          [FDRep.subgroupInduction (k := K) (G := G) V]₀ g =
          (FDRep.subgroupInduction (k := K) (G := G) V).character g := by
            rw [finiteRepGrothendieckCharacter_class]
      _ = Representation.character (Representation.ind H.subtype V.ρ) g := by rfl
      _ = (Ind[H](V.character)) g := by
          simpa using
            congrFun
              (Subgroup.inducedClassFunction_eq_character_ind
                (H := H) (K := K) V.ρ).symm g
      _ = (Ind[H]((finiteRepGrothendieckCharacter K H [V]₀ : H → K))) g := by
            refine congrArg (fun f : H → K => (Ind[H](f)) g) ?_
            ext h
            simpa using finiteRepGrothendieckCharacter_class (K := K) (G := H) V h
  simpa [Subgroup.characterRingOverFieldInduction_apply] using hpoint

/-- `ch ∘ Ind = Ind ∘ ch`: the Grothendieck-group character map intertwines subgroup induction on
`R₀[K]` with induction on the character ring `R[K]`, for every class `x ∈ R₀[K](H)`.  This is the
keystone for transporting Brauer/Artin induction surjectivity (stated over `R[K]`) back to the
Grothendieck group `R₀[K]`. -/
theorem finiteRepGrothendieckCharacter_subgroupInduction
    (H : Subgroup G) (x : R₀[K](H)) :
    finiteRepGrothendieckCharacter K G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction K H x) =
      H.characterRingOverFieldInduction K
        (finiteRepGrothendieckCharacter K H x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    simpa using
      fdRep_subgroupInduction_character_eq_characterRingOverFieldInduction
        (K := K) (G := G) (H := H) V
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

omit [CharZero K] in
/-- Generator case of multiplicativity: `ch([V]₀ · [W]₀) = ch[V]₀ · ch[W]₀`, because the character
of a tensor product is the product of characters (`FDRep.char_tensor`). -/
theorem finiteRepGrothendieckCharacter_classmul (V W : FDRep K G) :
    finiteRepGrothendieckCharacter K G ([V]₀ * [W]₀)
      = finiteRepGrothendieckCharacter K G [V]₀ * finiteRepGrothendieckCharacter K G [W]₀ := by
  rw [finiteRepGrothendieckClass_mul]
  apply Subtype.ext; funext g
  rw [finiteRepGrothendieckCharacter_class]
  show (MonoidalCategory.tensorObj V W).character g
    = ((finiteRepGrothendieckCharacter K G [V]₀ * finiteRepGrothendieckCharacter K G [W]₀ :
        R[K](G)) : G → K) g
  rw [FDRep.char_tensor]
  show (V.character * W.character) g
    = ((finiteRepGrothendieckCharacter K G [V]₀ : R[K](G)) : G → K) g
      * ((finiteRepGrothendieckCharacter K G [W]₀ : R[K](G)) : G → K) g
  rw [finiteRepGrothendieckCharacter_class, finiteRepGrothendieckCharacter_class]
  rfl

omit [CharZero K] in
/-- The Grothendieck-group character map is multiplicative: `ch(x · y) = ch x · ch y`.  Together
with additivity this makes `ch` a ring homomorphism `R₀[K](G) → R[K](G)`. -/
theorem finiteRepGrothendieckCharacter_mul (x y : R₀[K](G)) :
    finiteRepGrothendieckCharacter K G (x * y)
      = finiteRepGrothendieckCharacter K G x * finiteRepGrothendieckCharacter K G y := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul]
  refine QuotientAddGroup.induction_on x ?_
  intro vx
  refine QuotientAddGroup.induction_on y ?_
  intro vy
  refine FreeAbelianGroup.induction_on vx ?_ ?_ ?_ ?_
  · simp
  · intro V
    refine FreeAbelianGroup.induction_on vy ?_ ?_ ?_ ?_
    · simp
    · intro W
      exact congrArg Subtype.val (finiteRepGrothendieckCharacter_classmul V W)
    · intro W hW
      simp [map_neg, mul_neg, hW]
    · intro W₁ W₂ hW₁ hW₂
      simp [map_add, mul_add, hW₁, hW₂]
  · intro vx hvx
    simp [map_neg, neg_mul, hvx]
  · intro vx₁ vx₂ hvx₁ hvx₂
    simp [map_add, add_mul, hvx₁, hvx₂]

omit [CharZero K] in
/-- Over any field `K`, the Grothendieck-group character map is surjective onto the character ring:
`R[K](G)` is generated as a `ℤ`-algebra by irreducible characters, each of which is `ch [ρ]₀`, and
`ch` is a ring homomorphism.  (No characteristic-zero or complete-family hypothesis is needed.) -/
theorem finiteRepGrothendieckCharacter_surjective' :
    Function.Surjective (finiteRepGrothendieckCharacter K G) := by
  intro y
  obtain ⟨f, hf⟩ := y
  suffices h : ∃ x : R₀[K](G), (finiteRepGrothendieckCharacter K G x : G → K) = f by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Subtype.ext hx⟩
  induction hf using Algebra.adjoin_induction with
  | mem χ hχ =>
      obtain ⟨ρ, hfd, _hirr, rfl⟩ := hχ
      letI : FiniteDimensional K ρ := hfd
      refine ⟨[FDRep.of ρ.ρ]₀, ?_⟩
      funext g
      rw [finiteRepGrothendieckCharacter_class]
      rfl
  | algebraMap r =>
      refine ⟨r • 1, ?_⟩
      rw [map_zsmul, finiteRepGrothendieckCharacter_one]
      ext g
      simp [Algebra.algebraMap_eq_smul_one]
  | add f1 f2 _ _ ih1 ih2 =>
      obtain ⟨x1, hx1⟩ := ih1
      obtain ⟨x2, hx2⟩ := ih2
      refine ⟨x1 + x2, ?_⟩
      rw [map_add]
      ext g
      simp only [Subalgebra.coe_add, Pi.add_apply, hx1, hx2]
  | mul f1 f2 _ _ ih1 ih2 =>
      obtain ⟨x1, hx1⟩ := ih1
      obtain ⟨x2, hx2⟩ := ih2
      refine ⟨x1 * x2, ?_⟩
      rw [finiteRepGrothendieckCharacter_mul]
      ext g
      simp only [Subalgebra.coe_mul, Pi.mul_apply, hx1, hx2]

omit [CharZero K] in
/-- A complete pairwise-nonisomorphic family of simple finite-dimensional representations exists
over any field, indexed by the isomorphism classes of simple objects of `FDRep K G`.  (No
algebraic-closedness or characteristic hypothesis.) -/
theorem exists_complete_family_any_field :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep K G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep K G // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv := ⟨fun a ↦ ⟨Iso.refl _⟩, fun {a b} ⟨e⟩ ↦ ⟨e.symm⟩,
        fun {a b c} ⟨eab⟩ ⟨ebc⟩ ↦ ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep K G := fun q ↦ (Quotient.out q).1
  refine ⟨ι, π, ?_, ?_, ?_⟩
  · intro q q' hqq' ⟨e⟩
    apply hqq'
    calc q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := Quotient.sound ⟨e⟩
      _ = q' := Quotient.out_eq q'
  · intro q; exact (Quotient.out q).2
  · intro τ hτ
    refine ⟨⟦⟨τ, hτ⟩⟧, ?_⟩
    rcases (Quotient.exact (Quotient.out_eq (⟦⟨τ, hτ⟩⟧ : ι))) with ⟨e⟩
    exact ⟨e.symm⟩

/-- Over a characteristic-zero field, the Grothendieck-group character map `R₀[K](G) → R[K](G)` is
bijective, with no externally supplied data: a complete family exists
(`exists_complete_family_any_field`) and is finite (`finite_index_of_complete_pairwiseNonisomorphic`).
Injectivity is the simple-class-basis argument; surjectivity is the family-free ring-homomorphism
argument. -/
theorem finiteRepGrothendieckCharacter_bijective' :
    Function.Bijective (finiteRepGrothendieckCharacter K G) := by
  obtain ⟨ι, π, hpw, hc⟩ := exists_complete_family_any_field (K := K) (G := G)
  letI : Finite ι := finite_index_of_complete_pairwiseNonisomorphic π hpw hc
  letI : Fintype ι := Fintype.ofFinite ι
  exact ⟨finiteRepGrothendieckCharacter_injective π hpw hc,
    finiteRepGrothendieckCharacter_surjective'⟩

/-- The Grothendieck-group character map as an additive equivalence `R₀[K](G) ≃+ R[K](G)` over a
characteristic-zero field (no externally supplied family). -/
noncomputable def finiteRepGrothendieckCharacterAddEquiv' :
    R₀[K](G) ≃+ R[K](G) :=
  AddEquiv.ofBijective (finiteRepGrothendieckCharacter K G)
    finiteRepGrothendieckCharacter_bijective'

@[simp] theorem finiteRepGrothendieckCharacterAddEquiv'_apply (x : R₀[K](G)) :
    finiteRepGrothendieckCharacterAddEquiv' (K := K) (G := G) x
      = finiteRepGrothendieckCharacter K G x := rfl

end

end Representation
