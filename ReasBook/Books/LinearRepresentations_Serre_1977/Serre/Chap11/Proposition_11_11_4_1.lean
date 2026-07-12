import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.RegularOwnerIncidence
import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_2_3
import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_3_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.TensorCharacterBridge
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_3_2

-- Declarations for this item are assembled here from the extracted Proposition 11-11.4-1 API.

universe u v

noncomputable section

open Representation
open Proposition_11_11_4_1
open scoped Pointwise Representation SubgroupInduction TensorProduct

namespace Proposition_11_11_4_1

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [FaithfulSMul A ℂ]

local instance fixedClassEvaluationFintypeGroup : Fintype G := Fintype.ofFinite G
local instance fixedClassEvaluationFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "P0" => tensorCharacterRingZeroPrimeIdeal

/-- Helper for Proposition 11-11.4-1: choose a representative of a conjugacy class. This keeps
the source-side fixed-class evaluation route concrete without unfolding quotient recursion in the
main proofs. -/
def conjClassRepresentative
    (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-1: the chosen representative maps back to the original
conjugacy class. -/
theorem conjClassRepresentative_mk
    (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative (G := G) c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-1: evaluating a realized tensor character at the chosen
representative gives a concrete complex-valued ring hom on `A ⊗ R(G)`. This is the fixed-class
evaluation map used by the source proof. -/
def tensorCharacterRingValueAtConjClassComplex
    (c : ConjClasses G) :
    A ⊗R(G) →+* ℂ where
  toFun χ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ)
      (conjClassRepresentative (G := G) c)
  map_one' := by
    simp [conjClassRepresentative]
  map_mul' χ ψ := by
    simp [conjClassRepresentative]
  map_zero' := by
    simp [conjClassRepresentative]
  map_add' χ ψ := by
    simp [conjClassRepresentative]

/-- Helper for Proposition 11-11.4-1: the fixed-class complex evaluation can be computed at any
representative of the same conjugacy class. -/
theorem tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) {x : G} (hx : ConjClasses.mk x = c) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ =
      ((tensorCharacterRingToSubalgebra A G χ :
          characterRingScalarExtensionSubalgebra A G) : G → ℂ) x := by
  let f : G → ℂ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ)
  have hf : _root_.IsClassFunction f := by
    exact
      isClassFunction_of_mem_characterRingScalarExtension
        (show f ∈ characterRingScalarExtension A G from
          (tensorCharacterRingToSubalgebra A G χ).2)
  have hrepr :
      ConjClasses.mk (conjClassRepresentative (G := G) c) = ConjClasses.mk x := by
    rw [conjClassRepresentative_mk (G := G) c, hx]
  exact hf.eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hrepr)

/-- Helper for Proposition 11-11.4-1: scalar tensors evaluate to the same scalar under the
fixed-class complex evaluation. -/
theorem tensorCharacterRingValueAtConjClassComplex_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c
      ((algebraMap A (A ⊗R(G))) a) = algebraMap A ℂ a := by
  simpa [tensorCharacterRingValueAtConjClassComplex, conjClassRepresentative] using
    congrArg
      (fun f : characterRingScalarExtensionSubalgebra A G ↦
        ((f : G → ℂ) (conjClassRepresentative (G := G) c)))
      ((tensorCharacterRingToSubalgebra A G).commutes a)

/-- Helper for Proposition 11-11.4-1: every value of a virtual character of `G` is an algebraic
integer. This is the light dependency-closed integrality input needed to build the fixed-class
evaluation bridge without importing later Chapter `11` files. -/
theorem characterRing_value_isIntegral_local
    (χ : R(G)) (x : G) :
    IsIntegral ℤ (χ x) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    simpa using Representation.char_isIntegral ρ.ρ x
  · intro n
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ n))
  · intro f g _ _ hf_int hg_int
    exact hf_int.add hg_int
  · intro f g _ _ hf_int hg_int
    exact hf_int.mul hg_int

/- The arithmetic source hypothesis used throughout Proposition 11-11.4-1: the coefficient ring
`A` contains (the image in `ℂ` of) every `Nat.card G`-th root of unity.  This is the exact
hypothesis convention of Theorems 11-11.2-1 / 11-11.2-2, and it makes `A = 𝒪_{ℚ(ζ_{|G|})}` an
admissible coefficient ring.  It replaces the (jointly unsatisfiable) hypothesis
`IsIntegralClosure A ℤ ℂ` of the original development. -/
variable
  (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))

include hroots in
/-- Helper for Proposition 11-11.4-1: the character value of a finite-dimensional representation
already lands in the image of `A`, because it is a sum of `|G|`-th roots of unity controlled by the
arithmetic source hypothesis `hroots`. -/
theorem rep_character_value_mem_range_of_roots
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (s : G) :
    ρ.character s ∈ Set.range (algebraMap A ℂ) := by
  rw [Representation.character,
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  have hsub : ((ρ s).charpoly.roots.sum) ∈ (algebraMap A ℂ).range := by
    refine Subring.multiset_sum_mem _ _ ?_
    intro μ hμ
    rw [RingHom.mem_range]
    have hpow_ord : μ ^ orderOf s = 1 := ρ.charpoly_root_pow_orderOf_eq_one s hμ
    obtain ⟨m, hm⟩ : orderOf s ∣ Nat.card G := orderOf_dvd_natCard s
    have hpowG : μ ^ Nat.card G = 1 := by
      rw [hm, pow_mul, hpow_ord, one_pow]
    have hμ0 : μ ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.card_pos (α := G)).ne'] at hpowG
      exact one_ne_zero hpowG.symm
    have hzpow : (Units.mk0 μ hμ0) ^ Nat.card G = 1 := by
      ext; push_cast; simpa using hpowG
    obtain ⟨a, ha⟩ := hroots (Units.mk0 μ hμ0) hzpow
    exact ⟨a, by simpa using ha⟩
  rw [RingHom.mem_range] at hsub
  exact hsub

include hroots in
/-- Helper for Proposition 11-11.4-1: every value of a virtual character of `G` lands in the image
of `A`.  This is the source bridge previously provided by `IsIntegralClosure.isIntegral_iff`, now
obtained from the arithmetic source hypothesis `hroots`. -/
theorem characterRing_value_mem_range_of_roots
    (χ : R(G)) (s : G) :
    ((χ : G → ℂ) s) ∈ Set.range (algebraMap A ℂ) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    exact rep_character_value_mem_range_of_roots (A := A) (G := G) (hroots := hroots) ρ.ρ s
  · intro n
    exact ⟨(n : A), by simp⟩
  · intro f g _ _ hf hg
    obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by simp only [map_add, ha, hb, Pi.add_apply]⟩
  · intro f g _ _ hf hg
    obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
    exact ⟨a * b, by simp only [map_mul, ha, hb, Pi.mul_apply]⟩

section RealizationInjectivityFaithful

open CategoryTheory

/-- Helper for Proposition 11-11.4-1 (FaithfulSMul rederivation of Lemma 10-10.2-3): every finite
group admits a finite complete pairwise nonisomorphic family of irreducible complex
representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family_faithful :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (Representation.leftRegular ℂ G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ i).toSubmodule)
              ((σ i).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := Representation.leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : CategoryTheory.Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact Representation.FDRep.simple_of_isIrreducible (π q)
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := hπ_simple
        exists_iso := ?_ }
    intro τ _
    let τρ := τ.ρ
    have hτ_irreducible : Representation.IsIrreducible τρ := by
      exact Representation.FDRep.isIrreducible_of_simple τ
    letI : Representation.IsIrreducible τρ := hτ_irreducible
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero τ hzero
    letI : Nontrivial τ := hτ_nontriv
    have hτ_pos : 0 < Module.finrank ℂ τ := Module.finrank_pos
    have hτ_mult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank ℂ τ := by
      simpa [τρ] using
        Representation.leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr τρ
          inferInstance
    have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
      rw [hτ_mult]
      exact hτ_pos
    obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
    let q : ι := ⟦j⟧
    rcases hjτ with ⟨eτ⟩
    rcases Quotient.exact (Quotient.out_eq q) with ⟨eqj⟩
    refine ⟨q, ?_⟩
    exact ⟨(eτ.symm.trans eqj.symm).toFDRepIso⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

omit [FaithfulSMul A ℂ] in
/-- Helper for Proposition 11-11.4-1: the normalized character pairing expands over finite
`A`-linear combinations. -/
private theorem groupFunctionPairing_sum_algebra_smul_left_faithful
    {ι : Type*} (s : Finset ι) (a : ι → A) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, algebraMap A ℂ (a j) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      have hsmul : (a i • χ i : G → ℂ) = algebraMap A ℂ (a i) • χ i := by
        ext g
        simp [Algebra.smul_def, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Proposition 11-11.4-1: a finite `A`-linear combination of the characters of a
complete pairwise nonisomorphic irreducible family can vanish only if every coefficient is zero.
This is the FaithfulSMul rederivation of Lemma 10-10.2-3's coefficient-vanishing lemma. -/
private lemma irreducible_character_coefficients_eq_zero_faithful
    {ι : Type*}
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : ι →₀ A)
    (hc : c.sum (fun i a ↦ a • (π i).character) = 0) :
    c = 0 := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : ℂ) :=
    Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  ext i
  have hpair0 :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ = (0 : ℂ) := by
    simpa [Representation.groupFunctionPairingOverField] using
      congrArg (fun φ : G → ℂ ↦ Representation.groupFunctionPairingOverField ℂ φ (π i).character) hc
  have hpair_expand :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ =
        c.sum (fun j a ↦ algebraMap A ℂ a * ⟪(π j).character, (π i).character⟫) := by
    simpa [Finsupp.sum] using
      (groupFunctionPairing_sum_algebra_smul_left_faithful (A := A) (G := G)
        (s := c.support) (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character))
  rw [hpair_expand] at hpair0
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : ℂ) := by
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    let X : Rep ℂ G := (CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (π i)
    let e₁ : ((π i) ⟶ (π i)) ≃ₗ[ℂ] (X ⟶ X) :=
      (FDRep.forget₂HomLinearEquiv (π i) (π i)).symm
    let e₂ : (X ⟶ X) ≃ₗ[ℂ] (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
    let e : ((π i) ⟶ (π i)) ≃ₗ[ℂ] (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      e₁.trans e₂
    letI : FiniteDimensional ℂ (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
    have hnontriv : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      refine ⟨0, e (𝟙 (π i)), ?_⟩
      intro h
      apply CategoryTheory.id_nonzero (π i)
      exact e.injective h.symm
    letI : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := hnontriv
    have hpair :
        ⟪(π i).character, (π i).character⟫ =
          Module.finrank ℂ (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        ℂ (π i).ρ (π i).ρ
    rw [hpair]
    exact_mod_cast Module.finrank_pos.ne'
  have hpair_single :
      c.sum (fun j a ↦ algebraMap A ℂ a * ⟪(π j).character, (π i).character⟫) =
        algebraMap A ℂ (c i) * ⟪(π i).character, (π i).character⟫ := by
    rw [Finsupp.sum]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hi
      by_cases hci : c i = 0
      · simp [hci]
      · exact (hi (Finsupp.mem_support_iff.2 hci)).elim
  rw [hpair_single] at hpair0
  have hcoeffC : algebraMap A ℂ (c i) = 0 :=
    (mul_eq_zero.mp hpair0).resolve_right hself_ne
  have hcoeffA : c i = 0 := by
    exact (FaithfulSMul.algebraMap_injective A ℂ) <| by
      simpa using hcoeffC
  simpa using hcoeffA

omit [FaithfulSMul A ℂ] in
/-- Helper for Proposition 11-11.4-1: realizing a basis expansion in `A ⊗ R(G)` evaluates
coefficientwise. -/
private lemma tensorCharacterRingToFunction_finsupp_sum_faithful
    {ι : Type*} (b : Module.Basis ι ℤ (R(G))) (c : ι →₀ A) :
    ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : A ⊗R(G)) : G → ℂ) =
      c.sum fun i a ↦ a • (((b i : R(G)) : G → ℂ)) := by
  classical
  simp [Finsupp.sum, map_sum]

/-- Helper for Proposition 11-11.4-1: the ambient realization of `A ⊗ R(G)` as complex-valued
functions is injective, using only `FaithfulSMul A ℂ` (the de-vacuumed replacement for the
`IsIntegralClosure`-based Lemma 10-10.2-3). -/
theorem tensorCharacterRingToFunction_injective_faithful :
    Function.Injective (fun χ : A ⊗R(G) ↦ ((χ : G → ℂ))) := by
  classical
  intro ξ η hξη
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family_faithful (G := G)
  letI : Fintype ι := hι
  let b := Representation.irreducible_characters_basis_of_complete_family
    ℂ π hπ_pairwise hπ_complete
  have hdiff : ((ξ - η : A ⊗R(G)) : G → ℂ) = 0 := by
    have hsub := congrArg (fun z : G → ℂ ↦ z - ((η : A ⊗R(G)) : G → ℂ)) hξη
    simpa [map_sub] using hsub
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (R := ℤ) (M := A) (𝒞 := b) (x := ξ - η)
  have hrealized :
      c.sum (fun i a ↦ a • (π i).character) = 0 := by
    have hsum := tensorCharacterRingToFunction_finsupp_sum_faithful (A := A) (G := G) b c
    have hsum' :
        ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : A ⊗R(G)) : G → ℂ) =
          c.sum (fun i a ↦ a • (π i).character) := by
      simpa [b, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using hsum
    rw [← hsum', hc, hdiff]
  have hc_zero : c = 0 :=
    irreducible_character_coefficients_eq_zero_faithful
      (A := A) (G := G) π hπ_pairwise hπ_complete c hrealized
  have hξη' : ξ - η = 0 := by
    rw [← hc, hc_zero]
    simp
  exact sub_eq_zero.mp hξη'

end RealizationInjectivityFaithful

section IntegralClosureFixedClassEvaluation

include hroots in
/-- Helper for Proposition 11-11.4-1: evaluating an integral character at a representative of `c`
already lands in the arithmetic coefficient ring `A`. This is the coefficient-side source bridge
for the fixed-class evaluation map. -/
theorem characterRingValueAtConjClass_mem_range
    (c : ConjClasses G) (χ : R(G)) :
    (χ (conjClassRepresentative (G := G) c) : ℂ) ∈ Set.range (algebraMap A ℂ) :=
  characterRing_value_mem_range_of_roots (A := A) (G := G) (hroots := hroots) χ
    (conjClassRepresentative (G := G) c)

include hroots in
/-- Helper for Proposition 11-11.4-1: evaluation on the chosen representative lifts from the
ordinary character ring `R(G)` to an `A`-valued algebra map. -/
def characterRingValueAtConjClass
    (c : ConjClasses G) :
    R(G) →ₐ[ℤ] A where
  toFun χ := Classical.choose (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)
  map_zero' := by
    apply FaithfulSMul.algebraMap_injective A ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c 0))
  map_one' := by
    apply FaithfulSMul.algebraMap_injective A ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c 1))
  map_add' χ ψ := by
    apply FaithfulSMul.algebraMap_injective A ℂ
    have hχ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)
    have hψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)
    have hχψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c (χ + ψ))
    calc
      algebraMap A ℂ
          (Classical.choose
            (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c (χ + ψ))) =
          (χ + ψ) (conjClassRepresentative (G := G) c) := hχψ
      _ = χ (conjClassRepresentative (G := G) c) +
            ψ (conjClassRepresentative (G := G) c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)) +
          algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ) +
              Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)) := by
            rw [map_add]
  map_mul' χ ψ := by
    apply FaithfulSMul.algebraMap_injective A ℂ
    have hχ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)
    have hψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)
    have hχψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c (χ * ψ))
    calc
      algebraMap A ℂ
          (Classical.choose
            (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c (χ * ψ))) =
          (χ * ψ) (conjClassRepresentative (G := G) c) := hχψ
      _ = χ (conjClassRepresentative (G := G) c) *
            ψ (conjClassRepresentative (G := G) c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)) *
          algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ) *
              Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c ψ)) := by
            rw [map_mul]
  commutes' n := by
    apply FaithfulSMul.algebraMap_injective A ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c
          (algebraMap ℤ (R(G)) n)))

include hroots in
/-- Helper for Proposition 11-11.4-1: after scalar extension to `ℂ`, the `A`-valued evaluation on
`R(G)` agrees with ordinary character evaluation at the chosen representative of `c`. -/
theorem characterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (χ : R(G)) :
    algebraMap A ℂ (characterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ) =
      (χ (conjClassRepresentative (G := G) c) : ℂ) :=
  Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) (hroots := hroots) (G := G) c χ)

include hroots in
/-- Helper for Proposition 11-11.4-1: tensoring the identity on `A` with fixed-class evaluation on
`R(G)` gives an `A`-valued evaluation map on `A ⊗ R(G)`. -/
def tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    A ⊗R(G) →ₐ[ℤ] A :=
  Algebra.TensorProduct.productMap
    (AlgHom.id ℤ A)
    (characterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c)

include hroots in
/-- Helper for Proposition 11-11.4-1: the tensor-product evaluation sends a scalar tensor to the
same scalar in `A`. -/
theorem tensorCharacterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c
      ((algebraMap A (A ⊗R(G))) a) = a := by
  simp [tensorCharacterRingValueAtConjClass]

include hroots in
/-- Helper for Proposition 11-11.4-1: after applying `A → ℂ`, the `A`-valued tensor-product
evaluation becomes the corresponding complex evaluation at the chosen representative. -/
theorem tensorCharacterRingValueAtConjClass_complex_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) :
    algebraMap A ℂ (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ) =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ := by
  let f : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := (algebraMap A ℂ).comp
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c).toRingHom
      commutes' := by
        intro a
        exact congrArg (algebraMap A ℂ)
          (tensorCharacterRingValueAtConjClass_algebraMap (A := A) (hroots := hroots) (G := G) c a) }
  let g : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c
      commutes' := tensorCharacterRingValueAtConjClassComplex_algebraMap (A := A) (G := G) c }
  have hright :
      (AlgHom.restrictScalars ℤ f).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) =
        (AlgHom.restrictScalars ℤ g).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) := by
    ext ψ
    simp [f, g, tensorCharacterRingValueAtConjClass,
      characterRingValueAtConjClass_algebraMap]
    simpa [tensorCharacterRingToSubalgebra] using
      (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
        (A := A) (G := G) c
        ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) ψ)
        (conjClassRepresentative_mk (G := G) c)).symm
  have hfg : f = g := Algebra.TensorProduct.ext_ring hright
  exact congrArg (fun h : A ⊗R(G) →ₐ[A] ℂ ↦ h χ) hfg

end IntegralClosureFixedClassEvaluation

/-- Helper for Proposition 11-11.4-1: Serre's zero prime `P₀,c` is the kernel of the concrete
fixed-class evaluation map at any representative of `c`. This is the source-facing identification
used when reducing the zero branch to coordinate kernels. -/
theorem tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex
    (c : ConjClasses G) :
    tensorCharacterRingZeroPrimeIdealEval (A := A) (G := G) c =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c := by
  apply RingHom.ext
  intro z
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c
  calc
    tensorCharacterRingZeroPrimeIdealEval A c z =
        ((tensorCharacterRingToSubalgebra A G z :
            characterRingScalarExtensionSubalgebra A G) : G → ℂ) x := by
              rw [show c = ConjClasses.mk x by symm; exact hx]
              rfl
    _ = tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c z := by
          symm
          exact
            tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
              (A := A) (G := G) c z hx

section SourceValueProfile

variable [IsDomain A] [Ring.HasFiniteQuotients A]

include hroots in
/-- Helper for Proposition 11-11.4-1: when fixed-class evaluation already lands in the integral
closure ring `A`, the zero point of `Spec A` pulls back exactly to the public zero owner `P₀,c`.
This is the source-faithful normalization step behind the discarded stronger zero-branch route. -/
theorem zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c)
      ⟨(⊥ : Ideal A), inferInstance⟩ =
        tensorCharacterRingZeroPrimeIdeal (A := A) (G := G) c := by
  apply PrimeSpectrum.ext
  ext χ
  change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ = 0 ↔
    tensorCharacterRingZeroPrimeIdealEval A c χ = 0
  constructor
  · intro hχ
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex (A := A) (G := G) c,
      ← tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) c]
    simpa [hχ]
  · intro hχ
    apply FaithfulSMul.algebraMap_injective A ℂ
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex (A := A) (G := G) c,
      ← tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) c] at hχ
    simpa using hχ

include hroots in
/-- Helper for Proposition 11-11.4-1: every fixed-class evaluation pullback contracts to the
source prime used on the coefficient ring. This is the scalar normalization needed before the
zero and nonzero branches can both read off the coefficient prime from the same source
presentation. -/
theorem value_comap_eq_source_prime
    (c : ConjClasses G) (q : PrimeSpectrum A) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
        (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c) q).asIdeal =
      q.asIdeal := by
  ext a
  change
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c
        ((algebraMap A (A ⊗R(G))) a) ∈ q.asIdeal ↔
      a ∈ q.asIdeal
  rw [tensorCharacterRingValueAtConjClass_algebraMap (A := A) (hroots := hroots) (G := G) c a]

include hroots in
/-- Helper for Proposition 11-11.4-1: bundle the fixed-class evaluations into Serre's source
map `A ⊗ R(G) → A^{Cl(G)}`. This is the governing source object for Proposition `30`, and it
keeps the later prime-classification step on the source route instead of returning to fiber
transport packages. -/
noncomputable def tensorCharacterRingValueProfile :
    A ⊗R(G) →ₐ[A] (ConjClasses G → A) where
  toFun χ c := tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ
  map_one' := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_mul' χ ψ := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_zero' := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_add' χ ψ := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  commutes' a := by
    ext c
    simpa using
      tensorCharacterRingValueAtConjClass_algebraMap (A := A) (hroots := hroots) (G := G) c a

include hroots in
/-- Helper for Proposition 11-11.4-1: the source map evaluates pointwise to the chosen fixed-class
evaluation. This keeps later `rw` steps on the explicit source presentation. -/
@[simp] theorem tensorCharacterRingValueProfile_apply
    (χ : A ⊗R(G)) (c : ConjClasses G) :
    tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G) χ c =
      tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c χ :=
  rfl

/-- Helper for Proposition 11-11.4-1: the point-mass function at a conjugacy class in Serre's
source ring `A^{Cl(G)}`. This is the idempotent source generator used in the lying-over pivot. -/
noncomputable def conjClassDelta
    (c : ConjClasses G) : ConjClasses G → A :=
  fun d ↦
    let _ : DecidableEq (ConjClasses G) := Classical.decEq _
    if d = c then 1 else 0

/-- Helper for Proposition 11-11.4-1: each source point mass is an idempotent in
`A^{Cl(G)}`. This is the key source-side integrality input for the intended lying-over proof. -/
theorem conjClassDelta_mul_self
    (c : ConjClasses G) :
    conjClassDelta (A := A) (G := G) c * conjClassDelta (A := A) (G := G) c =
      conjClassDelta (A := A) (G := G) c := by
  ext d
  classical
  by_cases hd : d = c
  · simp [conjClassDelta, hd]
  · simp [conjClassDelta, hd]

/-- Helper for Proposition 11-11.4-1: the source point masses span the full function ring on
conjugacy classes. This makes the intended source-spectrum proof reduce to adjoining finitely many
idempotents to the image of the source map. -/
theorem sum_smul_conjClassDelta_eq
    (F : ConjClasses G → A) :
    (∑ c : ConjClasses G, F c • conjClassDelta (A := A) (G := G) c) = F := by
  funext d
  classical
  simp [conjClassDelta]

include hroots in
/-- Helper for Proposition 11-11.4-1: each source point mass is integral over the image of
Serre's source profile map. This is the idempotent input for the lying-over step on
`A^{Cl(G)}`. -/
theorem conjClassDelta_isIntegral_over_valueProfile
    (c : ConjClasses G) :
    ((tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)).toRingHom).IsIntegralElem
      (conjClassDelta (A := A) (G := G) c) := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A ⊗R(G))), ?_, ?_⟩
  · simpa using
      (Polynomial.monic_X.mul
        (Polynomial.monic_X_sub_C (1 : A ⊗R(G))))
  · simp [conjClassDelta_mul_self, sub_eq_add_neg, mul_add]

include hroots in
/-- Helper for Proposition 11-11.4-1: Serre's source profile map
`A ⊗ R(G) → A^{Cl(G)}` is injective. This is the exact missing hypothesis needed to apply
lying-over to the source inclusion and keep the proof on Serre's source spectrum
`Spec(A^{Cl(G)}) → Spec(A ⊗ R(G))`. -/
theorem tensorCharacterRingValueProfile_injective :
    Function.Injective (tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)) := by
  intro χ ψ hχψ
  apply tensorCharacterRingToFunction_injective_faithful (A := A) (G := G)
  ext g
  have hclass :
      tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G) χ (ConjClasses.mk g) =
        tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G) ψ (ConjClasses.mk g) :=
    congrFun hχψ (ConjClasses.mk g)
  have hclass_complex := congrArg (algebraMap A ℂ) hclass
  rw [tensorCharacterRingValueProfile_apply (A := A) (hroots := hroots) (G := G) χ (ConjClasses.mk g),
    tensorCharacterRingValueProfile_apply (A := A) (hroots := hroots) (G := G) ψ (ConjClasses.mk g)] at hclass_complex
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) (ConjClasses.mk g) χ,
    tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) (ConjClasses.mk g) ψ] at hclass_complex
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
      (ConjClasses.mk g) χ rfl,
    tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
      (ConjClasses.mk g) ψ rfl] at hclass_complex
  simpa using hclass_complex

include hroots in
/-- Helper for Proposition 11-11.4-1: Serre's source profile map
`A ⊗ R(G) → A^{Cl(G)}` is integral. This is the source-faithful bridge from the tensor character
ring to the function ring on conjugacy classes. -/
theorem tensorCharacterRingValueProfile_isIntegral :
    RingHom.IsIntegral (tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)).toRingHom := by
  let f : A ⊗R(G) →+* (ConjClasses G → A) :=
    (tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)).toRingHom
  intro F
  let s : Finset (ConjClasses G) := Finset.univ
  have hsum :
      f.IsIntegralElem
        (s.sum fun c =>
          f ((algebraMap A (A ⊗R(G))) (F c)) *
            conjClassDelta (A := A) (G := G) c) := by
    classical
    refine Finset.induction_on (s := s) ?_ ?_
    · simpa using RingHom.isIntegralElem_zero f
    · intro c s hc hs
      rw [Finset.sum_insert hc]
      have hscalar :
          f.IsIntegralElem (f ((algebraMap A (A ⊗R(G))) (F c))) :=
        RingHom.isIntegralElem_map f
      have hterm :
          f.IsIntegralElem
            (f ((algebraMap A (A ⊗R(G))) (F c)) *
              conjClassDelta (A := A) (G := G) c) :=
        hscalar.mul f (conjClassDelta_isIntegral_over_valueProfile (A := A) (hroots := hroots) (G := G) c)
      exact hterm.add f hs
  have hrewrite :
      (s.sum fun c =>
        f ((algebraMap A (A ⊗R(G))) (F c)) *
          conjClassDelta (A := A) (G := G) c) = F := by
    calc
      (s.sum fun c =>
        f ((algebraMap A (A ⊗R(G))) (F c)) *
          conjClassDelta (A := A) (G := G) c)
          =
        (s.sum fun c =>
          F c • conjClassDelta (A := A) (G := G) c) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            ext d
            have hconst :
                f ((algebraMap A (A ⊗R(G))) (F c)) d = F c := by
              simpa [f, tensorCharacterRingValueProfile] using
                tensorCharacterRingValueAtConjClass_algebraMap
                  (A := A) (hroots := hroots) (G := G) d (F c)
            calc
              (f ((algebraMap A (A ⊗R(G))) (F c)) *
                  conjClassDelta (A := A) (G := G) c) d
                  =
                f ((algebraMap A (A ⊗R(G))) (F c)) d *
                  conjClassDelta (A := A) (G := G) c d := by
                    rfl
              _ = F c * conjClassDelta (A := A) (G := G) c d := by rw [hconst]
              _ = (F c • conjClassDelta (A := A) (G := G) c) d := by
                    simp [Algebra.smul_def]
      _ = F := by
            simpa [s] using sum_smul_conjClassDelta_eq (A := A) (G := G) F
  exact hrewrite ▸ hsum

include hroots in
/-- Helper for Proposition 11-11.4-1: evaluating Serre's source profile at a fixed conjugacy
class recovers the corresponding fixed-class evaluation map. This keeps the source-spectrum proof
as a direct comap computation instead of a transport argument. -/
theorem evalRingHom_comp_tensorCharacterRingValueProfile
    (d : ConjClasses G) :
    (Pi.evalRingHom (fun _ : ConjClasses G ↦ A) d).comp
        (tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)).toRingHom =
      (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d).toRingHom := by
  rfl

include hroots in
/-- Helper for Proposition 11-11.4-1: every ambient prime should be presented directly as the
pullback of a coefficient prime along fixed-class evaluation. This is Serre's actual source map
`Spec(A^{Cl(G)}) → Spec(A ⊗ R(G))`, and replacing the old fiber packages by this theorem is the
main structural pivot for Proposition `30`. -/
theorem source_prime_eq_value_comap_of_class
    (𝔭 : PrimeSpectrum (A ⊗R(G))) :
    ∃ (d : ConjClasses G) (q : PrimeSpectrum A),
      PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d) q = 𝔭 := by
  let f : A ⊗R(G) →+* (ConjClasses G → A) :=
    (tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G)).toRingHom
  obtain ⟨Q, hQ⟩ :=
    RingHom.IsIntegral.comap_surjective
      (f := f)
      (tensorCharacterRingValueProfile_isIntegral (A := A) (hroots := hroots) (G := G))
      (tensorCharacterRingValueProfile_injective (A := A) (hroots := hroots) (G := G))
      𝔭
  obtain ⟨d, q, hdq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (R := fun _ : ConjClasses G ↦ A) Q
  refine ⟨d, q, ?_⟩
  have hcomp :
      PrimeSpectrum.comap
          (((Pi.evalRingHom (fun _ : ConjClasses G ↦ A) d)).comp f) q = 𝔭 := by
    simpa [hdq] using hQ
  simpa [f, evalRingHom_comp_tensorCharacterRingValueProfile (A := A) (hroots := hroots) (G := G) d] using hcomp

include hroots in
/-- Helper for Proposition 11-11.4-1: once an ambient prime is known to contract to the fixed
maximal ideal `M`, Serre's source-spectrum presentation can be normalized so that the coefficient
prime in the fixed-class evaluation pullback is exactly `M`. This is the source-faithful wrapper
needed before attaching the `p`-regular owner class to the presentation. -/
theorem source_prime_eq_value_comap_of_class_over_fixed_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : PrimeSpectrum (A ⊗R(G))}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = M.1.asIdeal) :
    ∃ d : ConjClasses G,
      PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) = 𝔭 := by
  obtain ⟨d, q, hq⟩ :=
    source_prime_eq_value_comap_of_class (A := A) (hroots := hroots) (G := G) 𝔭
  have hqIdeal : q.asIdeal = M.1.asIdeal := by
    calc
      q.asIdeal =
          Ideal.comap (algebraMap A (A ⊗R(G)))
            (PrimeSpectrum.comap
              (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d) q).asIdeal := by
                symm
                exact value_comap_eq_source_prime (A := A) (hroots := hroots) (G := G) d q
      _ =
          Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
            simpa [hq]
      _ = M.1.asIdeal := h𝔭
  have hqEq : q = (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    simpa using hqIdeal
  refine ⟨d, ?_⟩
  simpa [hqEq] using hq

include hroots in
/-- Helper for Proposition 11-11.4-1: under the integral-closure hypothesis, the zero branch is
already a formal corollary of the source-spectrum presentation. This records the exact reduction
proved by the source route, even though the public zero-branch theorem below still needs a
coefficient-descent-free bridge to avoid adding `[IsIntegralClosure A ℤ ℂ]` to its statement. -/
theorem zero_fiber_prime_classification_over_bot_of_source_presentation
    {𝔭 : PrimeSpectrum (A ⊗R(G))}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥) :
    ∃ c : ConjClasses G, P0 A c = 𝔭 := by
  obtain ⟨c, q, hq⟩ :=
    source_prime_eq_value_comap_of_class (A := A) (hroots := hroots) (G := G) 𝔭
  have hqbotIdeal : q.asIdeal = ⊥ := by
    calc
      q.asIdeal =
          Ideal.comap (algebraMap A (A ⊗R(G)))
            (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c) q).asIdeal := by
              symm
              exact value_comap_eq_source_prime (A := A) (hroots := hroots) (G := G) c q
      _ =
          Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
            simpa [hq]
      _ = ⊥ := h𝔭
  have hqbot : q = ⟨(⊥ : Ideal A), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  refine ⟨c, ?_⟩
  calc
    P0 A c =
        PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c)
          ⟨(⊥ : Ideal A), inferInstance⟩ := by
            symm
            exact zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
              (A := A) (hroots := hroots) (G := G) c
    _ =
        PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) c) q := by
          simpa [hqbot]
    _ = 𝔭 := hq

end SourceValueProfile

end

end Proposition_11_11_4_1

-- The cyclic `p^k`-power congruence helpers (`exists_p_power_eq_pRegularComponent_pow`,
-- `quotient_span_prime_charP`, `exists_linear_character_of_irreducible_rep`,
-- `exists_lifts_of_linear_character_values_with_pow_eq`, `cyclic_character_qpow_quotient_eq`,
-- `tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension`,
-- `int_modEq_of_qpow_quotient_eq_mod_p`) previously declared here now live verbatim in
-- `Serre.Chap10.Lemma_10_10_3_2`, which reaches this file through
-- `Serre.Chap10.Lemma_10_10_2_3 → Theorem_10_10_2_1 → Theorem_10_10_2_1.PRegularEndgame`;
-- keeping local copies would clash with those public declarations.

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
variable [Algebra A ℂ] [FaithfulSMul A ℂ]
variable
  (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))

local notation "SpecARG" => PrimeSpectrum (A ⊗R(G))

/-- Helper for Proposition 11-11.4-1: every nonzero prime of the arithmetic coefficient ring is
one of the residual-characteristic maximal ideals indexing Serre's regular branch. -/
theorem nonzero_primeSpectrum_eq_residual_maximal
    (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
      M.1.asIdeal = q.asIdeal := by
  -- A nonzero prime becomes maximal because every nonzero quotient of `A` is finite.
  letI : q.asIdeal.IsMaximal :=
    Ring.HasFiniteQuotients.maximalOfPrime hq
  have hfiniteQuot : Finite (A ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Finite (A ⧸ q.asIdeal) := hfiniteQuot
  -- The residue field is finite, so its characteristic is a genuine prime number.
  have hfiniteResidue : Finite q.asIdeal.ResidueField := by
    exact Finite.of_surjective
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective
  letI : Finite q.asIdeal.ResidueField := hfiniteResidue
  let p : Nat.Primes :=
    ⟨ringChar q.asIdeal.ResidueField, CharP.prime_ringChar q.asIdeal.ResidueField⟩
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨q.asIdeal, inferInstance⟩, hq, by
      simpa [p] using
        (inferInstance : CharP q.asIdeal.ResidueField (ringChar q.asIdeal.ResidueField))⟩
  -- The packaged maximal ideal is definitionally the original prime ideal.
  exact ⟨p, M, rfl⟩

include hroots in
/-- Helper for Proposition 11-11.4-1: the source-spectrum route already classifies every prime of
`A ⊗ R(G)` into the zero branch or into a fixed-class evaluation pullback over a residual
maximal ideal. This is the verified prefix of Serre's proof before the remaining regular-branch
owner identification is applied. -/
theorem tensor_character_ring_prime_ideal_source_presentation
    (𝔭 : SpecARG) :
    (∃ c : ConjClasses G, tensorCharacterRingZeroPrimeIdeal A c = 𝔭) ∨
      ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
        ∃ d : ConjClasses G,
          PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) = 𝔭 := by
  by_cases h𝔭 :
      Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥
  · left
    -- The zero-contraction branch is already handled by the extracted source-presentation theorem.
    exact
      zero_fiber_prime_classification_over_bot_of_source_presentation
        (A := A) (hroots := hroots) (G := G) h𝔭
  · right
    let q : PrimeSpectrum A :=
      PrimeSpectrum.comap (algebraMap A (A ⊗R(G))) 𝔭
    have hq : q.asIdeal ≠ ⊥ := by
      -- The negated zero branch says exactly that the contracted coefficient prime is nonzero.
      simpa [q] using h𝔭
    obtain ⟨p, M, hM⟩ :=
      nonzero_primeSpectrum_eq_residual_maximal (A := A) q hq
    have hcontract :
        Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = M.1.asIdeal := by
      -- Re-express the contracted prime using the packaged residual-characteristic maximal ideal.
      simpa [q] using hM.symm
    obtain ⟨d, q', hq'⟩ :=
      source_prime_eq_value_comap_of_class (A := A) (hroots := hroots) (G := G) 𝔭
    have hqIdeal : q'.asIdeal = M.1.asIdeal := by
      calc
        q'.asIdeal =
            Ideal.comap (algebraMap A (A ⊗R(G)))
              (PrimeSpectrum.comap
                (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d) q').asIdeal := by
                  symm
                  exact value_comap_eq_source_prime (A := A) (hroots := hroots) (G := G) d q'
        _ = Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
              simpa [hq']
        _ = M.1.asIdeal := hcontract
    have hqEq : q' = (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      simpa using hqIdeal
    -- This is the exact nonzero branch that remains to be identified with Serre's indexed
    -- regular owner `P_{M,c}`.
    exact ⟨p, M, d, by simpa [hqEq] using hq'⟩

include hroots in
/-- Helper for Proposition 11-11.4-1: evaluating at a fixed conjugacy class and then contracting
back to `A` recovers the chosen residual-characteristic maximal ideal. This is the easy scalar
half of the nonzero source branch. -/
theorem value_comap_eq_fixed_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
        (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
          (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal =
      M.1.asIdeal := by
  -- The fixed-class evaluation fixes scalar tensors, so the source prime contracts back to `M`.
  simpa using
    value_comap_eq_source_prime (A := A) (hroots := hroots) (G := G) d
      (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)

include hroots in
/-- Helper for Proposition 11-11.4-1: a pure induction generator belongs to the evaluation
pullback prime over `M` exactly when its fixed-class value lies in `M`. This is the stable
rewrite needed before the regular-owner criterion can be applied. -/
theorem induction_generator_mem_value_comap_iff
    (M : MaximalSpectrum A) (d : ConjClasses G) (H : Subgroup G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction_local χ)) ∈
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
        (⟨M.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal ↔
        characterRingValueAtConjClass (A := A) (hroots := hroots) d
          (H.characterRingInduction_local χ) ∈ M.asIdeal := by
  -- Membership in a prime comap is definitionally membership of the evaluated image.
  change
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction_local χ)) ∈ M.asIdeal ↔
      _
  -- On pure tensors from the character-ring factor, the tensor evaluator is the fixed-class value.
  simp [tensorCharacterRingValueAtConjClass]

/-- Helper for Proposition 11-11.4-1: if the owner class of `d` has no associated
`p`-elementary subgroup inside `H`, then no conjugate of any associated subgroup built from a
representative of that owner can lie inside `H`. This is the exact hypothesis shape required by
Theorem `11-11.3-2`. -/
theorem no_conjugate_associated_subgroup_of_not_hasAssociated_owner
    (p : Nat.Primes) (H : Subgroup G) (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)))
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup (p : ℕ) x P ≤ H := by
  intro g hg
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  let P' :
      Sylow (p : ℕ) (Subgroup.centralizer ({MulAut.conj g x} : Set G)) :=
    P.mapSurjective
      (show Function.Surjective
          (Proposition_11_11_4_1.centralizer_conj_equiv (G := G) g x).toMonoidHom from
        (Proposition_11_11_4_1.centralizer_conj_equiv (G := G) g x).surjective)
  have hxg :
      MulAut.conj g x ∈ ((owner : PRegularConjClass G p) : ConjClasses G).carrier := by
    -- Conjugating a representative stays inside the same owner conjugacy class.
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    calc
      ConjClasses.mk (MulAut.conj g x) = ConjClasses.mk x := by
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr
          (isConj_iff.mpr ⟨g⁻¹, by simp [MulAut.conj_apply, mul_assoc]⟩)
      _ = ((owner : PRegularConjClass G p) : ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hmap :
      Subgroup.map (MulAut.conj g).toMonoidHom
          (associatedPElementarySubgroup (p : ℕ) x P) ≤ H := by
    simpa using hg
  have htransport :
      associatedPElementarySubgroup (p : ℕ) (MulAut.conj g x) P' ≤ H := by
    -- The stable conjugation-transport lemma rewrites the given subgroup inclusion into the
    -- canonical owner-facing subgroup at the conjugated representative.
    let htransport_eq :=
      Proposition_11_11_4_1.associatedPElementarySubgroup_conj_transport_stable
        (G := G) p (x := x) (g := g) P
    simpa [P'] using htransport_eq ▸ hmap
  exact hNotAssoc
    (hasAssociatedPElementarySubgroupInClass_of_le
      (c := owner) (H := H) hxg P' htransport)

/-- Helper for Proposition 11-11.4-1: if an `A`-valued quantity becomes a `p`-multiple of an
algebraic integer in `ℂ`, then it lies in every maximal ideal of residual characteristic `p`.
This separates the coefficient-ring descent from the group-theoretic part of the regular-branch
criterion. -/
theorem mem_residual_maximal_of_complex_prime_multiple
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {z : integralClosure ℤ ℂ}
    (ha : algebraMap A ℂ a = (z : ℂ) * (p : ℂ)) :
    a ∈ M.1.asIdeal := by
  classical
  -- The scalar `p` lies in `M`, because the residue field has characteristic `p`.
  have hp_mem : ((p : ℕ) : A) ∈ M.1.asIdeal := by
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    have hp0 : (p : A ⧸ M.1.asIdeal) = 0 := CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  -- Work inside the integral closure `B := integralClosure A ℂ`, which is integral over `A`.  We do
  -- *not* assume `A` is the full ring of algebraic integers; instead the going-up (lying-over)
  -- theorem produces a prime `Q` of `B` lying over `M`, and the algebraic integer `z` lives in `B`.
  set B := integralClosure A ℂ with hBdef
  have hzint : IsIntegral A (z : ℂ) := by
    have h0 : IsIntegral ℤ (z : ℂ) :=
      (IsIntegralClosure.isIntegral_iff (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2 ⟨z, rfl⟩
    exact h0.tower_top
  let z' : B := ⟨(z : ℂ), hzint⟩
  haveI : (M.1.asIdeal).IsPrime := M.1.2.isPrime
  obtain ⟨Q, _hQge, hQp, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) M.1.asIdeal (⊥ : Ideal B)
      (by simp)
  have hcoeA : ((algebraMap A B a : B) : ℂ) = algebraMap A ℂ a :=
    (IsScalarTower.algebraMap_apply A B ℂ a).symm
  have hcoeP : ((algebraMap A B ((p : ℕ) : A) : B) : ℂ) = ((p : ℕ) : ℂ) := by
    have h : ((algebraMap A B ((p : ℕ) : A) : B) : ℂ) = algebraMap A ℂ ((p : ℕ) : A) :=
      (IsScalarTower.algebraMap_apply A B ℂ ((p : ℕ) : A)).symm
    rw [h, map_natCast]
  -- In `B` the element `algebraMap a` factors as `z' * (p : B)`.
  have heq : algebraMap A B a = z' * algebraMap A B ((p : ℕ) : A) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hcoeA, hcoeP, ha]
  -- Since `p ∈ M` and `Q` lies over `M`, the factor `algebraMap p` lies in `Q`.
  have hpQ : algebraMap A B ((p : ℕ) : A) ∈ Q := by
    have hmem : ((p : ℕ) : A) ∈ Q.comap (algebraMap A B) := by
      rw [hQcomap]; exact hp_mem
    rwa [Ideal.mem_comap] at hmem
  have hkey : algebraMap A B a ∈ Q := by
    rw [heq]; exact Q.mul_mem_left z' hpQ
  -- Contracting `Q` back to `A` puts `a` into `M`.
  have haQ : a ∈ Q.comap (algebraMap A B) := by rw [Ideal.mem_comap]; exact hkey
  rwa [hQcomap] at haQ

/-- Helper for Proposition 11-11.4-1: an `A`-valued quantity whose complex realization is an
integer divisible by the residual characteristic already lies in the maximal ideal `M`. This is
the integer-valued counterpart to the algebraic-integer descent used on induction values. -/
theorem mem_residual_maximal_of_integer_value_dvd
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {n : ℤ}
    (ha : algebraMap A ℂ a = (n : ℂ))
    (hn : (p : ℤ) ∣ n) :
    a ∈ M.1.asIdeal := by
  rcases hn with ⟨m, rfl⟩
  -- Rewrite the integer value as an explicit `p`-multiple and apply the algebraic-integer
  -- descent already proved above.
  refine mem_residual_maximal_of_complex_prime_multiple (A := A) (p := p) (M := M)
    (a := a) (z := algebraMap ℤ (integralClosure ℤ ℂ) m) ?_
  calc
    algebraMap A ℂ a = ((m : ℤ) * (p : ℤ) : ℂ) := by
      simpa [Int.cast_mul, mul_comm] using ha
    _ = ((algebraMap ℤ (integralClosure ℤ ℂ) m : integralClosure ℤ ℂ) : ℂ) * (p : ℂ) := by
      simp [Int.cast_mul]

/-- Helper for Proposition 11-11.4-1: an `A`-valued quantity whose complex realization is an
integer not divisible by the residual characteristic cannot lie in the maximal ideal `M`. This is
the arithmetic endpoint needed for the future Brauer witness on the regular branch. -/
theorem not_mem_residual_maximal_of_integer_value_not_dvd
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {n : ℤ}
    (ha : algebraMap A ℂ a = (n : ℂ))
    (hn : ¬ (p : ℤ) ∣ n) :
    a ∉ M.1.asIdeal := by
  intro haM
  have haA : a = (n : A) := by
    -- Compare the complex realizations and use injectivity of `A → ℂ` to identify `a` with the
    -- integer element `n` inside `A`.
    apply FaithfulSMul.algebraMap_injective A ℂ
    calc
      algebraMap A ℂ a = (n : ℂ) := ha
      _ = algebraMap A ℂ (n : A) := by simp
  have hn_mem : (n : A) ∈ M.1.asIdeal := by
    simpa [haA] using haM
  have hp0 :
      (p : A ⧸ M.1.asIdeal) = 0 := by
    -- The quotient by `M` has characteristic `p`, so the scalar `p` vanishes there.
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    exact CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
  have hp_mem : ((p : ℤ) : A) ∈ M.1.asIdeal := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  have hnat_not_dvd : ¬ (p : ℕ) ∣ n.natAbs := by
    intro hdiv
    exact hn <|
      (Int.dvd_natAbs).mp <|
        Int.natCast_dvd_natCast.mpr hdiv
  have hcop : Nat.Coprime n.natAbs (p : ℕ) := by
    exact ((Nat.Prime.coprime_iff_not_dvd p.2).2 hnat_not_dvd).symm
  have hgcd : Int.gcd n (p : ℤ) = 1 := by
    -- Convert the prime-to-`p` hypothesis into the integer gcd form needed for Bézout.
    simpa [Int.gcd_def, Nat.gcd_comm] using hcop.gcd_eq_one
  have hbezout :
      n * Int.gcdA n (p : ℤ) + (p : ℤ) * Int.gcdB n (p : ℤ) = 1 := by
    -- Rewrite the integer gcd identity into a Bézout relation for `n` and `p`.
    simpa [hgcd] using (Int.gcd_eq_gcd_ab n (p : ℤ)).symm
  have hbezoutA :
      ((n * Int.gcdA n (p : ℤ) + (p : ℤ) * Int.gcdB n (p : ℤ) : ℤ) : A) = 1 := by
    -- Move the Bézout relation from integers into the coefficient ring `A`.
    simpa using congrArg (fun z : ℤ ↦ (z : A)) hbezout
  have h1_mem : (1 : A) ∈ M.1.asIdeal := by
    have hleft :
        ((n : A) * (Int.gcdA n (p : ℤ) : A)) ∈ M.1.asIdeal := by
      exact M.1.asIdeal.mul_mem_right (Int.cast (R := A) (Int.gcdA n (p : ℤ))) hn_mem
    have hright :
        (((p : ℤ) : A) * (Int.gcdB n (p : ℤ) : A)) ∈ M.1.asIdeal := by
      simpa [mul_comm] using
        M.1.asIdeal.mul_mem_left (Int.cast (R := A) (Int.gcdB n (p : ℤ))) hp_mem
    have hsum :
        ((n : A) * (Int.gcdA n (p : ℤ) : A) +
          (((p : ℤ) : A) * (Int.gcdB n (p : ℤ) : A))) ∈ M.1.asIdeal :=
      M.1.asIdeal.add_mem hleft hright
    rw [← hbezoutA]
    simpa [Int.cast_add, Int.cast_mul] using hsum
  have htop : M.1.asIdeal = ⊤ :=
    Ideal.eq_top_of_isUnit_mem M.1.asIdeal h1_mem (by simp)
  exact M.1.2.ne_top htop

/-- Helper for Proposition 11-11.4-1: every induced class function coming from the realized scalar
extension on a subgroup is represented by an element of Serre's induction ideal `I_H`. This
separates the tensor-realization step from the later Brauer arithmetic on the induced values. -/
theorem induced_realization_mem_tensorCharacterRingInductionIdeal
    (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      (ξ : G → ℂ) = Ind[H](f) := by
  -- Induct over the defining `A`-span of the scalar extension on `H`, so the base case is
  -- exactly one generator of Serre's induction ideal `I_H`.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      refine ⟨Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (Subgroup.characterRingInduction_local (G := G) H ⟨χ, hχ⟩), ?_, ?_⟩
      · -- By definition, the local induction generator is one of the spanning generators of `I_H`.
        exact Ideal.subset_span ⟨⟨χ, hχ⟩, rfl⟩
      · -- The chosen generator realizes the induced class function pointwise on `G`.
        ext g
        simp [Algebra.TensorProduct.includeRight, Subgroup.characterRingInduction_local_apply]
  | zero =>
      refine ⟨0, Ideal.zero_mem _, ?_⟩
      -- Induction sends the zero class function to the zero class function.
      ext g
      simp [Subgroup.inducedClassFunction]
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      rcases hf₁ with ⟨ξ₁, hξ₁_mem, hξ₁_eval⟩
      rcases hf₂ with ⟨ξ₂, hξ₂_mem, hξ₂_eval⟩
      refine ⟨ξ₁ + ξ₂,
        (tensorCharacterRingInductionIdeal (A := A) (G := G) H).add_mem hξ₁_mem hξ₂_mem,
        ?_⟩
      -- The tensor realization is additive, and subgroup induction is additive as well.
      ext g
      calc
        ((ξ₁ + ξ₂ : A ⊗R(G)) : G → ℂ) g = (ξ₁ : G → ℂ) g + (ξ₂ : G → ℂ) g := by
          simp
        _ = Ind[H](f₁) g + Ind[H](f₂) g := by rw [hξ₁_eval, hξ₂_eval]
        _ = Ind[H](f₁ + f₂) g := by
          simpa [Subgroup.inducedClassFunction_map_add]
  | smul a f _ hf' =>
      rcases hf' with ⟨ξ, hξ_mem, hξ_eval⟩
      have hsmul_mem : a • ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H := by
        have hsmul_eq :
            a • ξ = (algebraMap A (A ⊗R(G)) a) * ξ := by
          simpa using (Algebra.smul_def a ξ)
        have hmul :
            (algebraMap A (A ⊗R(G)) a) * ξ ∈
              tensorCharacterRingInductionIdeal (A := A) (G := G) H :=
          (tensorCharacterRingInductionIdeal (A := A) (G := G) H).mul_mem_left
            (algebraMap A (A ⊗R(G)) a) hξ_mem
        rw [hsmul_eq]
        exact hmul
      refine ⟨a • ξ, hsmul_mem, ?_⟩
      -- Scalar multiplication commutes with both the tensor realization and subgroup induction.
      ext g
      calc
        ((a • ξ : A ⊗R(G)) : G → ℂ) g = algebraMap A ℂ a * (ξ : G → ℂ) g := by
          change
            (((characterRingScalarExtension A G).subtype ∘ₗ
                Submodule.tensorToSpan A (Subalgebra.toSubmodule R[ℂ](G))) (a • ξ)) g =
              algebraMap A ℂ a * (ξ : G → ℂ) g
          rw [LinearMap.map_smul]
          simp [Pi.smul_apply, Algebra.smul_def]
        _ = algebraMap A ℂ a * Ind[H](f) g := by rw [hξ_eval]
        _ = Ind[H](a • f) g := by
          simpa [Pi.smul_apply, Algebra.smul_def, mul_comm] using
            congrFun
              (Subgroup.inducedClassFunction_map_smul (S := A) H a f).symm g

include hroots in
/-- Helper for Proposition 11-11.4-1: the forward half of Serre's regular-prime criterion is
already available once the canonical `p`-regular owner of `d` is represented by a concrete
element `x`. This isolates the Chapter `11.3` divisibility step before transporting the result
back from `ConjClasses.mk x` to the original class `d` modulo `M`. -/
theorem tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  classical
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)) :=
    Classical.choice
      (show Nonempty (Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) from Sylow.nonempty)
  -- Reduce ideal containment to checking the source generators coming from subgroup induction.
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨χ, rfl⟩
  refine
    (induction_generator_mem_value_comap_iff
      (A := A) (hroots := hroots) (G := G) M.1 (ConjClasses.mk x) H χ).2 ?_
  have hxreg : IsPRegular (p : ℕ) x := owner.2 x hx
  have hnoConj :
      ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup (p : ℕ) x P ≤ H :=
    no_conjugate_associated_subgroup_of_not_hasAssociated_owner
      (G := G) p H d hx P hNotAssoc
  obtain ⟨z, hz⟩ :=
    induced_characterRing_value_eq_prime_multiple_of_algebraicInteger
      (p := (p : ℕ)) (H := H) (x := x) hxreg P hnoConj χ
  have hclass :
      ((H.characterRingInduction_local χ : R(G)) : G → ℂ)
          (Proposition_11_11_4_1.conjClassRepresentative (G := G) (ConjClasses.mk x)) =
        ((H.characterRingInduction_local χ : R(G)) : G → ℂ) x := by
    have hf :
        _root_.IsClassFunction
          (((H.characterRingInduction_local χ : R(G)) : G → ℂ)) := by
      exact
        Representation.isClassFunction_of_mem_characterRingOverField
          (K := ℂ) (H.characterRingInduction_local χ)
          (H.characterRingInduction_local χ).property
    -- The chosen representative of `ConjClasses.mk x` is conjugate to `x`, so class functions
    -- take the same value at both points.
    exact hf.eq_of_isConj <|
      ConjClasses.mk_eq_mk_iff_isConj.mp <|
        by simpa using
          Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (ConjClasses.mk x)
  -- Chapter `11.3` gives the required value as a `p`-multiple in `ℂ`, and the residual
  -- characteristic of `M` descends that multiple back to membership in `M`.
  refine mem_residual_maximal_of_complex_prime_multiple (A := A) (p := p) (M := M)
    (a := characterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x)
      (H.characterRingInduction_local χ))
    (z := z) ?_
  calc
    algebraMap A ℂ
        (characterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x)
          (H.characterRingInduction_local χ)) =
        ((H.characterRingInduction_local χ : R(G)) : G → ℂ)
          (Proposition_11_11_4_1.conjClassRepresentative (G := G) (ConjClasses.mk x)) := by
            simpa using
              characterRingValueAtConjClass_algebraMap (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x)
                (H.characterRingInduction_local χ)
    _ = ((H.characterRingInduction_local χ : R(G)) : G → ℂ) x := hclass
    _ = (z : ℂ) * (p : ℂ) := by
          simpa [Subgroup.characterRingInduction_local,
            Representation.Subgroup.characterRingInduction] using hz.symm

include hroots in
/-- Helper for Proposition 11-11.4-1: the forward half of Serre's regular-prime criterion can be
applied at the canonical owner representative obtained by taking the `p'`-part of the fixed
representative of `d`. This packages the arbitrary-representative lemma above in the exact
source-chosen form used by the remaining transport step back to `d`. -/
theorem tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_canonical_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G)
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  let x : G := pRegularComponent p
    (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)
  have hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier := by
    -- Rewrite the owner of `d` to the owner of its chosen representative, then note that a
    -- conjugacy class contains the representative used to define it.
    rw [← Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d]
    simpa [x, Proposition_11_11_4_1.pregular_conj_class_of_element] using
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl :
        pRegularComponent p (Proposition_11_11_4_1.conjClassRepresentative (G := G) d) ∈
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))).carrier)
  -- Apply the representative-level forward implication to the canonical source representative.
  simpa [x] using
    tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_representative
      (A := A) (hroots := hroots) (G := G) p M d H hx hNotAssoc


/-- Helper for Proposition 11-11.4-1: restricting a realized scalar-extension class function from
`L` to the subgroup-of-`H` copy `L.subgroupOf H` preserves scalar-extension membership. This is
the thin interface bridge needed before induction in stages can move the auxiliary witness from
its associated subgroup into `I_H`. -/
theorem subgroupOf_restriction_mem_characterRingScalarExtension
    (L H : Subgroup G) (hL : L ≤ H) {f : L → ℂ}
    (hf : f ∈ characterRingScalarExtension A L) :
    (fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z)) ∈
      characterRingScalarExtension A (L.subgroupOf H) := by
  -- Transport the defining span across the canonical subgroup equivalence `L.subgroupOf H ≃* L`.
  rw [characterRingScalarExtension] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
    let e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hL
    let χ : R(L.subgroupOf H) := Subgroup.characterRingTransport e ⟨ψ, hψ⟩
    have hχ :
        ((χ : R(L.subgroupOf H)) : L.subgroupOf H → ℂ) =
          fun z : L.subgroupOf H ↦ ψ (e z) := by
      ext z
      simp [χ, e, Subgroup.characterRingTransport_apply]
    exact hχ ▸ Submodule.subset_span χ.property
  | zero =>
    exact Submodule.zero_mem _
  | add f₁ f₂ _ _ hf₁ hf₂ =>
    exact Submodule.add_mem _ hf₁ hf₂
  | smul a g _ hg =>
    exact Submodule.smul_mem _ a hg

/-- Helper for Proposition 11-11.4-1: if `L ≤ H` and a class function on `L` lies in the realized
scalar extension, then its direct induction from `L` to `G` is realized by an element of Serre's
induction ideal `I_H`. This packages the restriction-to-`L.subgroupOf H` and induction-in-stages
route into a single reusable witness theorem. -/
theorem induced_realization_mem_tensorCharacterRingInductionIdeal_of_le
    (L H : Subgroup G) (hL : L ≤ H) {f : L → ℂ}
    (hf : f ∈ characterRingScalarExtension A L) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      (ξ : G → ℂ) = Ind[L](f) := by
  let fH : H → ℂ :=
    Ind[L.subgroupOf H](
      fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z))
  have hf_restr :
      (fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z)) ∈
        characterRingScalarExtension A (L.subgroupOf H) :=
    subgroupOf_restriction_mem_characterRingScalarExtension
      (A := A) (G := G) L H hL hf
  have hfH : fH ∈ characterRingScalarExtension A H := by
    -- First realize the restricted auxiliary function on `H`, then induce inside `H`.
    simpa [fH] using
      induced_mem_characterRingScalarExtension_of_mem
        (A := A) (G := H) (H := L.subgroupOf H) hf_restr
  rcases induced_realization_mem_tensorCharacterRingInductionIdeal
      (A := A) (G := G) H hfH with ⟨ξ, hξ_mem, hξ_eval⟩
  refine ⟨ξ, hξ_mem, ?_⟩
  -- Induction in stages identifies the realization of the `I_H` witness with direct induction
  -- from the original subgroup `L`.
  calc
    (ξ : G → ℂ) = Ind[H](fH) := hξ_eval
    _ = Ind[L](f) := by
      simpa [fH] using
        (Subgroup.inducedClassFunction_subgroupOf_induction_in_stages
          (H := H) (L := L) hL f)


/-- Helper for Proposition 11-11.4-1: on a finite commutative group `B`, the `|B|`-weighted delta
function at a point is an `A`-linear combination of the linear characters of `B`, with coefficients
that lie in `A` because they are the root-of-unity values `χ(u⁻¹)` controlled by the source
hypothesis `hrootsB`.  This is the coefficient-ring-general form of Lemma 10-10.3-1's weighted
delta expansion, now obtained from `hrootsB` rather than from `IsIntegralClosure`. -/
theorem weighted_delta_expansion_over_A
    {B : Type} [CommGroup B] [Finite B] [DecidableEq B] (u : B)
    (hrootsB : ∀ z : ℂˣ, z ^ Nat.card B = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ∃ coeff : (B →* ℂˣ) → A,
      (fun h : B ↦ if u = h then (Nat.card B : ℂ) else 0) =
        ∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  have hval : ∀ χ : B →* ℂˣ, (χ u⁻¹ : ℂ) ∈ Set.range (algebraMap A ℂ) := by
    intro χ
    refine hrootsB (χ u⁻¹) ?_
    have hpow : (u⁻¹ : B) ^ Nat.card B = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
    calc (χ u⁻¹) ^ Nat.card B = χ ((u⁻¹) ^ Nat.card B) := (map_pow χ u⁻¹ _).symm
      _ = χ 1 := by rw [hpow]
      _ = 1 := map_one χ
  let coeff : (B →* ℂˣ) → A := fun χ ↦ Classical.choose (hval χ)
  have hcoeff : ∀ χ : B →* ℂˣ, algebraMap A ℂ (coeff χ) = (χ u⁻¹ : ℂ) :=
    fun χ ↦ Classical.choose_spec (hval χ)
  refine ⟨coeff, ?_⟩
  ext h
  calc
    (fun x : B ↦ if u = x then (Nat.card B : ℂ) else 0) h
        = (Representation.leftRegular ℂ B).character (u⁻¹ * h) := by
            by_cases hu : u = h
            · subst hu
              simp [Representation.leftRegular_character_one (k := ℂ) (G := B)]
            · have hne : u⁻¹ * h ≠ 1 := by
                intro h1; apply hu
                have hm := congrArg (fun t : B ↦ u * t) h1
                simpa [mul_assoc] using hm.symm
              simpa [hu] using
                (Representation.leftRegular_character_eq_zero_of_ne_one (k := ℂ) (G := B) hne).symm
    _ = ∑ χ : B →* ℂˣ, (χ (u⁻¹ * h) : ℂ) := by
          simpa [Finset.sum_apply] using
            congrArg (fun φ : B → ℂ => φ (u⁻¹ * h))
              (commGroup_regularCharacter_eq_sum_linearCharacters (B := B))
    _ = (∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character) h := by
          simp [Finset.sum_apply, hcoeff, Algebra.smul_def, map_mul,
            MonoidHom.toRepresentation_character_apply]

include hroots in
/-- Helper for Proposition 11-11.4-1: Brauer's explicit auxiliary function on the associated
`p`-elementary subgroup belongs to the *arithmetic* scalar extension `A`-character ring, using only
the roots-of-unity source hypothesis `hroots`.  This is the coefficient-ring-general form of Lemma
10-10.3-3's `brauerAssociatedAuxiliaryFunction_mem_characterRingScalarExtension`; it lets the
forward witness be realized over `A` (rather than over the full ring of algebraic integers). -/
theorem brauerAux_mem_characterRingScalarExtension_of_roots
    (p : Nat.Primes) (x : G) (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)))
    (hx : IsPRegular (p : ℕ) x) :
    brauerAssociatedAuxiliaryFunction (p : ℕ) x P ∈
      characterRingScalarExtension A (associatedPElementarySubgroup (p : ℕ) x P) := by
  classical
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let H' := associatedPElementarySubgroup (p : ℕ) x P
  let C₀ : Subgroup H' := (Subgroup.zpowers x).subgroupOf H'
  let hdecomp := associatedPElementarySubgroup_decomposition x hx P
  letI : IsCyclic C₀ := by simpa [C₀] using hdecomp.cyclic
  letI : CommGroup C₀ := IsCyclic.commGroup
  let u : C₀ := associatedPElementary_zpowers_generator (p : ℕ) x P
  have hcardC₀ : Nat.card C₀ ∣ Nat.card G := by
    have h1 : Nat.card C₀ ∣ Nat.card H' := by
      simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card C₀
    have h2 : Nat.card H' ∣ Nat.card G := by
      simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H'
    exact dvd_trans h1 h2
  have hrootsC₀ : ∀ z : ℂˣ, z ^ Nat.card C₀ = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) := by
    intro z hz
    refine hroots z ?_
    obtain ⟨m, hm⟩ := hcardC₀
    rw [hm, pow_mul, hz, one_pow]
  have hrewrite :
      brauerAssociatedAuxiliaryFunction (p : ℕ) x P =
        fun h : H' ↦
          if associatedPElementary_zpowers_projection x hx P h = u then (Nat.card C₀ : ℂ)
          else 0 := by
    simpa [C₀, u] using brauerAssociatedAuxiliaryFunction_eq_pullback_weighted_delta x P hx
  obtain ⟨coeff, hcoeff⟩ :=
    weighted_delta_expansion_over_A (A := A) (B := C₀) (u := u) (hrootsB := hrootsC₀)
  have hpullback :
      (fun h : H' ↦
        if associatedPElementary_zpowers_projection x hx P h = u then (Nat.card C₀ : ℂ) else 0) =
        ∑ χ : C₀ →* ℂˣ,
          coeff χ •
            fun h : H' ↦ ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ) := by
    ext h
    have hpoint :
        (if u = associatedPElementary_zpowers_projection x hx P h then (Nat.card C₀ : ℂ) else 0) =
          (∑ χ : C₀ →* ℂˣ, coeff χ • χ.toRepresentation.character)
            (associatedPElementary_zpowers_projection x hx P h) := by
      simpa [Finset.sum_apply] using
        congrFun hcoeff (associatedPElementary_zpowers_projection x hx P h)
    calc
      (if associatedPElementary_zpowers_projection x hx P h = u then (Nat.card C₀ : ℂ) else 0)
          = (if u = associatedPElementary_zpowers_projection x hx P h then
              (Nat.card C₀ : ℂ) else 0) := by
              by_cases hEq : u = associatedPElementary_zpowers_projection x hx P h
              · rw [if_pos hEq.symm, if_pos hEq]
              · have hEq' : ¬ associatedPElementary_zpowers_projection x hx P h = u :=
                  fun hu => hEq hu.symm
                rw [if_neg hEq', if_neg hEq]
      _ = (∑ χ : C₀ →* ℂˣ, coeff χ • χ.toRepresentation.character)
            (associatedPElementary_zpowers_projection x hx P h) := hpoint
      _ = (∑ χ : C₀ →* ℂˣ,
            coeff χ •
              fun h : H' ↦
                ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) h := by
            simp [Finset.sum_apply, MonoidHom.toRepresentation_character_apply]
  rw [hrewrite, hpullback]
  refine Submodule.sum_mem _ ?_
  intro χ _
  refine (characterRingScalarExtension A H').smul_mem (coeff χ) ?_
  let η : R(H') := (χ.comp (associatedPElementary_zpowers_projection x hx P)).toCharacterRing
  have hηcoe :
      ((η : R(H')) : H' → ℂ) =
        fun h : H' ↦ ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ) := by
    ext h; simp [η, MonoidHom.toCharacterRing_apply]
  rw [← hηcoe]
  exact mem_characterRingScalarExtension_of_mem_characterRing (A := A) _ η.property

include hroots in
/-- Helper for Proposition 11-11.4-1: an associated owner subgroup supplies an explicit
element of Serre's induction ideal `I_H` whose fixed-class value is an integer prime to `p`, so
it cannot lie in the evaluation pullback prime over `M`.

Faithful rework (no `IsIntegralClosure.equiv`): rather than transporting the Chapter 10 auxiliary
tensor (whose coefficients are arbitrary algebraic integers) along the now-unavailable equivalence
`(integralClosure ℤ ℂ) ≃ A`, we realize Brauer's *explicit* auxiliary function directly over `A`
from `hroots` (`brauerAux_mem_characterRingScalarExtension_of_roots`), induce it into `I_H`, and
read off its value `n` at `x` (with `p ∤ n`) from the Chapter 10 support clauses. -/
theorem associated_owner_induction_witness_not_mem_owner_value_comap
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)))
    (hP : associatedPElementarySubgroup (p : ℕ) x P ≤ H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      ξ ∉ (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  let L : Subgroup G := associatedPElementarySubgroup (p : ℕ) x P
  have hxreg : IsPRegular (p : ℕ) x := owner.2 x hx
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  -- Realize Brauer's explicit auxiliary function over `A` and induce it into `I_H`.
  have hfmem :
      brauerAssociatedAuxiliaryFunction (p : ℕ) x P ∈ characterRingScalarExtension A L :=
    brauerAux_mem_characterRingScalarExtension_of_roots
      (A := A) (G := G) (hroots := hroots) p x P hxreg
  rcases induced_realization_mem_tensorCharacterRingInductionIdeal_of_le
      (A := A) (G := G) L H hP hfmem with ⟨ξ, hξ_mem, hξ_eval⟩
  -- The Chapter 10 support clauses give the induced value `n` at `x`, with `p ∤ n`.
  obtain ⟨ψ0, hψ0⟩ :=
    exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction (p := (p : ℕ)) x P hxreg
  obtain ⟨n, hnval, hndiv⟩ :=
    associated_auxiliary_character_induced_at_x_clause_of_realization
      (p := (p : ℕ)) x P hxreg ψ0 hψ0
  rw [hψ0] at hnval
  have hvalue_complex :
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) =
        (n : ℂ) := by
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) =
          tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) ξ := by
            simpa using
              tensorCharacterRingValueAtConjClass_complex_eq
                (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ
      _ = (ξ : G → ℂ) x := by
            simpa [tensorCharacterRingToSubalgebra] using
              (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
                (A := A) (G := G) (ConjClasses.mk x) ξ
                (rfl : ConjClasses.mk x = ConjClasses.mk x))
      _ = Ind[L](brauerAssociatedAuxiliaryFunction (p : ℕ) x P) x := by
            simpa using congrFun hξ_eval x
      _ = (n : ℂ) := hnval
  refine ⟨ξ, hξ_mem, ?_⟩
  -- The Chapter 10 auxiliary value at `x` is an integer prime to `p`, so the pullback prime over
  -- `M` cannot contain the induced witness.
  change
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∉ M.1.asIdeal
  exact
    not_mem_residual_maximal_of_integer_value_not_dvd
      (A := A) (p := p) (M := M) hvalue_complex hndiv

include hroots in
/-- Helper for Proposition 11-11.4-1: any owner representative `x` of the canonical `p`-regular
class of `d` gives the same fixed-class evaluation as the source-chosen representative
`pRegularComponent p (conjClassRepresentative d)`. This isolates the exact class-equality part of
the remaining transport. -/
theorem owner_representative_value_eq_canonical_pregular_component_value
    (p : Nat.Primes) (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ =
      tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
        (ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ := by
  have hmk :
      ConjClasses.mk x =
        ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) := by
    -- Both representatives lie in the same canonical owner class of `d`.
    calc
      ConjClasses.mk x =
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
            ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      _ =
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p
            (ConjClasses.mk
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) :
            ConjClasses G) := by
            rw [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d]
      _ =
          ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) := by
            rfl
  -- Compare the two `A`-valued evaluations after embedding them into `ℂ`, where the class-equality
  -- rewrite can be applied directly to the realized tensor character.
  apply FaithfulSMul.algebraMap_injective A ℂ
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ]
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G)
    (ConjClasses.mk
      (pRegularComponent p
        (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ]
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
    (ConjClasses.mk x) ξ rfl]
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
    (ConjClasses.mk
      (pRegularComponent p
        (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ hmk]

include hroots in
/-- Helper for Proposition 11-11.4-1: modulo the residual ideal `M`, membership of the fixed-class
value at the canonical `p`-regular component is equivalent to membership of the value at any owner
representative `x` of that component. This isolates the owner-side transport from the still-missing
Chapter `10` comparison between `d` and its canonical `p`-regular component. -/
theorem canonical_pregular_component_value_mem_residual_iff_owner_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
        (ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
      M.1.asIdeal ↔
        tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∈
          M.1.asIdeal := by
  -- The two fixed-class evaluations already agree in `A`, so ideal membership is identical.
  rw [← owner_representative_value_eq_canonical_pregular_component_value
    (A := A) (hroots := hroots) (G := G) p d hx ξ]

include hroots in
/-- Helper for Proposition 11-11.4-1: the complex realization of the `A`-valued fixed-class
evaluation at `ConjClasses.mk x` is the realized tensor character evaluated at `x` itself. -/
private theorem algebraMap_valueAtConjClass_mk_eq_apply
    (ξ : A ⊗R(G)) (x : G) :
    algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) =
      (ξ : G → ℂ) x := by
  calc
    algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) ξ :=
        tensorCharacterRingValueAtConjClass_complex_eq (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ
    _ = (ξ : G → ℂ) x := by
        simpa using
          (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
            (A := A) (G := G) (ConjClasses.mk x) ξ rfl)

/-- Helper for Proposition 11-11.4-1 (FaithfulSMul rederivation of Lemma 10-10.3-2): the
principal-ideal quotient `A ⧸ (p)` has characteristic `p` once `p` is a non-unit. -/
theorem quotient_span_prime_charP_faithful
    {p : ℕ} [Fact p.Prime] (hp_nonunit : ¬ IsUnit (p : A)) :
    CharP (A ⧸ Ideal.span ({(p : A)} : Set A)) p :=
  CharP.quotient A p (by simpa using hp_nonunit)

/-- Helper for Proposition 11-11.4-1: a degree-`1` character has lift values in `A` (via the
roots-of-unity source hypothesis `hrootsH`) whose `p^k`th powers agree whenever the underlying
group elements have the same `p^k`th power. -/
theorem exists_lifts_of_linear_character_values_with_pow_eq_faithful
    {H : Type} [Group H] [Finite H]
    {p : ℕ}
    (hrootsH : ∀ w : ℂˣ, w ^ Nat.card H = 1 → ((w : ℂ) ∈ Set.range (algebraMap A ℂ)))
    (ρ : H →* ℂˣ) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = (ρ y : ℂ) ∧
      algebraMap A ℂ az = (ρ z : ℂ) ∧
      ay ^ (p ^ k) = az ^ (p ^ k) := by
  have hyroot : (ρ y) ^ Nat.card H = 1 := by
    obtain ⟨t, ht⟩ := orderOf_dvd_natCard y
    rw [ht, pow_mul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
  have hzroot : (ρ z) ^ Nat.card H = 1 := by
    obtain ⟨t, ht⟩ := orderOf_dvd_natCard z
    rw [ht, pow_mul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
  obtain ⟨ay, hay⟩ := hrootsH (ρ y) hyroot
  obtain ⟨az, haz⟩ := hrootsH (ρ z) hzroot
  refine ⟨ay, az, hay, haz, ?_⟩
  have h_inj : Function.Injective (algebraMap A ℂ) :=
    FaithfulSMul.algebraMap_injective A ℂ
  apply h_inj
  calc
    algebraMap A ℂ (ay ^ (p ^ k)) = (ρ y : ℂ) ^ (p ^ k) := by
      rw [map_pow, hay]
    _ = (ρ (y ^ (p ^ k)) : ℂ) := by
      simp
    _ = (ρ (z ^ (p ^ k)) : ℂ) := by
      simp [hpow]
    _ = (ρ z : ℂ) ^ (p ^ k) := by
      simp
    _ = algebraMap A ℂ (az ^ (p ^ k)) := by
      rw [map_pow, haz]

/-- Helper for Proposition 11-11.4-1: on a finite cyclic group, every ordinary character admits
lifts at `y` and `z` whose `p^k`th powers agree modulo `(p)` once `y^(p^k) = z^(p^k)`. -/
theorem cyclic_character_qpow_quotient_eq_faithful
    {H : Type} [Group H] [Finite H] [IsCyclic H]
    {p : ℕ} [Fact p.Prime]
    (hp_nonunit : ¬ IsUnit (p : A))
    (hrootsH : ∀ w : ℂˣ, w ^ Nat.card H = 1 → ((w : ℂ) ∈ Set.range (algebraMap A ℂ)))
    {ψ : H → ℂ} (hψ : ψ ∈ R(H)) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = ψ y ∧
      algebraMap A ℂ az = ψ z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CommGroup H := IsCyclic.commGroup
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP_faithful (A := A) (p := p) hp_nonunit
  let P : (g : H → ℂ) → g ∈ R(H) → Prop := fun g _ ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  refine Algebra.adjoin_induction (p := P) ?_ ?_ ?_ ?_ hψ
  · intro χ hχ
    rcases hχ with ⟨ρ, -, hρirr, rfl⟩
    obtain ⟨α, hα⟩ := exists_linear_character_of_irreducible_rep (ρ := ρ)
    obtain ⟨ay, az, hay, haz, hpowA⟩ :=
      exists_lifts_of_linear_character_values_with_pow_eq_faithful
        (A := A) (p := p) hrootsH α hpow
    refine ⟨ay, az, ?_, ?_, ?_⟩
    · simpa [hα]
    · simpa [hα]
    · simpa [mk] using congrArg mk hpowA
  · intro n
    refine ⟨n, n, ?_, ?_, ?_⟩
    · simp
    · simp
    · rfl
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by
          simp [mk]
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay * uy, az * uz, ?_, ?_, ?_⟩
    · simp [hay, huy, map_mul]
    · simp [haz, huz, map_mul]
    · calc
        mk ((ay * uy) ^ (p ^ k)) = (mk (ay * uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay * mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) * (mk uy) ^ (p ^ k) := by
          simpa using mul_pow (mk ay) (mk uy) (p ^ k)
        _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az * uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az * uz)) ^ (p ^ k) = (mk az * mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by
              simpa using mul_pow (mk az) (mk uz) (p ^ k)
        _ = mk ((az * uz) ^ (p ^ k)) := by
          simp [mk]

/-- Helper for Proposition 11-11.4-1: the cyclic Frobenius `p^k`-power congruence for an
`A`-realized tensor character on a finite cyclic group, derived from `FaithfulSMul`, a non-unit
witness `hp_nonunit`, and the roots-of-unity source hypothesis `hrootsH`. -/
theorem tensor_character_qpow_quotient_eq_faithful
    {H : Type} [Group H] [Finite H] [IsCyclic H]
    (p : ℕ) [Fact p.Prime] (hp_nonunit : ¬ IsUnit (p : A))
    (hrootsH : ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))
    {f : H → ℂ} (hf : f ∈ characterRingScalarExtension A H)
    {y z : H} {k : ℕ} (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = f y ∧
      algebraMap A ℂ az = f z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP_faithful (A := A) (p := p) hp_nonunit
  let P : (H → ℂ) → Prop := fun g ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  refine Submodule.span_induction
    (s := (R(H) : Set (H → ℂ)))
    (p := fun g _ ↦ P g)
    ?_ ?_ ?_ ?_ hf
  · intro ψ hψ
    exact cyclic_character_qpow_quotient_eq_faithful
      (A := A) (p := p) hp_nonunit hrootsH hψ hpow
  · refine ⟨0, 0, ?_, ?_, rfl⟩
    · simp
    · simp
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by
          simp [mk]
  · intro a g _ hg
    rcases hg with ⟨ay, az, hay, haz, hq⟩
    refine ⟨a * ay, a * az, ?_, ?_, ?_⟩
    · calc
        algebraMap A ℂ (a * ay) = algebraMap A ℂ a * algebraMap A ℂ ay := by
          simp [map_mul]
        _ = algebraMap A ℂ a * g y := by
          rw [hay]
        _ = (a • g) y := by
          simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        algebraMap A ℂ (a * az) = algebraMap A ℂ a * algebraMap A ℂ az := by
          simp [map_mul]
        _ = algebraMap A ℂ a * g z := by
          rw [haz]
        _ = (a • g) z := by
          simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        mk ((a * ay) ^ (p ^ k)) = (mk (a * ay)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk a * mk ay) ^ (p ^ k) := by
          simp [mk]
        _ = (mk a) ^ (p ^ k) * (mk ay) ^ (p ^ k) := by
          simpa using mul_pow (mk a) (mk ay) (p ^ k)
        _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by
          rw [hq]
        _ = (mk (a * az)) ^ (p ^ k) := by
          symm
          calc
            (mk (a * az)) ^ (p ^ k) = (mk a * mk az) ^ (p ^ k) := by
              simp [mk]
            _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by
              simpa using mul_pow (mk a) (mk az) (p ^ k)
        _ = mk ((a * az) ^ (p ^ k)) := by
          simp [mk]

include hroots in
/-- Helper for Proposition 11-11.4-1: the cyclic-subgroup Frobenius comparison between the
realized values at `x` and at its canonical `p`-regular component, packaged with `A`-valued lifts
of the two endpoint values. Isolating this restriction-to-`⟨x⟩` step gives the residual
congruence lemmas below a fresh elaboration budget. -/
private theorem exists_qpow_span_quotient_eq_of_apply
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : G) (ξ : A ⊗R(G)) :
    ∃ (k : ℕ) (ay az : A),
      algebraMap A ℂ ay = (ξ : G → ℂ) x ∧
      algebraMap A ℂ az = (ξ : G → ℂ) (pRegularComponent p x) ∧
      (Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) ay) ^ ((p : ℕ) ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) az) ^ ((p : ℕ) ^ k) := by
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  -- `p` lies in the residual maximal ideal `M`, hence is a non-unit of `A`.
  have hp_mem : ((p : ℕ) : A) ∈ M.1.asIdeal := by
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    have hp0 : (p : A ⧸ M.1.asIdeal) = 0 := CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  have hp_nonunit : ¬ IsUnit ((p : ℕ) : A) := fun hu =>
    M.1.2.ne_top (Ideal.eq_top_of_isUnit_mem M.1.asIdeal hp_mem hu)
  obtain ⟨k, hkpow⟩ := exists_p_power_eq_pRegularComponent_pow (p := (p : ℕ)) x
  let H : Subgroup G := Subgroup.zpowers x
  -- The ambient roots-of-unity hypothesis restricts to the cyclic subgroup `H = ⟨x⟩`.
  have hrootsH : ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) := by
    intro z hz
    refine hroots z ?_
    obtain ⟨m, hm⟩ : Nat.card H ∣ Nat.card G := by
      simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H
    rw [hm, pow_mul, hz, one_pow]
  let xH : H := ⟨x, Subgroup.mem_zpowers x⟩
  let xrH : H :=
    ⟨pRegularComponent p x,
      (p_component_decomposition_exists (p := (p : ℕ)) x
        (isOfFinOrder_of_finite x)).right_mem_zpowers⟩
  have hxpowH : xH ^ ((p : ℕ) ^ k) = xrH ^ ((p : ℕ) ^ k) := by
    apply Subtype.ext
    simpa [xH, xrH] using hkpow
  let f : H → ℂ := ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ)
  have hf : f ∈ characterRingScalarExtension A H :=
    tensorCharacterRing_mem_characterRingScalarExtension
      (H.tensorCharacterRingRestriction ξ)
  have hfx : f xH = (ξ : G → ℂ) x := by
    change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xH = (ξ : G → ℂ) x
    rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
  have hfxr : f xrH = (ξ : G → ℂ) (pRegularComponent p x) := by
    change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xrH =
      (ξ : G → ℂ) (pRegularComponent p x)
    rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
  obtain ⟨ay, az, hay, haz, hq⟩ :=
    tensor_character_qpow_quotient_eq_faithful
      (A := A) (H := H) (p := (p : ℕ)) hp_nonunit hrootsH (f := f) hf
      (y := xH) (z := xrH) (k := k) hxpowH
  exact ⟨k, ay, az, hay.trans hfx, haz.trans hfxr, hq⟩

/-- Helper for Proposition 11-11.4-1: a `p^k`-power congruence modulo the principal ideal `(p)`
descends to the residual quotient `A / M`, where Frobenius injectivity cancels the powers.
Stating this over opaque elements `a b : A` keeps the fixed-class evaluation terms away from the
unifier. -/
private theorem residual_quotient_eq_of_qpow_span_quotient_eq
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a b : A} {k : ℕ}
    (hq : (Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) a) ^ ((p : ℕ) ^ k) =
      (Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) b) ^ ((p : ℕ) ^ k)) :
    Ideal.Quotient.mk M.1.asIdeal a = Ideal.Quotient.mk M.1.asIdeal b := by
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  letI : CharP M.1.asIdeal.ResidueField p := M.2.2
  letI : CharP (A ⧸ M.1.asIdeal) p :=
    RingHom.charP
      (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
      M.1.asIdeal.injective_algebraMap_quotient_residueField p
  have hp0 : (p : A ⧸ M.1.asIdeal) = 0 := CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
  have hp_mem : ((p : ℕ) : A) ∈ M.1.asIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  have hspan_le :
      Ideal.span ({((p : ℕ) : A)} : Set A) ≤ M.1.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem]
    simpa using hp_mem
  have hqpowM :
      (Ideal.Quotient.mk M.1.asIdeal a) ^ ((p : ℕ) ^ k) =
        (Ideal.Quotient.mk M.1.asIdeal b) ^ ((p : ℕ) ^ k) := by
    simpa using congrArg (Ideal.Quotient.factor hspan_le) hq
  exact ((frobenius_inj (A ⧸ M.1.asIdeal) p).iterate k) <| by
    simpa [iterate_frobenius] using hqpowM

include hroots in
/-- Helper for Proposition 11-11.4-1: for any tensor character, the fixed-class evaluations at an
element `x` and at its canonical `p`-regular component become equal in the residue field of `M`.
This is the source-faithful Chapter `10` congruence specialized to the only quotient used in the
regular branch. -/
theorem residual_valueAtConjClass_eq_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : G) (ξ : A ⊗R(G)) :
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) =
      Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
          (ConjClasses.mk (pRegularComponent p x)) ξ) := by
  -- The cyclic-subgroup Frobenius step compares the two fixed-class values modulo `(p)`, and the
  -- opaque-element descent lemma factors that congruence through `A / M` where Frobenius
  -- injectivity cancels the `p^k`th powers.
  obtain ⟨k, ay, az, hay, haz, hq⟩ :=
    exists_qpow_span_quotient_eq_of_apply (A := A) (G := G) (hroots := hroots) p M x ξ
  have hay_eq :
      ay = tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ := by
    -- The cyclic-step lift at `x` coincides with the canonical `A`-valued fixed-class evaluation.
    apply FaithfulSMul.algebraMap_injective A ℂ
    rw [hay, algebraMap_valueAtConjClass_mk_eq_apply (A := A) (hroots := hroots) (G := G) ξ x]
  have haz_eq :
      az = tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
        (ConjClasses.mk (pRegularComponent p x)) ξ := by
    -- The same comparison identifies the lift at `pRegularComponent p x`.
    apply FaithfulSMul.algebraMap_injective A ℂ
    rw [haz, algebraMap_valueAtConjClass_mk_eq_apply (A := A) (hroots := hroots) (G := G) ξ
      (pRegularComponent p x)]
  rw [hay_eq, haz_eq] at hq
  exact residual_quotient_eq_of_qpow_span_quotient_eq (A := A) p M hq

include hroots in
/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation at `d` differs from the
evaluation at the canonical `p`-regular component of `conjClassRepresentative d` by an element of
the residual ideal `M`. This is the exact Chapter `10` congruence step missing from the current
dependency-closed imports. -/
theorem residual_valueAtConjClass_eq_canonical_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (ξ : A ⊗R(G)) :
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) =
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) := by
  -- Apply the representative-level residue congruence to the source-chosen representative of `d`.
  simpa [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d] using
    residual_valueAtConjClass_eq_pregular_component
      (A := A) (hroots := hroots) (G := G) p M
      (Proposition_11_11_4_1.conjClassRepresentative (G := G) d) ξ

include hroots in
/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation at `d` differs from the
evaluation at the canonical `p`-regular component of `conjClassRepresentative d` by an element of
the residual ideal `M`. This is now a direct corollary of the quotient-level source congruence. -/
theorem value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
        tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
      M.1.asIdeal := by
  -- Pass to the quotient `A / M`, where the missing Chapter `10` step is exactly an equality.
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  calc
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
          tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
            (ConjClasses.mk
              (pRegularComponent p
                (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) =
      Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) -
        Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
            (ConjClasses.mk
              (pRegularComponent p
                (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) := by
          simp
    _ = 0 := by
          rw [residual_valueAtConjClass_eq_canonical_pregular_component
            (A := A) (hroots := hroots) (G := G) p M d ξ]
          simp

include hroots in
/-- Helper for Proposition 11-11.4-1: if `x` lies in the owner carrier of `d`, then the fixed
class evaluations at `d` and at `ConjClasses.mk x` differ by an element of the residual ideal
`M`. This is the exact bridge needed in the final contradiction argument. -/
theorem value_at_conj_class_sub_mem_residual_of_mem_owner_carrier
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
        tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∈
      M.1.asIdeal := by
  -- Rewrite the owner representative to the canonical `p`-regular representative, so only the
  -- Chapter `10` congruence for `d` remains.
  rw [owner_representative_value_eq_canonical_pregular_component_value
    (A := A) (hroots := hroots) (G := G) p d hx ξ]
  exact
    value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
      (A := A) (hroots := hroots) (G := G) p M d ξ

-- TODO: start from the Chapter `10.10.3.3` auxiliary tensor on the associated subgroup
-- `associatedPElementarySubgroup p x P`, transport it from `integralClosure ℤ ℂ` to `A` using
-- `transport_integralClosure_tensorCharacter_realization`, and then use induction in stages to
-- place the resulting ambient tensor inside `I_H`.
-- Route correction: the subgroup-of-`H` transport is now isolated in
-- `induced_realization_mem_tensorCharacterRingInductionIdeal_of_le`, and the owner-side witness is
-- now packaged by `associated_owner_induction_witness_not_mem_owner_value_comap`. The remaining
-- blocker is the Chapter `10` congruence from the ordinary class `d` to its canonical `p`-regular
-- component modulo `M`.
include hroots in
theorem associated_owner_induction_witness_not_mem_value_comap
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G)
    (hAssoc :
      HasAssociatedPElementarySubgroupInClass
        (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) H ∧
      ξ ∉ (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  rcases hAssoc with ⟨x, hx, P, hP⟩
  rcases associated_owner_induction_witness_not_mem_owner_value_comap
      (A := A) (hroots := hroots) (G := G) (p := p) (M := M) (d := d) (H := H) hx P hP with
    ⟨ξ, hξ_mem, hξ_notmem⟩
  refine ⟨ξ, hξ_mem, ?_⟩
  change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ ∉ M.1.asIdeal
  change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∉
      M.1.asIdeal at hξ_notmem
  intro hξd
  have hquot_d :
      Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) = 0 := by
    -- The assumed membership at `d` is exactly quotient-zero in `A / M`.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hξd
  have hcanon :
      tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
        M.1.asIdeal := by
    -- The missing Chapter `10` congruence identifies the quotient values at `d` and at the
    -- canonical `p`-regular component.
    have hquot_canonical :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
              (ConjClasses.mk
                (pRegularComponent p
                  (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) = 0 := by
      calc
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G)
              (ConjClasses.mk
                (pRegularComponent p
                  (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) =
          Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) := by
              symm
              exact residual_valueAtConjClass_eq_canonical_pregular_component
                (A := A) (hroots := hroots) (G := G) p M d ξ
        _ = 0 := hquot_d
    exact Ideal.Quotient.eq_zero_iff_mem.mp hquot_canonical
  have hξx :
      tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∈ M.1.asIdeal := by
    -- The owner representative lies in the same canonical `p`-regular class, so the already
    -- settled owner-side transport converts canonical membership into owner membership.
    exact
      (canonical_pregular_component_value_mem_residual_iff_owner_representative
        (A := A) (hroots := hroots) (G := G) p M d hx ξ).mp hcanon
  exact hξ_notmem hξx

include hroots in
/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation pullback over `M` already
satisfies Serre's intrinsic regular-prime criterion for the canonical `p`-regular owner of `d`. -/
theorem value_comap_isTensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    IsTensorCharacterRingRegularPrime (A := A) (G := G) p M
      (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d)
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)) := by
  constructor
  · -- The evaluation pullback contracts to the chosen maximal ideal because fixed-class
    -- evaluation fixes scalar tensors.
    exact value_comap_eq_fixed_maximal (A := A) (hroots := hroots) (G := G) p M d
  · intro H
    constructor
    · intro hcontain hAssoc
      -- An associated owner subgroup forces an explicit element of `I_H` to survive modulo `M`,
      -- so `I_H` cannot be contained in the pullback prime.
      rcases associated_owner_induction_witness_not_mem_value_comap
          (A := A) (hroots := hroots) (G := G) p M d H hAssoc with ⟨ξ, hξ_mem, hξ_notmem⟩
      exact hξ_notmem (hcontain hξ_mem)
    · intro hNotAssoc
      -- The forward containment direction is exactly the Chapter `11.3` divisibility argument
      -- already packaged at the canonical owner representative.
      let ccanon : ConjClasses G :=
        ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))
      have hcanonical :
          tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
            (PrimeSpectrum.comap
              (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon)
              (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal :=
        tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_canonical_representative
          (A := A) (hroots := hroots) (G := G) p M d H hNotAssoc
      intro ξ hξ
      change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ ∈ M.1.asIdeal
      have hcanonical_mem :
          tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon ξ ∈ M.1.asIdeal :=
        by
          change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon ξ ∈ M.1.asIdeal
          exact hcanonical hξ
      have hdiff :
          tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
              tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon ξ ∈
            M.1.asIdeal :=
        value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
          (A := A) (hroots := hroots) (G := G) p M d ξ
      rw [show tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ =
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
              tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon ξ) +
            tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) ccanon ξ by
            exact (sub_add_cancel _ _).symm]
      exact M.1.asIdeal.add_mem hdiff hcanonical_mem

include hroots in
/-- Helper for Proposition 11-11.4-1: the regular-branch prime indexed by a `p`-regular owner
class `c` and a residual-characteristic maximal ideal `M` is the pullback of `M` along fixed-class
evaluation on the underlying ordinary conjugacy class of `c`. -/
def tensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularConjClass G p) : SpecARG :=
  PrimeSpectrum.comap
    (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c : ConjClasses G))
    (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)

include hroots in
/-- Helper for Proposition 11-11.4-1: the remaining nonzero source branch should identify the
fixed-class evaluation pullback over `M` with Serre's canonical regular prime indexed by the
owner `p`-regular class of `d`. -/
theorem value_comap_eq_tensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
      (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
        tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) := by
  let c : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d
  let x : G := Proposition_11_11_4_1.conjClassRepresentative (G := G) (c : ConjClasses G)
  have hx : x ∈ (c : ConjClasses G).carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr
      (Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (c : ConjClasses G))
  apply PrimeSpectrum.ext
  ext ξ
  change tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ ∈ M.1.asIdeal ↔
    tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c : ConjClasses G) ξ ∈ M.1.asIdeal
  have hsub :
      tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ -
          tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ ∈
        M.1.asIdeal :=
    value_at_conj_class_sub_mem_residual_of_mem_owner_carrier
      (A := A) (hroots := hroots) (G := G) p M d
      (by simpa [c, x] using hx) ξ
  have hquot :
      Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) =
        Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (ConjClasses.mk x) ξ) :=
    Ideal.Quotient.eq.mpr hsub
  rw [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (c : ConjClasses G)] at hquot
  constructor
  · intro hmem
    have hzero :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hzero' :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c : ConjClasses G) ξ) = 0 := by
      rw [← hquot]
      exact hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero'
  · intro hmem
    have hzero :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) (c : ConjClasses G) ξ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hzero' :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d ξ) = 0 := by
      rw [hquot]
      exact hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero'

include hroots in
/-- Proposition 11-11.4-1: if with each ordinary conjugacy class `c` we associate `P₀,c`, and
with each `p`-regular class `c` and residual-characteristic maximal ideal `M` we associate
`P_{M,c}`, then every prime ideal of `A ⊗ R(G)` occurs exactly once in one of these two
families. -/
theorem tensor_character_ring_prime_ideal_classification
    (𝔭 : SpecARG) :
    (∃ c : ConjClasses G, tensorCharacterRingZeroPrimeIdeal A c = 𝔭) ∨
      ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
        ∃ c : PRegularConjClass G p,
          tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M c = 𝔭 := by
  -- Start from the verified source-spectrum presentation and only rewrite the nonzero branch
  -- through the canonical regular-owner parameter.
  rcases tensor_character_ring_prime_ideal_source_presentation (A := A) (hroots := hroots) (G := G) 𝔭 with h𝔭 | h𝔭
  · exact Or.inl h𝔭
  · rcases h𝔭 with ⟨p, M, d, hd⟩
    refine Or.inr ⟨p, M,
      Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d, ?_⟩
    -- The remaining rewrite is exactly the regular-branch owner identification above.
    calc
      tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) =
          PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (hroots := hroots) (G := G) d)
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
              symm
              exact value_comap_eq_tensorCharacterRingRegularPrime (A := A) (hroots := hroots) (G := G) p M d
      _ = 𝔭 := hd

section

-- Cache the `Fintype` instances with the same spelling as the section of
-- `Serre.Chap11.Proposition_11_11_4_1.OwnersAndPrimeFibers` that defines the bottom-fiber owner
-- API; without them the statement below re-synthesizes mismatching instance terms inside the
-- fiber types and blows the default elaboration budget on `isDefEq` checks.
local instance primeOverBotFibersFintypeGroup : Fintype G := Fintype.ofFinite G
local instance primeOverBotFibersFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Proposition 11-11.4-1: any prime of `A ⊗ R(G)` whose contraction to `A` is `(0)` is
canonically recovered from the corresponding point of the bottom fiber. This remains a thin
compatibility wrapper around the extracted owner API while the full Proposition 30 classification
is reconstructed on top of it. -/
theorem tensor_character_ring_prime_over_bot_to_fiber_symm
    {𝔭 : SpecARG}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥) :
    ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
      (prime_over_bot_to_fiber (A := A) 𝔭 h𝔭)).1 =
        𝔭.asIdeal := by
  -- This is the standard bottom-fiber normalization already verified in the extracted owner API,
  -- with a statement-identical wrapper; `exact` avoids re-normalizing the large fiber terms.
  exact prime_over_bot_to_fiber_symm (A := A) (G := G) 𝔭 h𝔭

end

end
