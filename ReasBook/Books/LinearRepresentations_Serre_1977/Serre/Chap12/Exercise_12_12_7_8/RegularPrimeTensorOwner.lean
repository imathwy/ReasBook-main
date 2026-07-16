import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_7_8.ScalarExtensionTransport
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_2

open scoped Representation
open Lean Elab Term Meta

noncomputable section

universe u v w

namespace Representation

/-- Term elaborator for the earlier Chapter 12 irreducible-family witness used to avoid
duplicating the regular-representation quotient construction in this file. -/
elab "privateCompleteIrreducibleFamilyWitness" : term => do
  let n :=
    Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "Serre")
              "Chap12")
            "Proposition_12_12_1_2")
          0)
        "Representation")
      "exists_complete_pairwise_nonisomorphic_irreducible_family"
  return (← mkConstWithFreshMVarLevels n)

open CategoryTheory
section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278RegularPrimeTensorOwnerGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278RegularPrimeTensorOwnerGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

/-- Helper for Exercise 12-12.7-8: choose a complex embedding of the intermediate field `K` so
the earlier Chapter 12 irreducible-family result can be reused without reproving it locally. -/
private noncomputable def intermediateFieldToComplex : K →+* ℂ :=
  NumberField.ComplexEmbedding.lift K (algebraMap ℚ ℂ)

/-- Helper for Exercise 12-12.7-8: the chosen embedding equips the intermediate field `K` with
the `ℂ`-algebra structure required by the imported irreducible-family witness. -/
noncomputable local instance intermediateFieldAlgebraComplex : Algebra K ℂ :=
  RingHom.toAlgebra (intermediateFieldToComplex (K := K))

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}
variable {R : Type*}

/-- Serre's defining characterization of the regular prime `P_{M,c}` in `A ⊗ R_K(G)` in the
Chapter `12` arithmetic setting where `K` is the fraction field of the domain `A`: it lies over
the maximal ideal `M`, and its residue condition is detected by evaluation on the chosen
`p`-regular `Γ_K`-class `c`. -/
def IsGaloisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) (P : SpecAKG) : Prop :=
  Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
      P.asIdeal = M.1.asIdeal ∧
    ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
      f ∈ P.asIdeal ↔
        ∀ x : { x : G // IsPRegular p x },
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1

/-- Helper for Exercise 12-12.7-8: a function on `p`-regular conjugacy classes descends to
Serre's quotient `PRegularGaloisPowerClass ΓK p` once it is invariant under the `Γ_K` power
action. This is the quotient step used by the regular-fiber evaluator after first working on
honest `p`-regular representatives. -/
def pRegularGaloisPowerClassLift
    (f : PRegularConjClass G p → R)
    (hf : ∀ t : ΓK, ∀ c : PRegularConjClass G p, f (t • c) = f c) :
    PRegularGaloisPowerClass ΓK p → R :=
  Quotient.lift f <| by
    intro a b hab
    rcases hab with ⟨t, rfl⟩
    simpa using hf t _

/-- Helper for Exercise 12-12.7-8: to prove equality of functions on Serre's `p`-regular
`Γ_K`-classes, it suffices to check equality on `p`-regular representatives. This keeps later
regular-fiber extensionality arguments on the source-faithful representative level. -/
theorem pRegularGaloisPowerClass_funext
    {f g : PRegularGaloisPowerClass ΓK p → R}
    (hfg : ∀ x : {x : G // IsPRegular p x},
      f (pRegularGaloisPowerClassMk ΓK p x) = g (pRegularGaloisPowerClassMk ΓK p x)) :
    f = g := by
  ext c
  obtain ⟨x, rfl⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p c
  exact hfg x

/-- Helper for Exercise 12-12.7-8: evaluating a descended function on the `Γ_K`-class of a chosen
`p`-regular representative returns the original representative-level value. This is the direct
quotient-lift interface used before comparing Serre's regular-fiber zero tests. -/
@[simp] theorem pRegularGaloisPowerClassLift_mk
    (f : PRegularConjClass G p → R)
    (hf : ∀ t : ΓK, ∀ c : PRegularConjClass G p, f (t • c) = f c)
    (x : {x : G // IsPRegular p x}) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) f hf
        (pRegularGaloisPowerClassMk ΓK p x) =
      f (PRegularConjClass.ofSubtype p x) := by
  rfl

/-- Helper for Exercise 12-12.7-8: at the `Γ_K`-class of a chosen representative, vanishing of a
descended function is equivalent to vanishing of the original representative-level value. This is
the source-faithful bridge used when quotient-level zero statements are normalized back to honest
`p`-regular representatives. -/
@[simp] theorem pRegularGaloisPowerClassLift_mk_eq_zero_iff
    {R : Type*} [Zero R]
    (f : PRegularConjClass G p → R)
    (hf : ∀ t : ΓK, ∀ c : PRegularConjClass G p, f (t • c) = f c)
    (x : {x : G // IsPRegular p x}) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) f hf
        (pRegularGaloisPowerClassMk ΓK p x) = 0 ↔
      f (PRegularConjClass.ofSubtype p x) = 0 := by
  rw [pRegularGaloisPowerClassLift_mk (K := K) (G := G) (p := p) f hf x]

/-- Helper for Exercise 12-12.7-8: once a function on `p`-regular conjugacy classes descends to
Serre's quotient `PRegularGaloisPowerClass ΓK p`, vanishing at a quotient class is equivalent to
vanishing on every `p`-regular representative of that class. This is the exact descent interface
used to turn the representative-level residue test into the quotient-level formula. -/
theorem pRegularGaloisPowerClassLift_eq_zero_iff_forall_representatives_eq_zero
    {R : Type*} [Zero R]
    (f : PRegularConjClass G p → R)
    (hf : ∀ t : ΓK, ∀ c : PRegularConjClass G p, f (t • c) = f c)
    (c : PRegularGaloisPowerClass ΓK p) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) f hf c = 0 ↔
      ∀ x : {x : G // IsPRegular p x},
        pRegularGaloisPowerClassMk ΓK p x = c →
          f (PRegularConjClass.ofSubtype p x) = 0 := by
  constructor
  · intro hc x hx
    subst hx
    simpa [pRegularGaloisPowerClassLift, pRegularGaloisPowerClassMk] using hc
  · intro hzero
    obtain ⟨x, rfl⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p c
    simpa [pRegularGaloisPowerClassLift, pRegularGaloisPowerClassMk] using hzero x rfl

/-- Helper for Exercise 12-12.7-8: the abstract tensor owner `A ⊗ R_K(G)` realized as a
`K`-valued function. This is the source-side owner used before passing to any fixed fiber. -/
abbrev tensorCharacterRingRealization :
    TensorProduct ℤ A (R[K](G)) →ₗ[A] G → K :=
  (Representation.characterRingOverFieldAlgebraScalarExtension A K G).subtype.comp
    (((R[K](G)).toSubmodule).tensorToSpan A)

/-- Helper for Exercise 12-12.7-8: on pure tensors, the abstract tensor-owner realization gives
the expected scalar multiple of the underlying character. -/
theorem tensorCharacterRingRealization_apply_tmul
    (a : A) (χ : R[K](G)) :
    tensorCharacterRingRealization (A := A) (K := K) (G := G) (a ⊗ₜ[ℤ] χ) =
      a • (χ : G → K) := by
  rfl

/-- Helper for Exercise 12-12.7-8: realizing a finite `A`-linear combination in the tensor owner
evaluates coefficientwise on the corresponding virtual characters. This is the realization-side
expansion needed before pairing with irreducible characters to prove injectivity. -/
theorem tensorCharacterRingRealization_finsupp_sum
    {ι : Type*} (b : Module.Basis ι ℤ (R[K](G))) (c : ι →₀ A) :
    tensorCharacterRingRealization (A := A) (K := K) (G := G)
      (c.sum fun i a ↦ a ⊗ₜ[ℤ] b i) =
        c.sum fun i a ↦ a • (((b i : R[K](G)) : G → K)) := by
  classical
  simp [Finsupp.sum, map_sum, tensorCharacterRingRealization_apply_tmul]

/-- Helper for Exercise 12-12.7-8: the normalized pairing expands over finite `A`-linear
combinations in its left argument after transporting coefficients along `A → K`. This is the
pairing identity needed to isolate irreducible-basis coefficients in the owner injectivity step.
-/
theorem groupFunctionPairing_sum_algebra_smul_left
    {ι : Type*} (s : Finset ι) (a : ι → A) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, algebraMap A K (a j) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      have hsmul : (a i • χ i : G → K) = algebraMap A K (a i) • χ i := by
        ext g
        simp [Algebra.smul_def, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.7-8: realizing an abstract tensor character in `A ⊗ R_K(G)`
already lands in Serre's scalar-extension owner `A ⊗ R_K(G) ⊂ (G → K)`. This is the source-side
normalization used before any fixed-fiber or quotient descent. -/
theorem tensorCharacterRingToFunction_mem_owner
    (ξ : TensorProduct ℤ A (R[K](G))) :
    tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ ∈
      characterRingOverFieldAlgebraScalarExtension A K G := by
  induction ξ using TensorProduct.induction_on with
  | zero =>
      simpa using (characterRingOverFieldAlgebraScalarExtension A K G).zero_mem
  | tmul a χ =>
      simpa [tensorCharacterRingRealization_apply_tmul] using
        (characterRingOverFieldAlgebraScalarExtension A K G).smul_mem a
          (mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
            (A := A) (K := K) (G := G) χ.property)
  | add ξ η hξ hη =>
      simpa [map_add] using
        (characterRingOverFieldAlgebraScalarExtension A K G).add_mem hξ hη

/-- Helper for Exercise 12-12.7-8: the abstract tensor owner `A ⊗ R_K(G)` maps linearly into
Serre's scalar-extension owner by realization as a `K`-valued function. -/
noncomputable def tensorCharacterRingToOwnerLinearMap :
    TensorProduct ℤ A (R[K](G)) →ₗ[A] characterRingOverFieldAlgebraScalarExtension A K G :=
  (tensorCharacterRingRealization (A := A) (K := K) (G := G)).codRestrict
    (characterRingOverFieldAlgebraScalarExtension A K G)
    (tensorCharacterRingToFunction_mem_owner (A := A) (K := K) (G := G))

/-- Helper for Exercise 12-12.7-8: every element of Serre's scalar-extension owner is realized by
an abstract tensor character. This is the source-level lifting step used to normalize the fixed
fiber before residue-field evaluation is introduced. -/
theorem exists_tensorCharacterRing_preimage_of_mem_owner
    {f : G → K}
    (hf : f ∈ characterRingOverFieldAlgebraScalarExtension A K G) :
    ∃ ξ : TensorProduct ℤ A (R[K](G)),
      tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ = f := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      refine ⟨1 ⊗ₜ[ℤ] (⟨g, by simpa using hg⟩ : R[K](G)), ?_⟩
      simp [tensorCharacterRingRealization_apply_tmul]
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨ξg, rfl⟩
      rcases hh with ⟨ξh, rfl⟩
      refine ⟨ξg + ξh, ?_⟩
      simp [map_add]
  | smul a g _ hg =>
      rcases hg with ⟨ξg, rfl⟩
      refine ⟨a • ξg, ?_⟩
      simp

/-- Helper for Exercise 12-12.7-8: every element of Serre's scalar-extension owner is realized by
an abstract tensor character. This is the surjective half of the fiber-to-tensor normalization
used in the regular-fiber route. -/
theorem tensorCharacterRingToOwnerLinearMap_surjective :
    Function.Surjective (tensorCharacterRingToOwnerLinearMap (A := A) (K := K) (G := G)) := by
  intro f
  obtain ⟨ξ, hξ⟩ :=
    exists_tensorCharacterRing_preimage_of_mem_owner (A := A) (K := K) (G := G) f.2
  refine ⟨ξ, ?_⟩
  apply Subtype.ext
  exact hξ

/-- Helper for Exercise 12-12.7-8: the realized tensor owner is already a class function on `G`.
This is the source-faithful interface needed before descending to `p`-regular representative
classes. -/
theorem tensorCharacterRingRealization_isClassFunction
    (ξ : TensorProduct ℤ A (R[K](G))) :
    _root_.IsClassFunction (tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ) := by
  let S := (((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))
  let p : ∀ f : G → K, f ∈ Submodule.span A S → Prop :=
    fun f _ ↦ _root_.IsClassFunction f
  have hp :
      p (tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ)
        (tensorCharacterRingToFunction_mem_owner (A := A) (K := K) (G := G) ξ) := by
    refine Submodule.span_induction (s := S) (p := p) ?_ ?_ ?_ ?_
      (tensorCharacterRingToFunction_mem_owner (A := A) (K := K) (G := G) ξ)
    · intro ψ hψ
      exact Representation.isClassFunction_of_mem_characterRingOverField ψ (by simpa [S] using hψ)
    · simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
    · intro f g _ _ hf hg
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      simpa using (inferInstance : _root_.IsClassFunction (f + g))
    · intro a f _ hf
      letI : _root_.IsClassFunction f := hf
      simpa using (inferInstance : _root_.IsClassFunction (a • f))
  exact hp

/-- Helper for Exercise 12-12.7-8: before quotienting by `Γ_K`, a realized tensor character
already descends to honest `p`-regular conjugacy classes. This is the representative-level owner
used in Serre's regular-fiber route. -/
def tensorCharacterRingPRegularLift_local
    (p : ℕ) (ξ : TensorProduct ℤ A (R[K](G))) :
    PRegularConjClass G p → K :=
  (tensorCharacterRingRealization_isClassFunction (A := A) (K := K) (G := G) ξ).pRegularLift p

/-- Helper for Exercise 12-12.7-8: evaluating the descended tensor owner on a chosen `p`-regular
representative returns the original tensor-character value. This keeps later residue arguments on
Serre's source-level representative side. -/
@[simp] theorem tensorCharacterRingPRegularLift_local_ofSubtype
    (p : ℕ) (ξ : TensorProduct ℤ A (R[K](G)))
    (x : {x : G // IsPRegular p x}) :
    tensorCharacterRingPRegularLift_local (A := A) (K := K) (G := G) p ξ
        (PRegularConjClass.ofSubtype p x) =
      tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ x.1 := by
  simpa [tensorCharacterRingPRegularLift_local] using
    IsClassFunction.pRegularLift_ofSubtype
      (hf := tensorCharacterRingRealization_isClassFunction (A := A) (K := K) (G := G) ξ)
      x

/-- Helper for Exercise 12-12.7-8: on a pure tensor, the descended representative-level owner
evaluates as the expected scalar multiple of the underlying virtual character. This is the
rewrite-friendly source formula needed before introducing residue classes. -/
@[simp] theorem tensorCharacterRingPRegularLift_local_tmul_ofSubtype
    (p : ℕ) (a : A) (χ : R[K](G))
    (x : {x : G // IsPRegular p x}) :
    tensorCharacterRingPRegularLift_local (A := A) (K := K) (G := G) p
        (a ⊗ₜ[ℤ] χ)
        (PRegularConjClass.ofSubtype p x) =
      algebraMap A K a * (χ : G → K) x.1 := by
  rw [tensorCharacterRingPRegularLift_local_ofSubtype,
    tensorCharacterRingRealization_apply_tmul]
  simp [Algebra.smul_def]

/-- Helper for Exercise 12-12.7-8: a finite `A`-linear combination of the characters of a
complete pairwise nonisomorphic irreducible family can vanish only if every coefficient is zero.
This is the coefficient-extraction step in the source-faithful owner injectivity argument. -/
theorem fraction_field_irreducible_character_coefficients_eq_zero
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : ι →₀ A)
    (hc : c.sum (fun i a ↦ a • (π i).character) = 0) :
    c = 0 := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  ext i
  have hpair0 :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ = (0 : K) := by
    simpa [Representation.groupFunctionPairingOverField] using
      congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hc
  have hpair_expand :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ =
        c.sum (fun j a ↦ algebraMap A K a * ⟪(π j).character, (π i).character⟫) := by
    simpa [Finsupp.sum] using
      (groupFunctionPairing_sum_algebra_smul_left
        (A := A) (K := K) (G := G)
        (s := c.support) (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character))
  rw [hpair_expand] at hpair0
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj (π i)
    let e₁ : ((π i) ⟶ (π i)) ≃ₗ[K] (X ⟶ X) :=
      (FDRep.forget₂HomLinearEquiv (π i) (π i)).symm
    let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
    let e : ((π i) ⟶ (π i)) ≃ₗ[K] (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      e₁.trans e₂
    letI : FiniteDimensional K (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
    have hnontriv : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      refine ⟨0, e (𝟙 (π i)), ?_⟩
      intro h
      apply CategoryTheory.id_nonzero (π i)
      exact e.injective h.symm
    letI : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := hnontriv
    have hpair :
        ⟪(π i).character, (π i).character⟫ =
          Module.finrank K (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        K (π i).ρ (π i).ρ
    rw [hpair]
    exact_mod_cast Module.finrank_pos.ne'
  have hpair_single :
      c.sum (fun j a ↦ algebraMap A K a * ⟪(π j).character, (π i).character⟫) =
        algebraMap A K (c i) * ⟪(π i).character, (π i).character⟫ := by
    rw [Finsupp.sum]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hi
      by_cases hci : c i = 0
      · simp [hci]
      · exact (hi (Finsupp.mem_support_iff.2 hci)).elim
  rw [hpair_single] at hpair0
  have hcoeffK : algebraMap A K (c i) = 0 :=
    (mul_eq_zero.mp hpair0).resolve_right hself_ne
  exact (IsFractionRing.injective A K) <| by simpa using hcoeffK

/-- Helper for Exercise 12-12.7-8: rebuilding an `FDRep` from its underlying representation gives
a canonical isomorphism. This keeps the complete-family proof on the representation side while
returning to the bundled `FDRep` owner only at the end. -/
noncomputable def fdRepIsoOfRho_local (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun _ => rfl

/-- Helper for Exercise 12-12.7-8: precomposing with a representation equivalence identifies the
corresponding intertwining spaces. This is the direct-sum transport used after decomposing the
regular representation into irreducible summands. -/
noncomputable def intertwiningMapCongrLeft_local
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V₁} {σ : Representation K G V₂}
    (e : ρ.Equiv σ) (τ : Representation K G W) :
    Representation.IntertwiningMap σ τ ≃ₗ[K] Representation.IntertwiningMap ρ τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.7-8: intertwining maps out of a direct sum are equivalent to
compatible families of intertwining maps out of each summand. This is the exact coordinate
extraction step used in the regular-representation quotient argument. -/
noncomputable def directSumIntertwiningMapEquivPi_local
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    Representation.IntertwiningMap (Representation.directSum π) τ ≃ₗ[K]
      ∀ i, Representation.IntertwiningMap (π i) τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.7-8: a nonzero intertwiner between two explicit irreducible
representations is already an equivalence. This is the direct Schur-style step used when the
regular representation decomposition is quotientized to a pairwise nonisomorphic family. -/
theorem nonempty_equiv_of_intertwiningMap_ne_zero_explicit_local
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hf : f ≠ 0) :
    Nonempty (ρ1.Equiv ρ2) := by
  refine ⟨f.ofBijective ?_⟩
  exact
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_right hf

/-- Helper for Exercise 12-12.7-8: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. This is the Schur-style
contrapositive used when quotienting the regular representation by isomorphism classes. -/
theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  by_contra hf
  exact hρ (nonempty_equiv_of_intertwiningMap_ne_zero_explicit_local
    (K := K) (G := G) ρ1 ρ2 f hf)

/-- Helper for Exercise 12-12.7-8: over Serre's fraction field `K`, the left regular
representation still contains a finite complete pairwise nonisomorphic irreducible family. This
is the finite owner basis used to prove injectivity of `A ⊗ R_K(G) → G → K`. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  exact privateCompleteIrreducibleFamilyWitness (K := K) (G := G)

/-- Helper for Exercise 12-12.7-8: realizing the abstract tensor owner `A ⊗ R_K(G)` as a
`K`-valued function is injective. This is the source-level injectivity needed before any residue
field or quotient descent is introduced. -/
theorem tensorCharacterRingRealization_injective :
    Function.Injective (tensorCharacterRingRealization (A := A) (K := K) (G := G)) := by
  classical
  intro ξ η hξη
  have hdiff :
      tensorCharacterRingRealization (A := A) (K := K) (G := G) (ξ - η) = 0 := by
    have hsub := congrArg
      (fun z : G → K ↦ z - tensorCharacterRingRealization (A := A) (K := K) (G := G) η) hξη
    simpa [map_sub] using hsub
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
  letI : Fintype ι := hι
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (R := ℤ) (M := A) (𝒞 := b) (x := ξ - η)
  have hrealized :
      c.sum (fun i a ↦ a • (π i).character) = 0 := by
    have hsum :=
      tensorCharacterRingRealization_finsupp_sum (A := A) (K := K) (G := G) b c
    have hsum' :
        tensorCharacterRingRealization (A := A) (K := K) (G := G)
            (c.sum fun i a ↦ a ⊗ₜ[ℤ] b i) =
          c.sum (fun i a ↦ a • (π i).character) := by
      simpa [b, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using hsum
    rw [← hsum', hc, hdiff]
  have hc_zero : c = 0 :=
    fraction_field_irreducible_character_coefficients_eq_zero
      (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete c hrealized
  have hξη' : ξ - η = 0 := by
    rw [← hc, hc_zero]
    simp
  exact sub_eq_zero.mp hξη'

/-- Helper for Exercise 12-12.7-8: Serre's scalar-extension owner is canonically the same
`A`-module as the abstract tensor owner `A ⊗ R_K(G)`. This isolates the owner-level transport
before base-changing to a fixed residue field. -/
noncomputable def ownerLinearEquiv_tensorCharacterRing :
    characterRingOverFieldAlgebraScalarExtension A K G ≃ₗ[A] TensorProduct ℤ A (R[K](G)) :=
  (LinearEquiv.ofBijective
    (tensorCharacterRingToOwnerLinearMap (A := A) (K := K) (G := G))
    ⟨fun ξ η hξη ↦
        tensorCharacterRingRealization_injective (A := A) (K := K) (G := G)
          (congrArg
            (fun f : characterRingOverFieldAlgebraScalarExtension A K G ↦ (f : G → K))
            hξη),
      tensorCharacterRingToOwnerLinearMap_surjective (A := A) (K := K) (G := G)⟩).symm

end RegularPrime

end

end Representation
