import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Proposition_9_9_4_2
import LinearRepresentations_Serre_1977.Serre.Chap09.Theorem_9_9_2_1
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_1_2
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_2

-- Stable restriction and pairing helpers extracted from Exercise 11-11.2-7.

noncomputable section

universe u v

namespace Representation

open scoped BigOperators Representation SubgroupInduction

section FrobeniusTheorem

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance restrictionAndPairingFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Conjugacy classes in a finite group form a finite type. -/
local instance restrictionAndPairingFintypeConjClasses
    (H : Type*) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Equality of subgroups is decidable by classical choice in this file-local proof environment. -/
local instance restrictionAndPairingDecidableEqSubgroup
    (H : Type*) [Group H] : DecidableEq (Subgroup H) :=
  Classical.decEq _

/-- Helper for Exercise 11-11.2-7: the globally weighted Adams transform preserves the same
prime-to-`|G|` power-invariance hypothesis. -/
lemma weighted_adamsOperator_power_invariant
    (n : ℕ+) (f : classFunctionSubmodule ℤ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x)
    (x : G) (m : ℕ) (hm : Nat.Coprime m (Nat.card G)) :
    ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) (x ^ m)) =
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x) := by
  let k : ℤ := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ)
  have hpow' := hpow (x ^ (n : ℕ)) m hm
  calc
    k * Ψ^n(f) (x ^ m) = k * f ((x ^ m) ^ (n : ℕ)) := by
      simp [k, Representation.adamsOperator]
    _ = k * f ((x ^ (n : ℕ)) ^ m) := by
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = k * f (x ^ (n : ℕ)) := by
      exact congrArg (fun z : ℤ ↦ k * z) hpow'
    _ = k * Ψ^n(f) x := by
      simp [k, Representation.adamsOperator]

/-- Helper for Exercise 11-11.2-7: restricting an integer-valued bundled class function to a
subgroup preserves the class-function condition. -/
lemma int_classFunctionRestriction_mem
    (H : Subgroup G) (f : classFunctionSubmodule ℤ G) :
    (fun h : H ↦ f h) ∈ classFunctionSubmodule ℤ H := by
  let hf : _root_.IsClassFunction (f : G → ℤ) := (mem_classFunctionSubmodule_iff ℤ _).1 f.2
  refine (mem_classFunctionSubmodule_iff ℤ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxyH : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hxyG : IsConj (x : G) (y : G) := by
    rw [isConj_iff] at hxyH ⊢
    rcases hxyH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact hf.eq_of_isConj hxyG

/-- Helper for Exercise 11-11.2-7: the normalized pairing of two honest characters is the
dimension of the intertwining space. -/
lemma groupFunctionPairing_character_eq_finrank_intertwiningMap_local
    {H : Type u} [Group H] [Finite H]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ H V) (ρ : Representation ℂ H W) :
    ⟪σ.character, ρ.character⟫ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  let _ : Fintype H := Fintype.ofFinite H
  letI : NeZero (Nat.card H : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card H : ℂ))
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ))

/-- Helper for Exercise 11-11.2-7: subgroup restriction of an integer-valued bundled class
function. -/
def int_classFunctionRestriction
    (H : Subgroup G) (f : classFunctionSubmodule ℤ G) :
    classFunctionSubmodule ℤ H :=
  ⟨fun h ↦ f h, int_classFunctionRestriction_mem (G := G) H f⟩

/-- Helper for Exercise 11-11.2-7: restricting a realized scalar-extension class function to a
subgroup preserves realized scalar-extension membership. -/
lemma classFunctionRestriction_mem_characterRingScalarExtension
    {A : Type*} [CommRing A] [Algebra A ℂ]
    (H : Subgroup G) {η : G → ℂ}
    (hη : η ∈ characterRingScalarExtension A G) :
    (fun h : H ↦ η h) ∈ characterRingScalarExtension A H := by
  rw [characterRingScalarExtension] at hη ⊢
  refine
    Submodule.span_induction
      (s := (R(G) : Set (G → ℂ)))
      (p := fun ψ _ ↦
        (fun h : H ↦ ψ h) ∈ Submodule.span A (R(H) : Set (H → ℂ)))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    have hres : (fun h : H ↦ ψ h) ∈ R(H) := by
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hψ
      · intro χ hχ
        rcases hχ with ⟨σ, hσfd, _hσirr, rfl⟩
        letI : FiniteDimensional ℂ σ := hσfd
        simpa using
          (Representation.rep_character_mem_characterRing
            (Rep.res H.subtype (Rep.of σ.ρ)))
      · intro n
        exact (R(H)).algebraMap_mem n
      · intro f g _ _ hf hg
        simpa using (R(H)).add_mem hf hg
      · intro f g _ _ hf hg
        simpa using (R(H)).mul_mem hf hg
    exact Submodule.subset_span hres
  · exact Submodule.zero_mem (Submodule.span A (R(H) : Set (H → ℂ)))
  · intro ψ ξ _ _ hψ hξ
    simpa using (Submodule.add_mem (Submodule.span A (R(H) : Set (H → ℂ))) hψ hξ)
  · intro a ψ _ hψ
    simpa using (Submodule.smul_mem (Submodule.span A (R(H) : Set (H → ℂ))) a hψ)

/-- Helper for Exercise 11-11.2-7: pairing a virtual character with an honest representation
character lands in the image of `ℤ`. -/
lemma characterRing_pairing_mem_range_int_with_rep_character
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (η : R(H)) (ρ : Representation ℂ H W) :
    ⟪(η : H → ℂ), ρ.character⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
  let S : Set (H → ℂ) :=
    { ψ |
        ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
          (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : H → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : H → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          have hψ' :
              ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
                ψ = σ.character := by
            simpa [S] using hψ
          rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              have hξ' :
                  ∃ (Y : Type u) (_ : AddCommGroup Y) (_ : Module ℂ Y)
                    (_ : FiniteDimensional ℂ Y) (τ : Representation ℂ H Y),
                    ξ = τ.character := by
                simpa [S] using hξ
              rcases hξ' with ⟨Y, _instYAdd, _instYMod, _instYfd, τ, rfl⟩
              let π : Representation ℂ H (TensorProduct ℂ X Y) := σ.tprod τ
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ X Y, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : H → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact
                (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : H → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : H → ℂ) ∈ Submodule.span ℤ S := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span
        ⟨(σ : Type u), inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ H (ULift.{u} ℂ)).character = (1 : H → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      rw [show algebraMap ℤ (H → ℂ) n =
          n • (Representation.trivial ℂ H (ULift.{u} ℂ)).character by
        ext x
        simp [htriv]]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ULift.{u} ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ H (ULift.{u} ℂ), rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  refine
    Submodule.span_induction
      (p := fun ψ _ ↦ ⟪ψ, ρ.character⟫ ∈ Set.range (algebraMap ℤ ℂ))
      ?_ ?_ ?_ ?_ hηspan
  · intro ψ hψ
    have hψ' :
        ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
          (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
          ψ = σ.character := by
      simpa [S] using hψ
    rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
    rw [groupFunctionPairing_character_eq_finrank_intertwiningMap_local σ ρ]
    exact ⟨(Module.finrank ℂ (σ.IntertwiningMap ρ) : ℤ), by simp⟩
  · change groupFunctionPairingOverField ℂ (0 : H → ℂ) ρ.character ∈
      Set.range (algebraMap ℤ ℂ)
    exact ⟨0, by simp [Representation.groupFunctionPairingOverField]⟩
  · intro ψ ξ _ _ hψ hξ
    rcases hψ with ⟨a, ha⟩
    rcases hξ with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    calc
      algebraMap ℤ ℂ (a + b) = algebraMap ℤ ℂ a + algebraMap ℤ ℂ b := by simp
      _ = groupFunctionPairingOverField ℂ ψ ρ.character +
            groupFunctionPairingOverField ℂ ξ ρ.character := by
          rw [ha, hb]
      _ = groupFunctionPairingOverField ℂ (ψ + ξ) ρ.character := by
          rw [Representation.groupFunctionPairing_add_left]
  · intro n ψ _ hψ
    rcases hψ with ⟨a, ha⟩
    refine ⟨n * a, ?_⟩
    calc
      algebraMap ℤ ℂ (n * a) = (n : ℂ) * algebraMap ℤ ℂ a := by
        simp [map_mul, mul_comm]
      _ = (n : ℂ) * groupFunctionPairingOverField ℂ ψ ρ.character := by rw [ha]
      _ = groupFunctionPairingOverField ℂ (n • ψ) ρ.character := by
        symm
        simpa [zsmul_eq_mul] using
          (Representation.groupFunctionPairing_smul_left
            (a := (n : ℂ)) (φ := ψ) (ψ := ρ.character))

/-- Helper for Exercise 11-11.2-7: pairing a rational scalar-extended class function with a
linear character lands in the image of `ℚ`. -/
lemma pairing_mem_range_rat_of_mem_characterRingScalarExtension
    {H : Type u} [Group H] [Finite H]
    (η : H → ℂ) (hη : η ∈ characterRingScalarExtension ℚ H) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, η⟫ ∈ Set.range (algebraMap ℚ ℂ) := by
  rw [Representation.groupFunctionPairing_comm]
  rw [characterRingScalarExtension] at hη
  refine
    Submodule.span_induction
      (s := (R(H) : Set (H → ℂ)))
      (p := fun ψ _ ↦ ⟪ψ, χ.toRepresentation.character⟫ ∈ Set.range (algebraMap ℚ ℂ))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    let ηR : R(H) := ⟨ψ, hψ⟩
    rcases characterRing_pairing_mem_range_int_with_rep_character (η := ηR) χ.toRepresentation with
      ⟨a, ha⟩
    exact ⟨(a : ℚ), by simpa using ha⟩
  · change groupFunctionPairingOverField ℂ (0 : H → ℂ) χ.toRepresentation.character ∈
      Set.range (algebraMap ℚ ℂ)
    exact ⟨0, by simp [Representation.groupFunctionPairingOverField]⟩
  · intro ψ ξ _ _ hψ hξ
    rcases hψ with ⟨a, ha⟩
    rcases hξ with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simpa [Representation.groupFunctionPairing_add_left, ha, hb, map_add]
  · intro a ψ _ hψ
    rcases hψ with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have hsmul :
        ⟪a • ψ, χ.toRepresentation.character⟫ =
          algebraMap ℚ ℂ a * ⟪ψ, χ.toRepresentation.character⟫ := by
      simpa using
        (Representation.groupFunctionPairing_smul_left
          (a := algebraMap ℚ ℂ a) (φ := ψ) (ψ := χ.toRepresentation.character))
    rw [hsmul]
    simpa [hb, map_mul, mul_assoc]

/-- Helper for Exercise 11-11.2-7: pairing a rational scalar-extended class function with an
honest representation character lands in the image of `ℚ`. -/
lemma pairing_mem_range_rat_of_mem_characterRingScalarExtension_with_rep_character
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (η : H → ℂ) (hη : η ∈ characterRingScalarExtension ℚ H) (ρ : Representation ℂ H W) :
    ⟪η, ρ.character⟫ ∈ Set.range (algebraMap ℚ ℂ) := by
  rw [characterRingScalarExtension] at hη
  refine
    Submodule.span_induction
      (s := (R(H) : Set (H → ℂ)))
      (p := fun ψ _ ↦ ⟪ψ, ρ.character⟫ ∈ Set.range (algebraMap ℚ ℂ))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    let ηR : R(H) := ⟨ψ, hψ⟩
    rcases characterRing_pairing_mem_range_int_with_rep_character (η := ηR) ρ with ⟨a, ha⟩
    exact ⟨(a : ℚ), by simpa using ha⟩
  · change groupFunctionPairingOverField ℂ (0 : H → ℂ) ρ.character ∈
      Set.range (algebraMap ℚ ℂ)
    exact ⟨0, by simp [Representation.groupFunctionPairingOverField]⟩
  · intro ψ ξ _ _ hψ hξ
    rcases hψ with ⟨a, ha⟩
    rcases hξ with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simpa [Representation.groupFunctionPairing_add_left, ha, hb, map_add]
  · intro a ψ _ hψ
    rcases hψ with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have hsmul :
        ⟪a • ψ, ρ.character⟫ = algebraMap ℚ ℂ a * ⟪ψ, ρ.character⟫ := by
      simpa using
        (Representation.groupFunctionPairing_smul_left
          (a := algebraMap ℚ ℂ a) (φ := ψ) (ψ := ρ.character))
    rw [hsmul]
    simpa [hb, map_mul, mul_assoc]

/-- Helper for Exercise 11-11.2-7: in the irreducible-character basis coming from a complete
family, each coefficient is the normalized pairing with the corresponding irreducible character. -/
lemma repr_irreducible_character_basis_eq_pairing
    {H : Type}
    [Group H] [Finite H]
    {ι : Type*}
    (π : ι → FDRep ℂ H)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Fintype ι]
    (x : classFunctionSubmodule ℂ H) (i : ι) :
    (irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : H → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : H → ℂ) (z : H → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : H → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨CategoryTheory.Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by simp [hij]
    exact hcoord_j.trans hpair_j.symm
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

end FrobeniusTheorem

end Representation
