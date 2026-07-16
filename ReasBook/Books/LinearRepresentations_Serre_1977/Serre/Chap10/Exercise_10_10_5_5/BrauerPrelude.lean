import LinearRepresentations_Serre_1977.Serre.Chap10.Exercise_10_10_5_5.AutoSplit
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_2_1

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

-- `conjClassRepresentative` and `conjClassRepresentative_mk` are the canonical declarations from
-- `Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge` (transitively imported); reused directly.

/-- Helper for Exercise 10-10.5-5: the quotient of a finite group by a normal subgroup is finite. -/
theorem quotientFinite (H : Subgroup G) [H.Normal] : Finite (G ⧸ H) := by
  infer_instance

/-- Helper for Exercise 10-10.5-5: the quotient of a finite group by a normal subgroup has a
fintype structure. -/
noncomputable abbrev quotientFintype (H : Subgroup G) [H.Normal] : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

/-- Helper for Exercise 10-10.5-5: a finite commutative group has finitely many complex degree-`1`
characters. -/
theorem linearCharacterFinite
    {A : Type u} [CommGroup A] [Finite A] :
    Finite (A →* ℂˣ) := by
  let eDual : (A →* ℂˣ) ≃* A :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := A) (M := ℂ))
  exact Finite.of_equiv A eDual.symm.toEquiv

/-- Helper for Exercise 10-10.5-5: the degree-`1` complex characters of a finite commutative
group form a finite type. -/
noncomputable abbrev linearCharacterFintype
    {A : Type u} [CommGroup A] [Finite A] :
    Fintype (A →* ℂˣ) := Fintype.ofFinite (A →* ℂˣ)

attribute [local instance] quotientFintype linearCharacterFintype

/-- Helper for Exercise 10-10.5-5: on a finite commutative group, the sum of all degree-`1`
complex characters vanishes away from the identity. -/
theorem commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one
    {A : Type u} [CommGroup A] [Finite A] {a : A} (ha : a ≠ 1) :
    ∑ χ : A →* ℂˣ, (χ a : ℂ) = 0 := by
  classical
  obtain ⟨φ, hφa⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := A) (M := ℂ) ha
  let e : (A →* ℂˣ) ≃ (A →* ℂˣ) :=
    { toFun := fun χ ↦ φ * χ
      invFun := fun χ ↦ φ⁻¹ * χ
      left_inv := by
        intro χ
        simp
      right_inv := by
        intro χ
        simp }
  have hsum :
      ∑ χ : A →* ℂˣ, ((φ * χ) a : ℂ) =
        ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
    exact Fintype.sum_equiv e
      (fun χ : A →* ℂˣ ↦ ((φ * χ) a : ℂ))
      (fun χ : A →* ℂˣ ↦ (χ a : ℂ))
      (fun χ ↦ rfl)
  have hmul :
      ∑ χ : A →* ℂˣ, ((φ * χ) a : ℂ) =
        (φ a : ℂ) * ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
    -- Pull the fixed scalar `φ(a)` out of the finite sum.
    simp [Finset.mul_sum]
  have hfactor :
      (((φ a : ℂ) - 1) * ∑ χ : A →* ℂˣ, (χ a : ℂ)) = 0 := by
    -- Compare the permutation-invariant sum with the same sum after multiplication by `φ(a)`.
    calc
      (((φ a : ℂ) - 1) * ∑ χ : A →* ℂˣ, (χ a : ℂ)) =
          (φ a : ℂ) * ∑ χ : A →* ℂˣ, (χ a : ℂ) -
            ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
              ring
      _ = 0 := by
        rw [← hmul, hsum, sub_self]
  have hne : ((φ a : ℂ) - 1) ≠ 0 := by
    intro hzero
    have hcast : (φ a : ℂ) = 1 := sub_eq_zero.mp hzero
    apply hφa
    ext
    simpa using hcast
  exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Exercise 10-10.5-5: the regular character of a finite commutative group is the
sum of all of its degree-`1` complex characters. -/
theorem commGroup_regularCharacter_eq_sum_linearCharacters
    {A : Type u} [CommGroup A] [Finite A] :
    (leftRegular ℂ A).character = ∑ χ : A →* ℂˣ, χ.toRepresentation.character := by
  let _ : Fintype A := Fintype.ofFinite A
  ext a
  by_cases ha : a = 1
  · subst ha
    -- At the identity, every linear character has value `1`, so the sum is the number of them.
    rw [Representation.leftRegular_character_one, Finset.sum_apply]
    have hcard : Fintype.card A = Fintype.card (A →* ℂˣ) := by
      simpa using
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := A) (M := ℂ)).symm
    simp [hcard]
  · -- Away from the identity, the character sum vanishes by the translation argument above.
    rw [Representation.leftRegular_character_eq_zero_of_ne_one ha, Finset.sum_apply]
    simpa using
      (commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one (A := A) ha).symm

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: evaluating an induced class function at the identity multiplies
the subgroup value at `1` by the subgroup index. -/
theorem inducedClassFunction_one_eq_index_mul_value
    (H : Subgroup G) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  classical
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  have h1H : (1 : G) ∈ H := by
    simp
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
    exact_mod_cast H.card_mul_index.symm
  have hχ1 : χ ⟨1, h1H⟩ = χ 1 := rfl
  have hsum0 : ∑ s : G, χ 1 = (Nat.card G : ℂ) * χ 1 := by
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hsum :
      ∑ s : G,
        (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
          (Nat.card G : ℂ) * χ 1 := by
    -- Every summand at the identity is the same subgroup value `χ 1`.
    have hterm :
        ∀ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) = χ 1 := by
      intro s
      have hs : s⁻¹ * (1 : G) * s ∈ H := by
        simpa using h1H
      simp [hs, hχ1]
    calc
      ∑ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
          = ∑ s : G, χ 1 := by
              simpa using
                (Fintype.sum_congr
                  (f := fun s : G ↦
                    if hs : s⁻¹ * (1 : G) * s ∈ H then
                      χ ⟨s⁻¹ * (1 : G) * s, hs⟩
                    else 0)
                  (g := fun _ : G ↦ χ 1)
                  hterm)
      _ = (Nat.card G : ℂ) * χ 1 := hsum0
  -- Now simplify the normalized induction formula using `|G| = |H| * [G : H]`.
  calc
    Ind[H](χ) 1
        = ((Nat.card H : ℂ)⁻¹) *
            ∑ s : G,
              (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) := by
            simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card H : ℂ)⁻¹) * ((Nat.card G : ℂ) * χ 1) := by
      rw [hsum]
    _ = ((Nat.card H : ℂ)⁻¹) * (((Nat.card H : ℂ) * H.index) * χ 1) := by
      rw [hcard]
    _ = (H.index : ℂ) * χ 1 := by
      field_simp [hH]

end Subgroup

-- The bundled-character owner `fdRepCharacterRing` and its companions
-- `fdRepCharacterRing_trivial_eq_one` / `fdRepCharacterRing_tensor_eq_mul` are the canonical
-- Chapter 10.5 declarations from `Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure`
-- (transitively imported here through `AutoSplit`).  They are reused directly rather than kept as
-- a duplicate copy, which would otherwise clash on import-merge.

-- Source/core/bridge triage:
-- * source-facing: Serre's subgroups `R₀'(G)` and `R'(G)`.
-- * core/canonical: `Subgroup.characterRingInduction` together with the ambient submodule owners
--   `Submodule.span`, `Submodule.map`, and `Submodule.sup`.
-- * bridge/view: the subgroup-side virtual character `α.toCharacterRing - 1` coming from a
--   degree-`1` complex character `α : E →* ℂˣ`.
--
-- Sampled owner declarations in this domain:
-- * `MonoidHom.toCharacterRing`
-- * `Subgroup.characterRingInduction`
-- * `Representation.artinInducedCharacterSubmodule`
-- * `Representation.pElementaryInducedCharacterSpan`
-- * `Representation.monomialCharacterSpan`
--
-- Primitive data: an elementary subgroup `E ≤ G` and a degree-`1` complex character
-- `α : E →* ℂˣ`.
-- Derived API: the virtual character `α.toCharacterRing - 1 ∈ R(E)` and its induced image in
-- `R(G)`.

/-- Serre's subgroup `R₀'(G)`, generated by the induced differences `Ind_E^G(α - 1)` where `E`
is elementary and `α : E →* ℂˣ` is a degree-one complex character. -/
def elementaryLinearCharacterAugmentationSpan (G : Type) [Group G] [Finite G] :
    Submodule ℤ (R(G)) :=
  Submodule.span ℤ
    { ψ : R(G) |
      ∃ E : Subgroup G, IsElementary E ∧ ∃ α : E →* ℂˣ,
        ψ = Subgroup.characterRingInduction E (α.toCharacterRing - 1) }

scoped[Representation] notation:max "R₀'(" G ")" =>
  Representation.elementaryLinearCharacterAugmentationSpan G

/-- Serre's subgroup `R'(G) = ℤ + R₀'(G)`, realized as the sum of the span of the trivial
character and `R₀'(G)`. -/
def elementaryLinearCharacterSpan (G : Type) [Group G] [Finite G] :
    Submodule ℤ (R(G)) :=
  Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)

scoped[Representation] notation:max "R'(" G ")" =>
  Representation.elementaryLinearCharacterSpan G

-- `exists_complete_pairwise_nonisomorphic_irreducible_family_local` is the canonical declaration
-- from `Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge` (also `Serre.Chap10.Lemma_10_10_2_3`),
-- transitively imported here; reused directly rather than kept as a duplicate copy.

-- `restrict_mem_characterRing_preBrauer` and `induced_mul_eq_induced_mul_restriction_preBrauer`
-- are the canonical declarations from
-- `Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge` (transitively imported); reused directly.

-- `mul_mem_pElementaryInducedCharacterSpan_local` and
-- `smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem_local` are the canonical declarations
-- from `Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge` (transitively imported); reused
-- directly rather than kept as duplicate copies.

-- The following helpers are the canonical declarations from
-- `Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge` (transitively imported); reused directly
-- rather than kept as duplicate copies:
-- * `finiteIndex_and_coprime_of_scalar_mem_pElementaryInducedCharacterSpan_local`
-- * `quotient_card_smul_mem_pElementaryInducedCharacterSpan_of_finiteIndex_local`
-- * `isPRegular_iff_pow_primeToPart_eq_one_local`
-- * `nat_dvd_of_isIntegral_natCast_div_local`
-- (the latter also lives in `Serre.Chap08.Corollary_8_8_1_3` etc.).

-- NOTE (falsification record): the former helper `pregular_indicator_mem_characterRing_local`
-- (sorried) was deleted: the statement was PROVEN FALSE in
-- `Representation.Brauer18.pregular_indicator_not_mem_characterRing`
-- (`Serre.Chap10.Theorem_10_10_2_1.PRegularEndgame`). It had no consumer.

end

end Representation
