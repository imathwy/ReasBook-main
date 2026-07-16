import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_1
import LinearRepresentations_Serre_1977.Serre.Chap09.Proposition_9_9_4_1
import LinearRepresentations_Serre_1977.Serre.Chap09.Proposition_9_9_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Representation SubgroupInduction
open Representation

noncomputable section

namespace Representation

section

variable (A : Type) [Group A] [Finite A]

attribute [local instance] Fintype.ofFinite

/-- Serre's auxiliary character candidate `λ_A = φ(|A|) r_A - θ_A` on a finite group `A`. -/
def cyclicGroupLambda : A → ℂ :=
  ((Nat.totient (Nat.card A) : ℂ)) • (leftRegular ℂ A).character - θ[A]

scoped[Representation] notation:max "λ[" A "]" => cyclicGroupLambda A

-- Source/core/bridge triage:
-- * source-facing: Serre's auxiliary class function `λ[A]`.
-- * core/canonical: the integral character ring owner `R(A)`.
-- * bridge/view: realization of `λ[A]` as an actual finite-dimensional character in `FDRep ℂ A`
--   and its induced sum over cyclic subgroups.

/-- Helper for Exercise 9-9.4-3: the pairing is additive across a finite sum in its left
argument. -/
private lemma groupFunctionPairing_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → A → ℂ)
    (ψ : A → ℂ) :
    Representation.groupFunctionPairingOverField ℂ (Finset.sum s fun i ↦ f i) ψ =
      Finset.sum s fun i ↦ Representation.groupFunctionPairingOverField ℂ (f i) ψ := by
  classical
  -- Peel off one summand at a time and use additivity of the pairing on the left.
  refine Finset.induction_on s ?_ ?_
  · simp [Representation.groupFunctionPairingOverField]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Representation.groupFunctionPairing_add_left, ih]

/-- Helper for Exercise 9-9.4-3: the trivial class function has self-pairing `1`. -/
private lemma groupFunctionPairing_one_one_eq_one :
    ⟪(1 : A → ℂ), (1 : A → ℂ)⟫ = 1 := by
  -- Rewrite the pairing as the average of the constant function `1`.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp [Nat.card_eq_fintype_card]

/-- Helper for Exercise 9-9.4-3: the regular character has pairing `1` with the unit character. -/
private lemma leftRegular_character_pairing_one_eq_one :
    ⟪((leftRegular ℂ A).character : A → ℂ), (1 : A → ℂ)⟫ = 1 := by
  -- Only the identity contributes to the regular-character average.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp only [Pi.one_apply, mul_one]
  calc
    (Nat.card A : ℂ)⁻¹ * ∑ t : A, (leftRegular ℂ A).character t
        = (Nat.card A : ℂ)⁻¹ * (Nat.card A : ℂ) := by
            rw [Finset.sum_eq_single 1]
            · simp [Representation.leftRegular_character_one]
            · intro t _ hne
              have hne' : t ≠ 1 := by
                simpa using hne
              simp [Representation.leftRegular_character_eq_zero_of_ne_one hne']
            · simp
    _ = 1 := by
          field_simp [Nat.cast_ne_zero]

/-- Helper for Exercise 9-9.4-3: in a finite cyclic group, generating the whole group is
equivalent to having order `|A|`. -/
private lemma zpowers_eq_top_iff_orderOf_eq_natCard [IsCyclic A] (a : A) :
    Subgroup.zpowers a = (⊤ : Subgroup A) ↔ orderOf a = Nat.card A := by
  constructor
  · intro ha
    exact orderOf_eq_card_of_zpowers_eq_top ha
  · intro ha
    -- In a finite cyclic group, equality of subgroup cardinalities forces equality with `⊤`.
    exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).mp <| by
      rw [Nat.card_zpowers, ha]

/-- Helper for Exercise 9-9.4-3: summing `θ[A]` over a finite cyclic group counts all generators,
so the total is `|A| * φ(|A|)`. -/
private lemma cyclicGroupTheta_sum_eq_card_mul_totient [IsCyclic A] :
    ∑ a : A, (θ[A] : A → ℂ) a = (Nat.card A : ℂ) * Nat.totient (Nat.card A) := by
  classical
  let S : Finset A := Finset.univ.filter fun a : A ↦ orderOf a = Nat.card A
  -- Rewrite `θ[A]` as the constant `|A|` on the generator set and `0` elsewhere.
  calc
    ∑ a : A, (θ[A] : A → ℂ) a
        = ∑ a : A, if orderOf a = Nat.card A then (Nat.card A : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [Representation.cyclicGroupTheta, zpowers_eq_top_iff_orderOf_eq_natCard]
    _ = Finset.sum S fun _a ↦ (Nat.card A : ℂ) := by
          rw [Finset.sum_ite]
          simp [S]
    _ = (S.card : ℂ) * (Nat.card A : ℂ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = (Nat.totient (Nat.card A) : ℂ) * (Nat.card A : ℂ) := by
          congr 1
          simpa [S, Nat.card_eq_fintype_card] using
            (IsCyclic.card_orderOf_eq_totient (α := A) (dvd_rfl : Fintype.card A ∣ Fintype.card A))
    _ = (Nat.card A : ℂ) * Nat.totient (Nat.card A) := by
          ring

/-- Helper for Exercise 9-9.4-3: the auxiliary function `θ[A]` pairs with the unit character as
the number of generators of the cyclic group `A`. -/
private lemma cyclicGroupTheta_pairing_one_eq_totient [IsCyclic A] :
    ⟪(θ[A] : A → ℂ), (1 : A → ℂ)⟫ = Nat.totient (Nat.card A) := by
  have hcard : (Nat.card A : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  -- Rewrite the pairing as the average of `θ[A]` and substitute the generator count.
  calc
    ⟪(θ[A] : A → ℂ), (1 : A → ℂ)⟫
        = (Nat.card A : ℂ)⁻¹ * ∑ a : A, (θ[A] : A → ℂ) a := by
            rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
            simp
    _ = (Nat.card A : ℂ)⁻¹ * ((Nat.card A : ℂ) * Nat.totient (Nat.card A)) := by
          rw [cyclicGroupTheta_sum_eq_card_mul_totient (A := A)]
    _ = Nat.totient (Nat.card A) := by
          rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

-- Proof sketch: evaluate the pairing directly from the definition of `cyclicGroupLambda A`,
-- use the explicit values of the regular character and of `θ[A]`, and count the
-- generators of the cyclic group by `Nat.totient (Nat.card A)`.
/-- Exercise 9-9.4-3 (1): if `A` is cyclic, Serre's auxiliary character candidate `λ_A` is
orthogonal to the unit character. -/
theorem cyclicGroupLambda_pairing_one_eq_zero [IsCyclic A] :
    ⟪λ[A], 1⟫ = 0 := by
  -- Expand Serre's definition of `λ[A]` and evaluate each pairing separately.
  calc
    ⟪λ[A], 1⟫
        =
          Representation.groupFunctionPairingOverField ℂ
            (((Nat.totient (Nat.card A) : ℂ) • ((leftRegular ℂ A).character : A → ℂ)) +
              ((-1 : ℂ) • (θ[A] : A → ℂ)))
            (1 : A → ℂ) := by
            simp [Representation.cyclicGroupLambda, sub_eq_add_neg]
    _ = Representation.groupFunctionPairingOverField ℂ
            (((Nat.totient (Nat.card A) : ℂ) • ((leftRegular ℂ A).character : A → ℂ)))
            (1 : A → ℂ) +
          Representation.groupFunctionPairingOverField ℂ (((-1 : ℂ) • (θ[A] : A → ℂ)))
            (1 : A → ℂ) := by
            rw [Representation.groupFunctionPairing_add_left]
    _ = (Nat.totient (Nat.card A) : ℂ) *
          Representation.groupFunctionPairingOverField ℂ
            (((leftRegular ℂ A).character : A → ℂ))
            (1 : A → ℂ) +
          (-1 : ℂ) *
            Representation.groupFunctionPairingOverField ℂ
              ((θ[A] : A → ℂ))
              (1 : A → ℂ) := by
            rw [Representation.groupFunctionPairing_smul_left,
              Representation.groupFunctionPairing_smul_left]
    _ = (Nat.totient (Nat.card A) : ℂ) + (-1 : ℂ) * Nat.totient (Nat.card A) := by
          simp [leftRegular_character_pairing_one_eq_one, cyclicGroupTheta_pairing_one_eq_totient]
    _ = 0 := by
          simp

-- Proof sketch: `θ[A]` already lies in the owner `R(A)` by Proposition `9-9.4-2`. The regular
-- character term is itself a genuine character, so it also lies in `R(A)`, and the character ring
-- is closed under additive combinations inside the ambient function space.
/-- If `A` is cyclic, Serre's auxiliary character candidate `λ_A` belongs to the character ring
`R(A)`. This is the canonical owner-level bridge from the source-facing function `λ_A` to the
chapter's character-ring API. -/
theorem cyclicGroupLambda_mem_characterRing [IsCyclic A] :
    λ[A] ∈ R(A) := by
  have hreg : (leftRegular ℂ A).character ∈ R(A) := by
    simpa using
      Representation.rep_character_mem_characterRingOverField
        (K := ℂ) (G := A) (Rep.of (leftRegular ℂ A))
  refine (R(A)).sub_mem ?_ (cyclicGroupTheta_mem_characterRing A)
  simpa [Pi.smul_apply, zsmul_eq_mul] using
    (R(A)).toSubmodule.smul_mem (Nat.totient (Nat.card A) : ℤ) hreg

/-- Helper for Exercise 9-9.4-3: `λ[A]` is the complexification of an explicit real-valued
function that is nonpositive away from the identity. -/
private lemma cyclicGroupLambda_real_model [IsCyclic A] :
    ∃ φ : A → ℝ, Complex.ofReal ∘ φ = λ[A] ∧ ∀ a : A, a ≠ 1 → φ a ≤ 0 := by
  classical
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq (Subgroup A) := Classical.decEq (Subgroup A)
  let φ : A → ℝ := fun a ↦
    (Nat.totient (Nat.card A) : ℝ) * (if a = 1 then (Nat.card A : ℝ) else 0) -
      (if Subgroup.zpowers a = (⊤ : Subgroup A) then (Nat.card A : ℝ) else 0)
  refine ⟨φ, ?_, ?_⟩
  · -- Compare the explicit real model with Serre's complex-valued formula pointwise.
    ext a
    by_cases ha : a = 1
    · subst ha
      by_cases htop : (⊥ : Subgroup A) = ⊤
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, htop]
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, htop]
    · by_cases hgen : Subgroup.zpowers a = (⊤ : Subgroup A)
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, Representation.leftRegular_character_eq_zero_of_ne_one ha, ha, hgen]
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, Representation.leftRegular_character_eq_zero_of_ne_one ha, ha, hgen]
  · intro a ha
    -- Away from the identity the regular-character term vanishes, leaving a nonpositive value.
    by_cases hgen : Subgroup.zpowers a = (⊤ : Subgroup A)
    · simp [φ, ha, hgen]
    · simp [φ, ha, hgen]

-- Proof sketch: apply Exercise `9-9.1-1` to the source-facing function `λ[A]`, using the
-- canonical owner theorem `cyclicGroupLambda_mem_characterRing`, the pairing identity above, and
-- the sign condition away from the identity to obtain a finite-dimensional realization directly in
-- `FDRep ℂ A`.
/-- Exercise 9-9.4-3 (2): if `A` is cyclic, the auxiliary function `λ_A` is the character of a
finite-dimensional complex representation of `A`. -/
theorem cyclicGroupLambda_is_character [IsCyclic A] :
    ∃ V : FDRep ℂ A, V.character = λ[A] := by
  obtain ⟨φ, hφ, hneg⟩ := cyclicGroupLambda_real_model (A := A)
  -- Apply Exercise `9-9.1-1` to the explicit real model of `λ[A]`.
  have hpair : ⟪Complex.ofReal ∘ φ, (1 : A → ℂ)⟫ = 0 := by
    simpa [hφ] using cyclicGroupLambda_pairing_one_eq_zero (A := A)
  have hR : Complex.ofReal ∘ φ ∈ R(A) := by
    simpa [hφ] using cyclicGroupLambda_mem_characterRing (A := A)
  simpa [hφ] using
    exists_fdRep_character_eq_of_mem_characterRing_of_pairing_one_eq_zero_of_nonpos_off_identity
      (G := A) (φ := φ) hpair hneg hR

end

end Representation

section

variable {G : Type} [Group G] [Finite G]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: pairing an induced class function with the unit character does
not change the average. -/
private lemma groupFunctionPairing_inducedClassFunction_one_eq (H : Subgroup G) (χ : H → ℂ) :
    ⟪Ind[H](χ), (1 : G → ℂ)⟫ = ⟪χ, (1 : H → ℂ)⟫ := by
  classical
  -- Pin the `Fintype` instance on `↥H` to the ambient `Fintype.ofFinite`, matching the one used in
  -- the statement; `classical` would otherwise prefer the decidable-membership instance and create a
  -- spurious mismatch between the two normalized pairings.
  letI : Fintype (↥H) := Fintype.ofFinite (↥H)
  have hcardG : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hsub_sum :
      (∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))) = ∑ h : H, χ h := by
    calc
      ∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))
          = ∑ y : G, if y ∈ H then (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) else (0 : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              by_cases hmem : y ∈ H <;> simp [hmem]
      _ = Finset.sum (Finset.univ.filter fun y : G ↦ y ∈ H)
            (fun y ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) := by
              simpa using
                (Finset.sum_filter
                  (s := Finset.univ)
                  (p := fun y : G ↦ y ∈ H)
                  (f := fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))).symm
      _ = ∑ h : H, χ h := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := Finset.univ)
                (p := fun y : G ↦ y ∈ H)
                (f := fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))).symm
  have hinner (s : G) :
      ∑ x : G,
        (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ)) =
          ∑ h : H, χ h := by
    let e : G ≃ G :=
      { toFun := fun x ↦ s⁻¹ * x * s
        invFun := fun y ↦ s * y * s⁻¹
        left_inv := by
          intro x
          simp [mul_assoc]
        right_inv := by
          intro y
          simp [mul_assoc] }
    -- Reindex by conjugation, then collapse the ambient sum to the subgroup carrier.
    calc
      ∑ x : G,
          (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
          = ∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) := by
              simpa [e] using
                Fintype.sum_equiv e
                  (fun x : G ↦ if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
                  (fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))
                  (fun x ↦ by rfl)
      _ = ∑ h : H, χ h := hsub_sum
  let F : G → G → ℂ := fun x s ↦
    ((Nat.card H : ℂ)⁻¹) *
      (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
  have hF (x : G) : Ind[H](χ) x = ∑ s : G, F x s := by
    simp [Subgroup.inducedClassFunction, F, Finset.mul_sum]
  have hFsum (s : G) : ∑ x : G, F x s = ((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h := by
    dsimp [F]
    rw [← Finset.mul_sum, hinner s]
  -- Expand the two pairings as normalized sums and use the conjugation reindexing above.
  have hcalc :
      ⟪Ind[H](χ), (1 : G → ℂ)⟫ = (Nat.card H : ℂ)⁻¹ * ∑ h : H, χ h := by
    calc
      ⟪Ind[H](χ), (1 : G → ℂ)⟫
          = (Nat.card G : ℂ)⁻¹ * ∑ x : G, Ind[H](χ) x := by
              rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
              simp
      _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, ∑ s : G, F x s := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [hF x]
      _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ∑ x : G, F x s := by
            rw [Finset.sum_comm]
      _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            simpa using hFsum s
      _ = (Nat.card G : ℂ)⁻¹ *
            ((Nat.card G : ℂ) * (((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h)) := by
              simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      _ = (Nat.card H : ℂ)⁻¹ * ∑ h : H, χ h := by
            rw [← mul_assoc, inv_mul_cancel₀ hcardG, one_mul]
  rw [hcalc]
  -- It remains to recognize the average over `H` as the normalized pairing of `χ` with `1`.
  -- Use the inversion-on-the-right form, which is phrased with `Nat.card`.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro h _
  simp

/-- Helper for Exercise 9-9.4-3: summing scalar multiples of a fixed class function factors out
that class function. -/
private lemma finset_sum_smul_const {ι : Type*} (s : Finset ι) (a : ι → ℂ) (χ : G → ℂ) :
    Finset.sum s (fun i ↦ a i • χ) = (Finset.sum s fun i ↦ a i) • χ := by
  classical
  -- Build the sum one term at a time and factor out the common class function.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, add_smul]

/-- Helper for Exercise 9-9.4-3: evaluating an induced class function at the identity multiplies
the subgroup value at `1` by the subgroup index. -/
private lemma inducedClassFunction_one_eq_index_mul_value (H : Subgroup G) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  -- TODO: evaluate the induction formula at the identity, where every summand is `χ 1`, and use
  -- `|G| = |H| * [G : H]`.
  classical
  have h1H : (1 : G) ∈ H := by
    simp
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
    exact_mod_cast H.card_mul_index.symm
  have hsum :
      ∑ s : G,
        (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
          (Nat.card G : ℂ) * χ 1 := by
    have hχ1 : χ ⟨1, h1H⟩ = χ 1 := rfl
    -- Every summand at the identity is the same subgroup value `χ 1`.
    calc
      ∑ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
          = ∑ _s : G, χ 1 := by
              have hterm :
                  ∀ s : G,
                    (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
                      χ 1 := by
                    intro s
                    have hs : s⁻¹ * (1 : G) * s ∈ H := by
                      simpa using h1H
                    simp [hs, hχ1]
              simpa using
                (Fintype.sum_congr
                  (f := fun s : G ↦
                    if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
                  (g := fun _s : G ↦ χ 1)
                  hterm)
      _ = (Nat.card G : ℂ) * χ 1 := by
            simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  -- Substitute the constant identity-value sum into the induction formula.
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
          field_simp [hcardH]

/-- Helper for Exercise 9-9.4-3: inducing the regular character from a subgroup recovers the
ambient regular character. -/
private lemma induced_leftRegular_character_eq (H : Subgroup G) :
    Ind[H](((leftRegular ℂ H).character : H → ℂ)) = (leftRegular ℂ G).character := by
  classical
  ext x
  by_cases hx : x = 1
  · -- At the identity, induction multiplies the subgroup value by the subgroup index.
    subst hx
    calc
      Ind[H](((leftRegular ℂ H).character : H → ℂ)) 1
          = (H.index : ℂ) * (leftRegular ℂ H).character 1 := by
              rw [inducedClassFunction_one_eq_index_mul_value]
      _ = (H.index : ℂ) * (Nat.card H : ℂ) := by
            simp
      _ = (Nat.card G : ℂ) := by
            have hcard' : (Nat.card H : ℂ) * H.index = (Nat.card G : ℂ) := by
              exact_mod_cast H.card_mul_index
            simpa [mul_comm] using hcard'
      _ = (leftRegular ℂ G).character 1 := by
            simp
  · -- Away from the identity, each induced summand evaluates the subgroup regular character away
    -- from `1`, so every term vanishes.
    have hsum :
        ∑ s : G,
          (if hs : s⁻¹ * x * s ∈ H then
            ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hs⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      by_cases hsx : s⁻¹ * x * s ∈ H
      · have hconj_ne : s⁻¹ * x * s ≠ 1 := by
          intro h1
          apply hx
          calc
            x = s * (s⁻¹ * x * s) * s⁻¹ := by
                  simp [mul_assoc]
            _ = 1 := by
                  simp [h1]
        have hsub_ne : (⟨s⁻¹ * x * s, hsx⟩ : H) ≠ 1 := by
          intro hsub
          apply hconj_ne
          exact congrArg Subtype.val hsub
        have hreg0 :
            ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hsx⟩ = 0 :=
          Representation.leftRegular_character_eq_zero_of_ne_one hsub_ne
        simpa [hsx] using hreg0
      · simpa [hsx]
    calc
      Ind[H](((leftRegular ℂ H).character : H → ℂ)) x
          = ((Nat.card H : ℂ)⁻¹) *
              ∑ s : G,
                (if hs : s⁻¹ * x * s ∈ H then
                  ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hs⟩
                else 0) := by
              simp [Subgroup.inducedClassFunction]
      _ = 0 := by
            rw [hsum]
            simp
      _ = (leftRegular ℂ G).character x := by
            symm
            exact Representation.leftRegular_character_eq_zero_of_ne_one hx

/-- Helper for Exercise 9-9.4-3: the sum of the generator counts of the cyclic subgroups of `G`
is `|G|`. -/
private lemma sum_totient_natCard_cyclicSubgroups_eq_natCard :
    ∑ H ∈ Subgroup.cyclicSubgroups G, Nat.totient (Nat.card H) = Nat.card G := by
  have hpair_rhs :
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ = Nat.card G := by
    -- Pair Serre's cyclic `θ`-identity with the unit character on the right.
    calc
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫
          = ⟪(Nat.card G : ℂ) • (1 : G → ℂ), (1 : G → ℂ)⟫ := by
              rw [sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
      _ = (Nat.card G : ℂ) * ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ := by
            rw [Representation.groupFunctionPairing_smul_left]
      _ = Nat.card G := by
            simp [groupFunctionPairing_one_one_eq_one]
  have hpair_lhs :
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ =
        (∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) := by
    -- Distribute the pairing across the finite subgroup sum and evaluate each cyclic contribution.
    calc
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫
          = ∑ H ∈ Subgroup.cyclicSubgroups G,
              ⟪(Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ := by
              simpa using
                groupFunctionPairing_finset_sum_left (A := G) (s := Subgroup.cyclicSubgroups G)
                  (f := fun H ↦ (Ind[H](θ[H]) : G → ℂ)) (ψ := (1 : G → ℂ))
      _ = ∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            haveI : IsCyclic H := (Subgroup.mem_cyclicSubgroups.mp hH)
            rw [groupFunctionPairing_inducedClassFunction_one_eq,
              cyclicGroupTheta_pairing_one_eq_totient]
  have hcomplex :
      (∑ H ∈ Subgroup.cyclicSubgroups G, Nat.totient (Nat.card H) : ℂ) = Nat.card G := by
    exact hpair_lhs.symm.trans hpair_rhs
  exact_mod_cast hcomplex

-- Proof sketch: expand `cyclicGroupLambda` inside the sum over cyclic subgroups. Proposition
-- `9-9.4-1` identifies the total contribution of the `θ_A` terms, while Proposition `7-7.2-1`
-- and the regular-character computation identify the total contribution of the regular terms with
-- `|G| • (leftRegular ℂ G).character`. Internally, each cyclic summand can be routed through the
-- canonical character-ring induction owner, but the public statement remains the source-facing
-- equality of class functions.
/-- Exercise 9-9.4-3 (3): summing the induced auxiliary characters `Ind_A^G(λ_A)` over the cyclic
subgroups `A ≤ G` gives `|G| (r_G - 1)`, written in Lean with the regular character
`(leftRegular ℂ G).character`. -/
theorem sum_induced_cyclicGroupLambda_eq_groupOrder_smul_regular_character_sub_one :
    ∑ H ∈ Subgroup.cyclicSubgroups G,
        Ind[H](λ[H]) =
      (Nat.card G : ℂ) • ((leftRegular ℂ G).character - 1) := by
  -- Expand each cyclic summand, rewrite the induced regular character, and then collect the
  -- common regular and `θ` contributions.
  calc
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](λ[H])
        = ∑ H ∈ Subgroup.cyclicSubgroups G,
            ((Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character - Ind[H](θ[H])) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            haveI : IsCyclic H := (Subgroup.mem_cyclicSubgroups.mp hH)
            calc
              Ind[H](λ[H])
                  = Ind[H](((Nat.totient (Nat.card H) : ℂ) •
                        ((leftRegular ℂ H).character : H → ℂ)) +
                      ((-1 : ℂ) • (θ[H] : H → ℂ))) := by
                          simp [Representation.cyclicGroupLambda, sub_eq_add_neg]
              _ = (Nat.totient (Nat.card H) : ℂ) • Ind[H](((leftRegular ℂ H).character : H → ℂ)) +
                    (-1 : ℂ) • Ind[H](θ[H]) := by
                        rw [Subgroup.inducedClassFunction_map_add,
                          Subgroup.inducedClassFunction_map_smul,
                          Subgroup.inducedClassFunction_map_smul]
              _ = (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character +
                    (-1 : ℂ) • Ind[H](θ[H]) := by
                        rw [induced_leftRegular_character_eq]
              _ = (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character - Ind[H](θ[H]) := by
                        simp [sub_eq_add_neg]
    _ = (∑ H ∈ Subgroup.cyclicSubgroups G,
            (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character) -
          ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            rw [Finset.sum_sub_distrib]
    _ = ((∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) •
            (leftRegular ℂ G).character) -
          ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            simp [finset_sum_smul_const]
    _ = (Nat.card G : ℂ) • (leftRegular ℂ G).character -
          (Nat.card G : ℂ) • (1 : G → ℂ) := by
            have htot :
                (∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) =
                  (Nat.card G : ℂ) := by
              exact_mod_cast sum_totient_natCard_cyclicSubgroups_eq_natCard (G := G)
            rw [htot, sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
    _ = (Nat.card G : ℂ) • ((leftRegular ℂ G).character - 1) := by
          rw [smul_sub]

end
