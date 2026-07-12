import Mathlib
import StacksProject_2024.Chap15.Definition_15_114_3
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_116_12
import StacksProject_2024.Chap15.Lemma_15_116_3
import StacksProject_2024.Chap15.Lemma_15_116_13
import StacksProject_2024.Chap15.Lemma_15_116_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Polynomial
open IsExtensionOfDiscreteValuationRings
open IsLocalRing

universe u v w x y z

section

/-- A degree-`p` extension has finite level `l` when it admits a quotient-polynomial presentation
`P(z) = a / π^n` from Lemma `15.116.13` for which `1 - ζ` is associated to `π ^ e₁` and
`l = n / e₁`. Forgetting the level identity recovers the chapter's finite-level owner
`IsDegreePFiniteLevelExtension`. -/
def IsDegreePFiniteLevelExtensionOfLevel
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime] [FiniteDimensional L M] : Prop :=
  ∃ ζ : B, IsPrimitiveRoot ζ p ∧
    ∃ π : B, ∃ e₁ n : ℕ,
      0 < e₁ ∧ Associated (1 - ζ) (π ^ e₁) ∧ l = (n : ℚ) / e₁ ∧
        ∃ P : B[X], IsOneSubZetaQuotientPolynomial p ζ P ∧
          ∃ a : B, ∃ z : M,
            Polynomial.aeval z (P.map (algebraMap B L)) =
                algebraMap L M ((algebraMap B L a) / (algebraMap B L π) ^ n) ∧
              Algebra.adjoin L ({z} : Set M) = ⊤ ∧
              Module.finrank L M = p

namespace IsDegreePFiniteLevelExtensionOfLevel

/-- Forgetting the level identity recovers the chapter's finite-level owner. -/
theorem toIsDegreePFiniteLevelExtension
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime] [FiniteDimensional L M]
    (h : IsDegreePFiniteLevelExtensionOfLevel B L M p l) :
    IsDegreePFiniteLevelExtension B L M p := by
  -- Proof comment: the exact-level witness already contains the witness expected by the
  -- level-forgetting owner.
  rcases h with ⟨ζ, hζ, π, e₁, n, he₁, hπ, -, P, hP, a, z, hz, hgen, hfinrank⟩
  exact ⟨ζ, hζ, π, e₁, n, he₁, hπ, P, hP, a, z, hz, hgen, hfinrank⟩

end IsDegreePFiniteLevelExtensionOfLevel

/-- A degree-`p` finite-level extension of level `l` has degree `p`. -/
theorem isDegreePFiniteLevelExtensionOfLevel_finrank_eq
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime] [FiniteDimensional L M]
    (h : IsDegreePFiniteLevelExtensionOfLevel B L M p l) :
    Module.finrank L M = p := by
  -- Proof comment: this is the degree statement already bundled in the finite-level owner.
  exact isDegreePFiniteLevelExtension_finrank_eq h.toIsDegreePFiniteLevelExtension

/-- Helper for Lemma 15.116.16: this is the mutable source-faithful state for the bad-index
induction. It keeps the current generator together with the current denominator witness for the
quotient-polynomial parameter, but does not yet encode the later residue-coefficient package. -/
structure MixedCharacteristicCoefficientExpansionState
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime] [FiniteDimensional L M] where
  ζ : B
  hζ : IsPrimitiveRoot ζ p
  π : B
  e₁ : ℕ
  nCur : ℕ
  he₁ : 0 < e₁
  hπ : Associated (1 - ζ) (π ^ e₁)
  hlevel : l = (nCur : ℚ) / e₁
  P : B[X]
  hP : IsOneSubZetaQuotientPolynomial p ζ P
  aCur : B
  zCur : M
  hzCur :
    Polynomial.aeval zCur (P.map (algebraMap B L)) =
      algebraMap L M ((algebraMap B L aCur) / (algebraMap B L π) ^ nCur)
  hgenCur : Algebra.adjoin L ({zCur} : Set M) = ⊤
  hfinrank : Module.finrank L M = p

namespace MixedCharacteristicCoefficientExpansionState

/-- Helper for Lemma 15.116.16: forgetting the mutable labels on the current generator and
denominator data recovers the original exact-level finite-level owner. -/
theorem toIsDegreePFiniteLevelExtensionOfLevel
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime] [FiniteDimensional L M]
    (state : MixedCharacteristicCoefficientExpansionState B L M p l) :
    IsDegreePFiniteLevelExtensionOfLevel B L M p l := by
  -- Proof comment: the state is only a relabeling of the exact witness, with the source names
  -- `nCur`, `aCur`, and `zCur` reserved for the later descent steps.
  exact
    ⟨state.ζ, state.hζ, state.π, state.e₁, state.nCur, state.he₁, state.hπ, state.hlevel,
      state.P, state.hP, state.aCur, state.zCur, state.hzCur, state.hgenCur, state.hfinrank⟩

end MixedCharacteristicCoefficientExpansionState

/-- Helper for Lemma 15.116.16: every exact-level quotient-polynomial presentation already gives
the initial mutable state for the source induction, before introducing the truncated coefficient
package and the good/bad index sets. -/
theorem exists_initial_mixed_characteristic_coefficient_expansion_state
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime] [FiniteDimensional L M]
    (h : IsDegreePFiniteLevelExtensionOfLevel B L M p l) :
    Nonempty (MixedCharacteristicCoefficientExpansionState B L M p l) := by
  rcases h with ⟨ζ, hζ, π, e₁, n, he₁, hπ, hlevel, P, hP, a, z, hz, hgen, hfinrank⟩
  -- Proof comment: repackage the existing exact-level witness using the mutable names from the
  -- source proof so the later quotient congruence lemmas can act on the current generator.
  exact
    ⟨{ ζ := ζ
       hζ := hζ
       π := π
       e₁ := e₁
       nCur := n
       he₁ := he₁
       hπ := hπ
       hlevel := hlevel
       P := P
       hP := hP
       aCur := a
       zCur := z
       hzCur := hz
       hgenCur := hgen
       hfinrank := hfinrank }⟩

end

noncomputable section

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [IsFractionRing C M]
variable [Algebra L M] [Algebra K M]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower B C M] [IsScalarTower B L M]
variable [IsScalarTower K L M]
variable [FiniteDimensional L M]

/-- Bridge/view for Lemma `15.116.16`: after the canonical reduced tensor-product base change
`L₁ = (L ⊗[K] K₁)_red`, some canonical branch field `F = L₁ ⧸ m` makes the branch tensor
`M ⊗[L] F` into a field, and that branch extension carries the source-facing finite-level
presentation of exact level `l`. -/
def IsDegreePFiniteLevelExtensionOfLevelAfterBaseChange
    (B : Type v) (K : Type x) (L : Type y) (M : Type z)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime] [FiniteDimensional L M]
    (K1 : Type*) [Field K1] [Algebra K K1] [FiniteDimensional K K1] : Prop :=
  let L1 := (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
  ∃ m : MaximalSpectrum L1,
    let F := L1 ⧸ m.asIdeal
    let _ : Field F := Ideal.Quotient.field m.asIdeal
    let _ : Algebra B F := inferInstance
    let _ : Algebra L F := inferInstance
    let _ : IsScalarTower B L F := inferInstance
    let _ : FiniteDimensional L F := inferInstance
    let MF := M ⊗[L] F
    ∃ hField : IsField MF, ∃ hFinite : FiniteDimensional F MF,
      let _ : Field MF := hField.toField
      let _ : Algebra F MF := Algebra.TensorProduct.rightAlgebra
      let _ : FiniteDimensional F MF := hFinite
      let BF := integralClosure B F
      let _ : Algebra BF F := RingHom.toAlgebra BF.val.toRingHom
      IsDegreePFiniteLevelExtensionOfLevel BF F MF p l

/-- Helper for Lemma 15.116.16: over a fixed mutable source state, a truncated coefficient datum
records the finite denominator slice together with a partition into the source good and bad index
sets. The actual coefficient reconstruction congruence is intentionally kept separate, so this
object only packages the combinatorial carrier needed for the lexicographic induction. -/
structure MixedCharacteristicTruncatedCoefficientData
    {l : ℚ} (state : MixedCharacteristicCoefficientExpansionState B L M p l) where
  mCur : ℕ
  hmCur_pos : 0 < mCur
  hmCur_le_e₁ : mCur ≤ state.e₁
  hmCur_le_nCur_succ : mCur ≤ state.nCur + 1
  coeff : ℕ → ResidueField B
  goodIndices : Finset ℕ
  badIndices : Finset ℕ
  hgood_subset :
    goodIndices ⊆ Finset.Icc (state.nCur + 1 - mCur) state.nCur
  hbad_subset :
    badIndices ⊆ Finset.Icc (state.nCur + 1 - mCur) state.nCur
  hdisjoint : Disjoint goodIndices badIndices
  hcover :
    ∀ i, i ∈ Finset.Icc (state.nCur + 1 - mCur) state.nCur →
      i ∈ goodIndices ∨ i ∈ badIndices

namespace MixedCharacteristicTruncatedCoefficientData

/-- Helper for Lemma 15.116.16: the source descent rank attached to a truncated coefficient datum
is the lexicographic pair `(nCur, |J|)` from the textbook argument. -/
def rank
    {l : ℚ} {state : MixedCharacteristicCoefficientExpansionState B L M p l}
    (data : MixedCharacteristicTruncatedCoefficientData state) : ℕ × ℕ :=
  (state.nCur, data.badIndices.card)

end MixedCharacteristicTruncatedCoefficientData

/-- Helper for Lemma 15.116.16: every mutable mixed-characteristic source state already has a
basic truncated coefficient carrier. This constructor only builds the finite index slice and the
initial good/bad partition skeleton; the later source-faithful coefficient expansion and descent
lemmas will refine it further. -/
theorem exists_truncated_coefficient_data_for_mixed_characteristic_state
    {l : ℚ}
    (hAB : WeaklyUnramified A B)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))))
    (state : MixedCharacteristicCoefficientExpansionState B L M p l) :
    Nonempty (MixedCharacteristicTruncatedCoefficientData state) := by
  let _ := hAB
  let _ := hκ
  -- Proof comment: choose the minimal positive truncation width `mCur = 1`. This already
  -- produces the finite source slice on which the later coefficient reconstruction will act.
  refine ⟨{ mCur := 1
            hmCur_pos := Nat.succ_pos 0
            hmCur_le_e₁ := Nat.succ_le_of_lt state.he₁
            hmCur_le_nCur_succ := Nat.succ_le_succ (Nat.zero_le _)
            coeff := fun _ ↦ 0
            goodIndices := Finset.Icc state.nCur state.nCur
            badIndices := ∅
            hgood_subset := ?_
            hbad_subset := ?_
            hdisjoint := by simp
            hcover := ?_ }⟩
  · -- Proof comment: with `mCur = 1`, the displayed source slice is the singleton `{nCur}`.
    intro i hi
    simpa using hi
  · -- Proof comment: the initial skeleton starts with no bad indices.
    simp
  · -- Proof comment: every index in the singleton source slice is therefore good at this coarse
    -- stage, which is enough to put a concrete rank on the induction object.
    intro i hi
    left
    simpa using hi

/-- Helper for Lemma 15.116.16: a refined mixed-characteristic coefficient expansion packages the
displayed residue-field coefficient slice from the truncated carrier together with chosen lifts of
those coefficients back to `B`. This is the first source-faithful upgrade beyond the coarse
good/bad index carrier; the later quotient-section compatibilities and reconstruction congruence
are still separate data. -/
structure MixedCharacteristicRefinedCoefficientExpansion
    {l : ℚ} (state : MixedCharacteristicCoefficientExpansionState B L M p l)
    (data : MixedCharacteristicTruncatedCoefficientData state) where
  coeffSlice : ℕ → ResidueField B
  coeffSlice_eq : coeffSlice = data.coeff
  coeffLift : ℕ → B
  hcoeffLift : ∀ i, residue B (coeffLift i) = coeffSlice i

/-- Helper for Lemma 15.116.16: the truncated coefficient carrier already determines a refined
coefficient package after choosing arbitrary lifts of the displayed residue classes to `B`. -/
theorem refined_truncated_coefficient_expansion_of_mixed_characteristic_state
    {l : ℚ}
    (state : MixedCharacteristicCoefficientExpansionState B L M p l)
    (data : MixedCharacteristicTruncatedCoefficientData state) :
    Nonempty (MixedCharacteristicRefinedCoefficientExpansion state data) := by
  classical
  -- Proof comment: choose one lift in `B` of each displayed residue coefficient. This gives the
  -- first executable coefficient package while postponing the later quotient-section congruences.
  refine ⟨{ coeffSlice := data.coeff
            coeffSlice_eq := rfl
            coeffLift := fun i ↦ Classical.choose (residue_surjective (data.coeff i))
            hcoeffLift := ?_ }⟩
  intro i
  exact Classical.choose_spec (residue_surjective (data.coeff i))

/-- Helper for Lemma 15.116.16: in the refined package, the displayed coefficient slice is exactly
the original coefficient function from the truncated carrier. -/
theorem refined_coefficient_slice_eq_truncated_coeff
    {l : ℚ}
    {state : MixedCharacteristicCoefficientExpansionState B L M p l}
    {data : MixedCharacteristicTruncatedCoefficientData state}
    (exp : MixedCharacteristicRefinedCoefficientExpansion state data) :
    exp.coeffSlice = data.coeff := by
  -- Proof comment: this is stored as part of the refined package so later descent steps can
  -- rewrite back to the coarse carrier without unpacking the structure definition.
  exact exp.coeffSlice_eq

variable
  (A B C K L M p)

/-- Helper for Lemma 15.116.16: once chosen lifts of the displayed coefficient slice are fixed,
the remaining source-faithful work is to build the mixed-characteristic quotient-section and
reconstruction congruence package, then run the reduction-or-terminal step on the lexicographic
rank. -/
theorem refined_truncated_coefficient_expansion_step
    {l : ℚ} (hl : 0 < l)
    (hAB : WeaklyUnramified A B)
    (hLM : IsDegreePFiniteLevelExtensionOfLevel B L M p l)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))))
    (state : MixedCharacteristicCoefficientExpansionState B L M p l)
    (data : MixedCharacteristicTruncatedCoefficientData state)
    (exp : MixedCharacteristicRefinedCoefficientExpansion state data) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      (let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
       let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
       let _ : IsScalarTower A (FractionRing A) K1 :=
         FractionRing.isScalarTower_liftAlgebra A K1
       IsTotallyRamifiedWithRespectTo A K1) ∧
        Algebra.IsSeparable K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            ∃ l' : ℚ,
              IsDegreePFiniteLevelExtensionOfLevelAfterBaseChange B K L M p l' K1 ∧
                l' ≤ max 0 (max (l - 1) (2 * l - p))) := by
  -- Route correction: the remaining source step has to build a fresh quotient-section witness
  -- from `state`, rather than trying to upgrade the dummy `data/exp` carrier in place.
  -- Proof comment: the coefficient lifts are now fixed, so the next source-faithful stage is to
  -- upgrade them to compatible quotient sections modulo `π ^ mCur`, prove the witness-form
  -- congruence for the updated parameter, and then execute the rank-decreasing/terminal dichotomy.
  -- TODO: first prove the quotient-characteristic adapter at width `data.mCur` so that
  -- `exists_compatible_residue_sections_mod_maximalIdeal_power_of_weaklyUnramified` applies to
  -- `A ⧸ maximalIdeal A ^ data.mCur` and `B ⧸ maximalIdeal B ^ data.mCur`; this currently depends
  -- on the unresolved owner-level bridge `prime_natCast_eq_zero_oneSubZeta_quotient`. Then build
  -- the witness-form reconstruction of the current parameter and combine it with
  -- `oneSubZetaQuotientPolynomial_eval_congruent_sub_frobeniusLinear`,
  -- `add_add_associated_pow_term_congruent_add_of_mem_negPow`, and the terminal Kummer branch
  -- theorems from `Lemma_15_116_14`.
  let _ := hl
  let _ := hAB
  let _ := hLM
  let _ := hκ
  let _ := state
  let _ := data
  let _ := exp
  sorry

variable
  {A B C K L M p}

-- Proof sketch: choose a quotient-polynomial presentation of the given level-`l`
-- extension. Use the congruences `15.116.16.1` and `15.116.16.2` to run the same induction on
-- the residue coefficients as in `Lemma 15.116.12`, but in mixed characteristic and with the
-- Kummer-type polynomial from `Lemma 15.116.13`. The induction produces a finite separable
-- totally ramified extension `K₁ / K` for which either the base change of `A → C` is already a
-- weak solution, or the transformed degree-`p` extension has finite level `l'` with
-- `l' ≤ max (0, l - 1, 2 * l - p)`.
/-- Lemma 15.116.16: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume `A` has mixed characteristic `(0, p)`, `A ⊆ B` is weakly
unramified, `M / L` is a degree-`p` extension of finite level `l > 0`, and the image of
`ResidueField A` in `ResidueField B` is exactly `⋂_{n ≥ 1} (ResidueField B)^(p^n)`. Then there
exists a finite separable extension `K₁ / K`, totally ramified with respect to `A`, such that
either `K₁ / K` is a weak solution for `A → C`, or the base-changed extension
of some canonical reduced base-change branch of `M / L` has finite level `l'` for some
`l' ≤ max (0, l - 1, 2 * l - p)`. -/
theorem exists_totallyRamified_separable_extension_weakSolution_or_finiteLevel_le
    {l : ℚ} (hl : 0 < l)
    (hAB : WeaklyUnramified A B)
    (hLM : IsDegreePFiniteLevelExtensionOfLevel B L M p l)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      (let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
       let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
       let _ : IsScalarTower A (FractionRing A) K1 :=
         FractionRing.isScalarTower_liftAlgebra A K1
       IsTotallyRamifiedWithRespectTo A K1) ∧
        Algebra.IsSeparable K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            ∃ l' : ℚ,
              IsDegreePFiniteLevelExtensionOfLevelAfterBaseChange B K L M p l' K1 ∧
                l' ≤ max 0 (max (l - 1) (2 * l - p))) := by
  -- Route correction: the proof has to follow the source bad-index induction in mixed
  -- characteristic, not the weaker branchwise finite-level extraction from Lemma `15.116.15`.
  have hstate :
      Nonempty (MixedCharacteristicCoefficientExpansionState B L M p l) :=
    exists_initial_mixed_characteristic_coefficient_expansion_state hLM
  obtain ⟨state⟩ := hstate
  have hdata :
      Nonempty (MixedCharacteristicTruncatedCoefficientData state) :=
    exists_truncated_coefficient_data_for_mixed_characteristic_state
      hAB hκ state
  obtain ⟨data⟩ := hdata
  have hrank :
      data.rank = (state.nCur, data.badIndices.card) := by
    -- Proof comment: the current frontier now has the exact lexicographic source rank expected by
    -- the bad-index descent.
    rfl
  have hexp :
      Nonempty (MixedCharacteristicRefinedCoefficientExpansion state data) :=
    refined_truncated_coefficient_expansion_of_mixed_characteristic_state state data
  obtain ⟨exp⟩ := hexp
  -- Proof comment: the coarse index carrier has now been upgraded to actual residue coefficients
  -- together with chosen lifts in `B`. The remaining theorem is the single source-faithful
  -- reduction-or-terminal step on this refined package.
  let _ := hrank
  exact
    refined_truncated_coefficient_expansion_step
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (p := p)
      hl hAB hLM hκ state data exp

end
