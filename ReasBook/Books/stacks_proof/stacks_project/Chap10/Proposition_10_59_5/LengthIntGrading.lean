import Mathlib
import StacksProject_2024.Chap10.Definition_10_58_3
import StacksProject_2024.Chap10.Definition_10_59_1
import StacksProject_2024.Chap10.Lemma_10_52_8
import StacksProject_2024.Chap10.Lemma_10_58_5
import StacksProject_2024.Chap10.Lemma_10_59_2
import StacksProject_2024.Chap10.Proposition_10_58_7
import StacksProject_2024.Chap10.Proposition_10_59_5.TextbookPieceAction

universe u v

open Filter
open HomogeneousIdeal
open IsLocalRing
open scoped BigOperators Ideal

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Ideal

variable (I : Ideal R)

/-- Helper for Proposition 10.59.5: every quotient `M / I^(n + 1)M` attached to an ideal of
definition has finite length. -/
lemma isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsFiniteLength R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  -- Compare a power of the maximal ideal with the chosen ideal of definition.
  have hleRad : maximalIdeal R ≤ I.radical := by
    rw [hI]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  let Q : Type v := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  -- The quotient is killed by `I ^ (n + 1)`, hence also by a power of the maximal ideal.
  have hQtors : Module.IsTorsionBySet R Q (I ^ (n + 1) : Ideal R) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x r hr
    change r • x ∈ (I ^ (n + 1) • (⊤ : Submodule R M))
    exact Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R M) by simp)
  have hQann : (maximalIdeal R) ^ (c * (n + 1)) ≤ Module.annihilator R Q := by
    have hpow : (maximalIdeal R) ^ (c * (n + 1)) ≤ I ^ (n + 1) := by
      simpa [pow_mul] using Ideal.pow_right_mono hc (n + 1)
    exact hpow.trans <| (Module.isTorsionBySet_iff_subset_annihilator R Q).mp hQtors
  have hpowQ : ((maximalIdeal R) ^ (c * (n + 1))) • (⊤ : Submodule R Q) = ⊥ := by
    refine (Submodule.le_annihilator_iff).mp ?_
    simpa [Submodule.annihilator_top] using hQann
  -- Finite generation of the quotient lets us apply the nilpotent maximal-ideal criterion.
  exact isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R)
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hpowQ


/-- Helper for Proposition 10.59.5: the length of the `n`-th associated graded piece agrees with
the Hilbert-Samuel `φ`-value. -/
lemma idealAssociatedGradedPiece_length_eq_phi
    (I : Ideal R) (n : ℕ) :
    Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I M n) = φ_ I M n := by
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  have hsub :
      (RingTheory.Sequence.idealAssociatedGradedStage I M (n + 1)).submoduleOf N =
        (I • (⊤ : Submodule R N)) := by
    -- Rewrite the next stage inside `N` as the intrinsic ideal multiple `I • N`.
    simpa [N, RingTheory.Sequence.idealAssociatedGradedStage, pow_succ', mul_smul] using
      submoduleOf_smul_eq_smul_top (R := R) (M := M) I N
  let e :
      RingTheory.Sequence.idealAssociatedGradedPiece I M n ≃ₗ[R]
        (N ⧸ (I • (⊤ : Submodule R N))) :=
    Submodule.quotEquivOfEq _ _ hsub
  -- Transport along the stage-quotient equivalence, then unfold the source-facing definition.
  calc
    Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I M n) =
        Module.length R (N ⧸ (I • (⊤ : Submodule R N))) := by
          exact e.length_eq
    _ = φ_ I M n := by
      simpa [Ideal.hilbertSamuelPhi, N]

/-- Helper for Proposition 10.59.5: the textbook quotient `I^n M / I^(n + 1) M` is identified
with the internal quotient `I^n M / I (I^n M)` used for the `R / I`-module structure. -/
noncomputable def idealAssociatedGradedInternalPieceEquiv
    (I : Ideal R) (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
        ((I) • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I M n)))) ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I M n :=
  -- Rewrite the internal denominator `I • I^n M` as the next stage `I^(n + 1) M`.
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_top_iff]
    change ((x : M) ∈ I • RingTheory.Sequence.idealAssociatedGradedStage I M n) ↔
      ((x : M) ∈ RingTheory.Sequence.idealAssociatedGradedStage I M (n + 1))
    rw [← mul_smul]
    rw [show I * I ^ n = I ^ (n + 1) by
      rw [Ideal.mul_comm, ← pow_succ]])

/-- Helper for Proposition 10.59.5: each associated graded piece is naturally an `R / I`-module
via the internal quotient model `I^n M / I (I^n M)`. -/
noncomputable instance idealAssociatedGradedPiece.moduleQuotient
    (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) :=
  (idealAssociatedGradedInternalPieceEquiv (R := R) (M := M) I n).symm.toAddEquiv.module _

/-- Helper for Proposition 10.59.5: after transporting the quotient action to the textbook
associated graded piece, the same internal-piece equivalence is linear over `R / I`. -/
noncomputable def idealAssociatedGradedInternalPieceEquivQuotient
    (I : Ideal R) (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
        ((I) • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I M n)))) ≃ₗ[R ⧸ I]
      RingTheory.Sequence.idealAssociatedGradedPiece I M n :=
  by
    -- The `R ⧸ I`-module on the textbook piece was transferred along the same additive
    -- equivalence, so `AddEquiv.linearEquiv` upgrades it to the required linear equivalence.
    exact
      (AddEquiv.linearEquiv
        (A := R ⧸ I)
        ((idealAssociatedGradedInternalPieceEquiv (R := R) (M := M) I n).symm.toAddEquiv)).symm

/-- Helper for Proposition 10.59.5: the degree-zero owner piece of `gr_I(R)` matches the internal
quotient model `I^0 / I(I^0)` before the final transport to the ordinary quotient `R / I`. -/
noncomputable def idealAssociatedGradedRingGradeZeroInternalQuotientLinearEquiv
    (I : Ideal R) :
    idealAssociatedGradedRingGrade I 0 ≃ₗ[R]
      (RingTheory.Sequence.idealAssociatedGradedStage I R 0 ⧸
        (I • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I R 0)))) := by
  -- Compare the owner degree-zero piece with the textbook quotient piece, then rewrite that piece
  -- through the internal quotient model used for the `R / I`-module structure.
  exact
    (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I 0).trans
      (idealAssociatedGradedInternalPieceEquiv (R := R) (M := R) I 0).symm

/-- Helper for Proposition 10.59.5: the associated graded piece has the same length whether it is
viewed as an `R`-module or as an `R / I`-module. -/
lemma idealAssociatedGradedPiece_length_over_quotient_eq_phi
    (I : Ideal R) (n : ℕ) :
    Module.length (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) = φ_ I M n := by
  let Q :=
    RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
      ((I) • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I M n)))
  have hlengthQ :
      Module.length R Q = Module.length (R ⧸ I) Q :=
    Module.length_eq_of_surjective
      (R := R ⧸ I) (S := R) (M := Q) Ideal.Quotient.mk_surjective
  -- Compare lengths on the internal quotient first, then transport back to the textbook quotient.
  calc
    Module.length (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) =
        Module.length (R ⧸ I) Q := by
          exact
            (idealAssociatedGradedInternalPieceEquivQuotient (R := R) (M := M) I n).symm.length_eq
    _ = Module.length R Q := by
          symm
          exact hlengthQ
    _ = Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I M n) := by
          exact (idealAssociatedGradedInternalPieceEquiv (R := R) (M := M) I n).length_eq
    _ = φ_ I M n := by
          exact idealAssociatedGradedPiece_length_eq_phi (R := R) (M := M) I n

/-- Helper for Proposition 10.59.5: the canonical `lof` range of the `n`-th direct-sum summand is
linearly equivalent to the `n`-th associated graded piece itself. -/
noncomputable def idealAssociatedGradedPiece_range_equiv
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece I M n ≃ₗ[R ⧸ I]
      LinearMap.range
        (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n) :=
  let lofN :=
    DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n
  let compN :=
    DirectSum.component (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n
  -- The `n`-th direct-sum summand is canonically equivalent to its image range.
  { toFun := fun x ↦ ⟨lofN x, ⟨x, rfl⟩⟩
    invFun := fun x ↦ compN x
    left_inv := by
      intro x
      simp [lofN, compN]
    right_inv := by
      rintro ⟨x, ⟨y, rfl⟩⟩
      apply Subtype.ext
      simp [lofN, compN]
    map_add' := by
      intro x y
      apply Subtype.ext
      simp [lofN]
    map_smul' := by
      intro r x
      apply Subtype.ext
      simp [lofN] }

/-- Helper for Proposition 10.59.5: the range of the `n`-th direct-sum summand in the associated
graded module has length `φ_{I,M}(n)` over `R / I`. -/
lemma idealAssociatedGradedPiece_range_length_over_quotient_eq_phi
    (I : Ideal R) (n : ℕ) :
    Module.length (R ⧸ I)
        (LinearMap.range
          (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n)) =
      φ_ I M n := by
  -- Replace the range by the original direct-sum summand before using the quotient-length formula.
  calc
    Module.length (R ⧸ I)
        (LinearMap.range
          (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n)) =
      Module.length (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) := by
        simpa using (idealAssociatedGradedPiece_range_equiv (R := R) (M := M) I n).symm.length_eq
    _ = φ_ I M n := by
      exact idealAssociatedGradedPiece_length_over_quotient_eq_phi (R := R) (M := M) I n

/-- Helper for Proposition 10.59.5: the direct-sum model of `gr_I(M)` is reindexed to `ℤ` by
putting the negative degrees equal to `⊥` and the nonnegative degrees equal to the corresponding
`DirectSum.lof` ranges. -/
noncomputable def associatedGradedIntGrading
    (I : Ideal R) :
    ℤ → Submodule (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedModule I M) :=
  fun n ↦
    if 0 ≤ n then
      LinearMap.range
        (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n.toNat)
    else
      ⊥

/-- Helper for Proposition 10.59.5: on nonnegative indices, the `ℤ`-adapter grading is exactly the
range of the corresponding direct-sum summand. -/
lemma associatedGradedIntGrading_eq_range_of_nonneg
    (I : Ideal R) {n : ℤ} (hn : 0 ≤ n) :
    associatedGradedIntGrading (R := R) I n =
      LinearMap.range
        (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n.toNat) := by
  -- Unfold the adapter and keep the nonnegative branch.
  simp [associatedGradedIntGrading, hn]

/-- Helper for Proposition 10.59.5: on the nonnegative tail, the reindexed graded piece has the
same `R / I`-length as the corresponding Hilbert-Samuel `φ`-value. -/
lemma associatedGradedIntGrading_length_over_quotient_eq_phi_of_nonneg
    (I : Ideal R) {n : ℤ} (hn : 0 ≤ n) :
    Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) =
      φ_ I M n.toNat := by
  -- Replace the integer-indexed piece by the matching direct-sum summand range and then reuse the
  -- already proved quotient-length formula for that range.
  rw [associatedGradedIntGrading_eq_range_of_nonneg (R := R) (M := M) I hn]
  exact idealAssociatedGradedPiece_range_length_over_quotient_eq_phi
    (R := R) (M := M) I n.toNat

/-- Helper for Proposition 10.59.5: on negative indices, the `ℤ`-adapter grading is trivial. -/
lemma associatedGradedIntGrading_eq_bot_of_neg
    (I : Ideal R) {n : ℤ} (hn : n < 0) :
    associatedGradedIntGrading (R := R) (M := M) I n = ⊥ := by
  have hnn : ¬ 0 ≤ n := by
    linarith
  -- Negative degrees are declared to be `⊥` so the textbook grading is extended by zero.
  simp [associatedGradedIntGrading, hnn]

/-- Helper for Proposition 10.59.5: the nonnegative degree `n` piece of the `ℤ`-adapter grading is
canonically the original `n`-th associated graded summand. -/
noncomputable def associatedGradedIntGrading_nat_linearEquiv
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece I M n ≃ₗ[R ⧸ I]
      associatedGradedIntGrading (R := R) (M := M) I (n : ℤ) := by
  have hnonneg : 0 ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  -- First identify the integer-lifted piece with the range of the `n`-th direct-sum summand.
  let hgrade :
      associatedGradedIntGrading (R := R) (M := M) I (n : ℤ) =
        LinearMap.range
          (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n) :=
    associatedGradedIntGrading_eq_range_of_nonneg (R := R) (M := M) I hnonneg
  -- Then reuse the already constructed range equivalence for the `n`-th summand.
  exact
    (idealAssociatedGradedPiece_range_equiv (R := R) (M := M) I n).trans
      (LinearEquiv.ofEq _ _ hgrade.symm)

/-- Helper for Proposition 10.59.5: under the nonnegative `ℤ`-grading, the transported `n`-th
piece is still represented by the same `DirectSum.lof` term in the ambient associated graded
module. -/
lemma associatedGradedIntGrading_nat_linearEquiv_coe
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedPiece I M n) :
    ((associatedGradedIntGrading_nat_linearEquiv (R := R) (M := M) I n x :
      associatedGradedIntGrading (R := R) (M := M) I (n : ℤ)) :
        RingTheory.Sequence.idealAssociatedGradedModule I M) =
      DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n x := by
  -- Unfold the range model: the transported subtype keeps the same ambient `DirectSum.lof`
  -- representative.
  simp [associatedGradedIntGrading_nat_linearEquiv, associatedGradedIntGrading_eq_range_of_nonneg,
    idealAssociatedGradedPiece_range_equiv]

/-- Helper for Proposition 10.59.5: reindexing the `ℕ`-graded direct sum by `ℤ` gives a direct-sum
decomposition of the ambient associated graded module. -/
noncomputable def associatedGradedIntGrading_decompose
    (I : Ideal R) :
    RingTheory.Sequence.idealAssociatedGradedModule I M →ₗ[R ⧸ I]
      DirectSum ℤ (fun n ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I n)) :=
  -- Send the original `n`-th direct-sum generator to the same generator, now viewed in degree
  -- `(n : ℤ)` of the reindexed grading.
  DirectSum.toModule (R ⧸ I) ℕ
    (DirectSum ℤ (fun n ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I n)))
    (fun n ↦
      (DirectSum.lof (R ⧸ I) ℤ
        (fun z ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I z)) (n : ℤ)).comp
        ((associatedGradedIntGrading_nat_linearEquiv (R := R) (M := M) I n).toLinearMap))

/-- Helper for Proposition 10.59.5: the `ℤ`-reindexed decomposition recombines back to the
original direct-sum presentation of `gr_I(M)`. -/
lemma associatedGradedIntGrading_decompose_left_inv
    (I : Ideal R) :
    DirectSum.coeLinearMap (associatedGradedIntGrading (R := R) (M := M) I) ∘ₗ
        associatedGradedIntGrading_decompose (R := R) I =
      LinearMap.id :=
by
  -- Check the recomposition identity on the original `ℕ`-indexed generators.
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  change DirectSum.coeLinearMap (associatedGradedIntGrading (R := R) (M := M) I)
      (associatedGradedIntGrading_decompose (R := R) I
        (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n x)) =
    DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n x
  rw [associatedGradedIntGrading_decompose, DirectSum.toModule_lof]
  rw [LinearMap.comp_apply]
  rw [DirectSum.coeLinearMap_lof]
  exact associatedGradedIntGrading_nat_linearEquiv_coe (R := R) (M := M) I n x

/-- Helper for Proposition 10.59.5: each `ℤ`-graded summand is recovered by decomposing its
ambient image and reading off the same degree. -/
lemma associatedGradedIntGrading_decompose_right_inv
    (I : Ideal R) :
    associatedGradedIntGrading_decompose (R := R) I ∘ₗ
        DirectSum.coeLinearMap (associatedGradedIntGrading (R := R) (M := M) I) =
      LinearMap.id :=
by
  -- A direct-sum map is determined by its values on the homogeneous `lof` generators.
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro xbar
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  by_cases hd : d < 0
  · have hbot :
        associatedGradedIntGrading (R := R) (M := M) I d = ⊥ :=
      associatedGradedIntGrading_eq_bot_of_neg (R := R) (M := M) I hd
    haveI : Subsingleton ↥(associatedGradedIntGrading (R := R) (M := M) I d) := by
      rw [hbot]
      infer_instance
    have hxbar : xbar = 0 := Subsingleton.elim _ _
    have hlof_zero :=
      LinearMap.map_zero
        (DirectSum.lof (R ⧸ I) ℤ
          (fun n ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I n)) d)
    rw [hxbar]
    rw [hlof_zero]
    exact LinearMap.map_zero (associatedGradedIntGrading_decompose (R := R) (M := M) I)
  · have hnonneg : 0 ≤ d := le_of_not_gt hd
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    let x :=
      (associatedGradedIntGrading_nat_linearEquiv (R := R) (M := M) I n).symm xbar
    have hxbar :
        associatedGradedIntGrading_nat_linearEquiv (R := R) (M := M) I n x = xbar := by
      exact LinearEquiv.apply_symm_apply _ _
    calc
      associatedGradedIntGrading_decompose (R := R) (M := M) I
          ((xbar : associatedGradedIntGrading (R := R) (M := M) I (n : ℤ)) :
            RingTheory.Sequence.idealAssociatedGradedModule I M) =
        associatedGradedIntGrading_decompose (R := R) (M := M) I
          (DirectSum.lof (R ⧸ I) ℕ (RingTheory.Sequence.idealAssociatedGradedPiece I M) n
            x) := by
              rw [← hxbar]
              rw [associatedGradedIntGrading_nat_linearEquiv_coe]
      _ = DirectSum.lof (R ⧸ I) ℤ
            (fun n ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I n))
            (n : ℤ)
            (associatedGradedIntGrading_nat_linearEquiv (R := R) (M := M) I n x) := by
              rw [associatedGradedIntGrading_decompose, DirectSum.toModule_lof,
                LinearMap.comp_apply]
              rfl
      _ = DirectSum.lof (R ⧸ I) ℤ
            (fun n ↦ ↥(associatedGradedIntGrading (R := R) (M := M) I n))
            (n : ℤ) xbar := by
              rw [hxbar]

/-- Helper for Proposition 10.59.5: the reindexed grading on `gr_I(M)` is a genuine internal
direct-sum decomposition. -/
noncomputable instance associatedGradedIntGrading_decomposition
    (I : Ideal R) :
    DirectSum.Decomposition (associatedGradedIntGrading (R := R) (M := M) I) :=
  -- Package the verified decomposition linear map and its two inverse identities.
  DirectSum.Decomposition.ofLinearMap
    (ℳ := associatedGradedIntGrading (R := R) (M := M) I)
    (associatedGradedIntGrading_decompose (R := R) I)
    (associatedGradedIntGrading_decompose_left_inv (R := R) (M := M) I)
    (associatedGradedIntGrading_decompose_right_inv (R := R) (M := M) I)

/-- Helper for Proposition 10.59.5: if `I` is an ideal of definition, then the quotient ring
`R / I` is Artinian. -/
lemma isArtinianRing_quotient_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsArtinianRing (R ⧸ I) := by
  -- The ring quotient is the zeroth Hilbert-Samuel quotient, hence it has finite length.
  rw [isArtinianRing_iff_isFiniteLength]
  rw [← Module.length_ne_top_iff]
  have hlen :
      Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
    Module.length_eq_of_surjective
      (R := R ⧸ I) (S := R) (M := R ⧸ I) Ideal.Quotient.mk_surjective
  have hpowTop :
      (I ^ 1 • (⊤ : Submodule R R)) = (I : Ideal R) := by
    simpa [pow_one, Ideal.smul_eq_mul] using (Ideal.mul_top I)
  have hfinite0 : IsFiniteLength R (R ⧸ (I ^ 1 • (⊤ : Submodule R R))) :=
    isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
      (R := R) (M := R) I hI 0
  have hlen0 :
      Module.length R (R ⧸ (I ^ 1 • (⊤ : Submodule R R))) = Module.length R (R ⧸ I) := by
    simpa [hpowTop] using
      (Submodule.quotEquivOfEq
        (I ^ 1 • (⊤ : Submodule R R)) (I : Ideal R) hpowTop).length_eq
  have hfiniteR : Module.length R (R ⧸ I) ≠ ⊤ := by
    have hne0 : Module.length R (R ⧸ (I ^ 1 • (⊤ : Submodule R R))) ≠ ⊤ := by
      simpa [Module.length_ne_top_iff] using hfinite0
    rw [← hlen0]
    exact hne0
  simpa [hlen] using hfiniteR

/-- Helper for Proposition 10.59.5: for positive indices, `χ` splits as the predecessor value plus
the corresponding `φ`-value after converting finite lengths to `ℚ`. -/
lemma hilbertSamuelChi_toNat_eq_hilbertSamuelPhi_toNat_add_pred_of_pos
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {n : ℕ} (hn : 0 < n) :
    ((χ_ I M n).toNat : ℚ) = ((φ_ I M n).toNat : ℚ) + ((χ_ I M (n - 1)).toNat : ℚ) := by
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let J : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  have hJN : J ≤ N := by
    -- Powers of an ideal act by a descending chain on `⊤`.
    simpa [J, N] using Submodule.pow_smul_top_le I M (Nat.le_succ n)
  have hphi :
      Module.length R (N ⧸ J.submoduleOf N) = φ_ I M n := by
    -- Identify the successive quotient with the defining `φ`-quotient.
    have hsub :
        J.submoduleOf N = (I • (⊤ : Submodule R N)) := by
      simpa [J, N, pow_succ', mul_smul] using
        submoduleOf_smul_eq_smul_top (R := R) (M := M) I N
    rw [Ideal.hilbertSamuelPhi]
    simpa [N] using congrArg (fun S : Submodule R N ↦ Module.length R (N ⧸ S)) hsub
  have hdecomp :
      χ_ I M n = χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N) := by
    -- Decompose `M / I^(n + 1)M` through `M / I^nM`.
    have hchiPred : Module.length R (M ⧸ N) = χ_ I M (n - 1) := by
      have hpred : n - 1 + 1 = n := by
        omega
      rw [Ideal.hilbertSamuelChi]
      dsimp [N]
      rw [hpred]
    have hchi : χ_ I M n = Module.length R (M ⧸ J) := by
      simpa [Ideal.hilbertSamuelChi, J]
    have hlen :
        Module.length R (M ⧸ J) =
          Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
      simpa [J, N] using
        (length_quotient_eq_add_length_submodule_quotient_of_le
          (R := R) (M := M) hJN)
    calc
      χ_ I M n = Module.length R (M ⧸ J) := hchi
      _ = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := hlen
      _ = χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N) := by
        rw [hchiPred]
  have hχpred_ne : χ_ I M (n - 1) ≠ ⊤ := by
    -- Ideals of definition give finite length for every adic quotient.
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI (n - 1)
  have hχ_ne : χ_ I M n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI n
  have hsucc_ne : Module.length R (N ⧸ J.submoduleOf N) ≠ ⊤ := by
    -- Finiteness of `χ n` forces the successive quotient to be finite as well.
    intro htop
    have : χ_ I M n = ⊤ := by
      simpa [hdecomp, htop]
    exact hχ_ne this
  have hnat :
      (χ_ I M n).toNat =
        (χ_ I M (n - 1)).toNat + (φ_ I M n).toNat := by
    -- Apply `ENat.toNat` to the exact length decomposition.
    have hnat' :
        (χ_ I M n).toNat =
          (χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N)).toNat := by
      exact congrArg ENat.toNat hdecomp
    rw [ENat.toNat_add hχpred_ne hsucc_ne] at hnat'
    simpa [hphi] using hnat'
  have hrat :
      ((χ_ I M n).toNat : ℚ) =
        ((χ_ I M (n - 1)).toNat : ℚ) + ((φ_ I M n).toNat : ℚ) := by
    exact_mod_cast hnat
  simpa [add_comm] using hrat

-- After packaging the associated graded owner action, the finite generation of `gr_I(M)` by
-- degree-zero classes and the degree-one generation of the irrelevant ideal of `gr_I(R)` are the
-- two source-faithful inputs for the final Proposition `10.58.7` application.

end Ideal

end
