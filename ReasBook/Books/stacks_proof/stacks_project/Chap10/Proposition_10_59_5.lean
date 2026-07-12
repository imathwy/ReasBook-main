import Mathlib
import StacksProject_2024.Chap10.Definition_10_58_3
import StacksProject_2024.Chap10.Definition_10_59_1
import StacksProject_2024.Chap10.Lemma_10_52_8
import StacksProject_2024.Chap10.Lemma_10_58_5
import StacksProject_2024.Chap10.Lemma_10_59_2
import StacksProject_2024.Chap10.Lemma_10_150_6.AssociatedGradedAPI
import StacksProject_2024.Chap10.Proposition_10_58_7
import StacksProject_2024.Chap10.Proposition_10_59_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open HomogeneousIdeal
open IsLocalRing
open scoped BigOperators Ideal

noncomputable section

local instance instAddActionNatIntProposition10595 : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Ideal

-- Proof sketch: form the associated graded ring `⊕_{d ≥ 0} I^d / I^(d + 1)` and the associated
-- graded module via the owner abstractions `idealAssociatedGradedRing I` and
-- `RingTheory.Sequence.idealAssociatedGradedModule I M`; Proposition 10.58.7 shows that the
-- resulting graded-piece Grothendieck-class function is numerical polynomial, and Lemma 10.55.1
-- identifies its length with the Hilbert-Samuel `φ`-function.
variable (I : Ideal R)

/-- Helper for Chap10 Proposition 10 59 5: eventual equality preserves numerical polynomiality
for rational-valued functions. -/
private lemma isNumericalPolynomial_congr_atTop
    {f g : ℤ → ℚ} (hg : IsNumericalPolynomial g) (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial f := by
  -- Reuse the same binomial expansion after replacing the function on the eventual tail.
  rcases hg with ⟨r, a, ha⟩
  exact ⟨r, a, hfg.trans ha⟩

/-- Helper for Chap10 Proposition 10 59 5: on the nonnegative tail, the length of the
integer-indexed associated graded piece is the Hilbert-Samuel `φ`-value. -/
private lemma associatedGradedIntGrading_length_eventuallyEq_phi
    (I : Ideal R) :
    (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- Restrict to the nonnegative tail, where the integer reindexing agrees with the original
  -- associated graded summand and its quotient length is already identified with `φ`.
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  have hlen :
      Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) =
        φ_ I M n.toNat :=
    associatedGradedIntGrading_length_over_quotient_eq_phi_of_nonneg
      (R := R) (M := M) I hn
  have hnat :
      (Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n)).toNat =
        (φ_ I M n.toNat).toNat :=
    congrArg ENat.toNat hlen
  exact_mod_cast hnat

/-- Helper for Chap10 Proposition 10 59 5: an ideal of definition makes the degree-zero owner
piece of the associated graded ring Artinian. -/
private lemma idealAssociatedGradedRingGradeZero_isArtinianRing_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsArtinianRing (idealAssociatedGradedRingGrade I 0) := by
  -- First use the already proved Artinianness of `R / I`, then transport it across the canonical
  -- degree-zero quotient bridge into the owner piece `(gr_I R)_0`.
  letI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_isIdealOfDefinition (R := R) I hI
  exact (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).toRingEquiv.isArtinianRing

/-- Helper for Chap10 Proposition 10 59 5: each textbook associated graded quotient piece is
finite over the quotient ring `R ⧸ I`. -/
private lemma idealAssociatedGradedPiece_moduleFinite_quotient
    (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) := by
  -- First prove finiteness for the internal quotient model as an `R`-module.
  let Q :=
    RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
      ((I) • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I M n)))
  have hQFiniteR : Module.Finite R Q := by
    dsimp [Q]
    infer_instance
  have hQFiniteQuot : Module.Finite (R ⧸ I) Q := by
    -- The quotient action is transported from the finite `R`-module structure.
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) Q
  -- Transport finite generation across the quotient-linear equivalence to the textbook piece.
  exact Module.Finite.equiv
    (idealAssociatedGradedInternalPieceEquivQuotient (R := R) (M := M) I n)

/-- Helper for Chap10 Proposition 10 59 5: every integer-reindexed associated graded piece is
finite over `R ⧸ I`. -/
private instance associatedGradedIntGrading_moduleFinite_quotient
    (I : Ideal R) (n : ℤ) :
    Module.Finite (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n) := by
  by_cases hn : 0 ≤ n
  · -- In nonnegative degree, identify the reindexed piece with the original quotient summand.
    rw [associatedGradedIntGrading_eq_range_of_nonneg (R := R) (M := M) I hn]
    have hpiece :
        Module.Finite (R ⧸ I)
          (RingTheory.Sequence.idealAssociatedGradedPiece I M n.toNat) :=
      idealAssociatedGradedPiece_moduleFinite_quotient (R := R) (M := M) I n.toNat
    exact Module.Finite.equiv
      (idealAssociatedGradedPiece_range_equiv (R := R) (M := M) I n.toNat)
  · -- Negative degrees are `⊥`, hence finite.
    have hneg : n < 0 := lt_of_not_ge hn
    rw [associatedGradedIntGrading_eq_bot_of_neg (R := R) (M := M) I hneg]
    infer_instance

/-- Helper for Chap10 Proposition 10 59 5: for an ideal of definition, every integer-reindexed
associated graded piece has finite length over `R ⧸ I`. -/
private lemma associatedGradedIntGrading_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℤ) :
    IsFiniteLength (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n) := by
  -- The quotient ring is Artinian, and the preceding helper gives finite generation for each
  -- integer-reindexed piece; Hopkins-Levitzki converts these two facts into finite length.
  letI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_isIdealOfDefinition (R := R) I hI
  exact
    ((IsArtinianRing.tfae (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n)).out 0 3).mp
      (inferInstance :
        Module.Finite (R ⧸ I)
          (associatedGradedIntGrading (R := R) (M := M) I n))

/-- Helper for Proposition 10.59.5: the associated graded length function is numerical
polynomial. This is the corrected length-valued Hilbert-Serre bridge for the proof of the
Hilbert-Samuel `φ`-function. -/
private lemma associatedGradedIntGrading_length_isNumericalPolynomial
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) :=
by
  -- Route correction: the previous proof tried to prove a stronger K0-valued statement for
  -- pieces viewed over `R ⧸ I`. That normal form is too strong: genuine homogeneous pieces are
  -- only degree-zero modules and are shifted by positive-degree owner scalars. The required
  -- bridge is the direct length-valued Hilbert-Serre theorem for those degree-zero pieces,
  -- transported at the end to the existing `R ⧸ I` spelling.
  -- Delegate the source Hilbert-Serre input to the theorem-local support module; the main target
  -- proof only needs the resulting length-valued numerical-polynomial bridge.
  exact associatedGradedIntGrading_length_isNumericalPolynomial_of_isIdealOfDefinition
    (R := R) (M := M) I hI

/-- Proposition 10.59.5 (1): if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`I` is an ideal of definition, then the Hilbert-Samuel `φ`-function of `M` with respect to `I`,
viewed as a function on the integers via `Int.toNat`, is a numerical polynomial. -/
@[stacks 00K8]
theorem hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  have howner :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (R ⧸ I)
              (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
    -- Route correction: isolate the remaining owner-packaging application of Proposition `10.58.7`
    -- in a dedicated helper so the main theorem is reduced to the final identification with `φ`.
    exact associatedGradedIntGrading_length_isNumericalPolynomial
      (R := R) (M := M) I hI
  -- Transfer the associated-graded length polynomial across the eventual length/`φ`
  -- identification isolated in the theorem-local support module.
  exact hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_associatedGradedLength
    (R := R) (M := M) I howner

-- Proof sketch: use the first part together with Lemma 10.58.5, which upgrades eventual
-- numerical polynomiality of the first difference to numerical polynomiality of the original
-- function via `IsNumericalPolynomial.of_sub_pred`, after identifying the first difference of
-- `χ_{I,M}` with `φ_{I,M}` for large `n`.
/-- Proposition 10.59.5 (2): if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`I` is an ideal of definition, then the Hilbert-Samuel `χ`-function of `M` with respect to `I`,
viewed as a function on the integers via `Int.toNat`, is a numerical polynomial. -/
@[stacks 00K8]
theorem hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial fun n : ℤ ↦ ((χ_ I M n.toNat).toNat : ℚ) := by
  -- Reduce `χ` to its eventual backward difference, which agrees with `φ` on the positive tail.
  refine IsNumericalPolynomial.of_sub_pred ?_
  rcases
      hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
        (R := R) (M := M) I hI with
    ⟨r, a, ha⟩
  refine ⟨r, a, ?_⟩
  have hdiff :
      (fun n : ℤ ↦
        ((χ_ I M n.toNat).toNat : ℚ) - ((χ_ I M (n - 1).toNat).toNat : ℚ)) =ᶠ[atTop]
        fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
    filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn
    have hn_pos : 0 < n := by
      linarith
    have hn_toNat_pos : 0 < n.toNat := by
      have hn_cast : (0 : ℤ) < (n.toNat : ℤ) := by
        simpa [Int.toNat_of_nonneg hn_pos.le] using hn_pos
      exact_mod_cast hn_cast
    have hpred_toNat : (n - 1).toNat = n.toNat - 1 := by
      simpa using (Int.toNat_sub_of_le hn)
    have hsplit :
        ((χ_ I M n.toNat).toNat : ℚ) =
          ((φ_ I M n.toNat).toNat : ℚ) + ((χ_ I M (n.toNat - 1)).toNat : ℚ) := by
      exact hilbertSamuelChi_toNat_eq_hilbertSamuelPhi_toNat_add_pred_of_pos
        (R := R) (M := M) I hI hn_toNat_pos
    -- Rewrite the predecessor index on the integer tail and solve the resulting linear identity.
    rw [hpred_toNat]
    linarith
  -- Combine the eventual difference identification with the numerical-polynomial witness for `φ`.
  filter_upwards [hdiff, ha] with n hdiffn han
  exact hdiffn.trans han

end Ideal

end
