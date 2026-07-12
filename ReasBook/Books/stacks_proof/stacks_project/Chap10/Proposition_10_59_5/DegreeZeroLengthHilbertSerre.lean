import StacksProject_2024.Chap10.Proposition_10_59_5.LengthMapOwner
import StacksProject_2024.Chap10.Proposition_10_59_5.LengthIntGrading
import StacksProject_2024.Chap10.Proposition_10_59_5.DegreeOneGeneration

-- Proof rescue support for Proposition 10.59.5: convert the K0-valued Hilbert-Serre theorem
-- from Proposition 10.58.7 into a length-valued statement over the degree-zero ring.

noncomputable section

universe u v w

open Filter
open HomogeneousIdeal
open scoped BigOperators Ideal

local instance instAddActionNatIntDegreeZeroLengthHilbertSerre : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

/-- Helper for Chap10 Proposition 10 59 5: eventual equality preserves numerical polynomiality
on `ℤ` for functions valued in any additive group. -/
lemma isNumericalPolynomial_of_eventuallyEq
    {A : Type*} [AddCommGroup A] {f g : ℤ → A}
    (hg : IsNumericalPolynomial g) (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial f := by
  -- Reuse the binomial-polynomial expression after replacing the function on the eventual tail.
  rcases hg with ⟨r, a, ha⟩
  exact ⟨r, a, hfg.trans ha⟩

/-- Helper for Chap10 Proposition 10 59 5: rational-valued numerical polynomiality is invariant
under eventual equality on `ℤ`. -/
lemma isNumericalPolynomial_eventuallyEq_iff
    {f g : ℤ → ℚ} (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial f ↔ IsNumericalPolynomial g := by
  -- Transfer the same eventual binomial expansion in each direction across the eventual equality.
  constructor
  · intro hf
    exact isNumericalPolynomial_of_eventuallyEq hf hfg.symm
  · intro hg
    exact isNumericalPolynomial_of_eventuallyEq hg hfg

namespace Submodule

/-- Helper for Chap10 Proposition 10 59 5: restricting a submodule along a surjective algebra
map does not change its composition length. -/
lemma length_restrictScalars_eq_of_surjective
    {A : Type u} {B : Type v} {G : Type w}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup G] [Module B G] [Module A G] [IsScalarTower A B G]
    (N : Submodule B G) (hsurj : Function.Surjective (algebraMap A B)) :
    Module.length A (Submodule.restrictScalars A N) = Module.length B N := by
  -- Apply the canonical length comparison to the inherited module structures on the submodule.
  exact Module.length_eq_of_surjective (R := B) (S := A) (M := N) hsurj

end Submodule

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] [IsNoetherianRing S]
variable {G : Type w} [AddCommGroup G] [Module S G]

/-- Helper for Chap10 Proposition 10 59 5: applying the Artinian length realization to the
K0-valued Hilbert-Serre theorem gives a length-valued numerical polynomial for the homogeneous
pieces, viewed by restriction of scalars to the degree-zero ring. -/
lemma gradedPieceLengthZero_isNumericalPolynomial_of_span_degreeOne_eq_irrelevant
    (ℳ : ℤ → Submodule S G)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S G] [Algebra.FiniteType (𝒜 0) S] [IsArtinianRing (𝒜 0)]
    (hgen : Ideal.span (𝒜 1 : Set S) = 𝒜₊.toIdeal) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        let _ : Module (𝒜 0) (ℳ n) := Module.restrictScalars (𝒜 0) S (ℳ n)
        ((Module.length (𝒜 0) (ℳ n)).toNat : ℚ)) := by
  -- First use Proposition 10.58.7 in its existing `K'_0(S₀)`-valued form.
  have hK : IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) :=
    gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_span_degreeOne_eq_irrelevant
      (𝒜 := 𝒜) (ℳ := ℳ) hgen
  have hZ :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          finiteGrothendieckGroup_lengthMap_owner (𝒜 0)
            (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ n)) := by
    -- Postcompose the numerical polynomial with the additive length map on `K'_0(S₀)`.
    simpa [Function.comp] using
      IsNumericalPolynomial.comp hK (finiteGrothendieckGroup_lengthMap_owner (𝒜 0))
  have hQ :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((finiteGrothendieckGroup_lengthMap_owner (𝒜 0)
            (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ n) : ℤ) : ℚ)) := by
    -- The target of this item is rational-valued, so cast the integer length realization once.
    simpa [Function.comp, Int.coe_castAddHom] using
      IsNumericalPolynomial.comp hZ (Int.castAddHom ℚ)
  -- Unfold the class of a homogeneous piece and evaluate the length map on that generator.
  simpa [gradedPieceFiniteGrothendieckGroupClass] using hQ

section DegreeZeroPieces

variable {G₀ : Type w} [AddCommGroup G₀] [Module (𝒜 0) G₀]

/-- Helper for Chap10 Proposition 10 59 5: the corrected K0-valued class function for genuine
degree-zero homogeneous pieces `ℳ n`, viewed as finite modules over `𝒜 0`. -/
noncomputable def gradedPieceFiniteGrothendieckGroupClassZero
    (ℳ : ℤ → Submodule (𝒜 0) G₀)
    [∀ n, Module.Finite (𝒜 0) (ℳ n)] :
    ℤ → finiteGrothendieckGroup (𝒜 0) :=
  fun n ↦ finiteGrothendieckGroupOf (𝒜 0) (FGModuleCat.of (𝒜 0) (ℳ n))

omit [IsNoetherianRing S] in
/-- Helper for Chap10 Proposition 10 59 5: the Artinian length realization evaluates the
corrected degree-zero K0 class of a homogeneous piece as its ordinary length. -/
lemma finiteGrothendieckGroup_lengthMap_owner_apply_classZero
    (ℳ : ℤ → Submodule (𝒜 0) G₀)
    [∀ n, Module.Finite (𝒜 0) (ℳ n)] [IsArtinianRing (𝒜 0)] (n : ℤ) :
    finiteGrothendieckGroup_lengthMap_owner (𝒜 0)
        (gradedPieceFiniteGrothendieckGroupClassZero 𝒜 ℳ n) =
      ((Module.length (𝒜 0) (ℳ n)).toNat : ℤ) := by
  -- Unfold only the corrected K0 class, then use the owner computation on a generator class.
  exact finiteGrothendieckGroup_lengthMap_owner_apply_of (𝒜 0)
    (FGModuleCat.of (𝒜 0) (ℳ n))

omit [IsNoetherianRing S] in
/-- Helper for Chap10 Proposition 10 59 5: after a corrected degree-zero K0 Hilbert-Serre theorem
is available, applying the owner length realization gives numerical polynomiality of the
degree-zero lengths. -/
lemma gradedPieceLengthZero_isNumericalPolynomial_of_classZero
    (ℳ : ℤ → Submodule (𝒜 0) G₀)
    [∀ n, Module.Finite (𝒜 0) (ℳ n)] [IsArtinianRing (𝒜 0)]
    (hK : IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClassZero 𝒜 ℳ)) :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((Module.length (𝒜 0) (ℳ n)).toNat : ℚ)) := by
  -- Postcompose the corrected K0-valued polynomial with the Artinian length realization.
  have hZ :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          finiteGrothendieckGroup_lengthMap_owner (𝒜 0)
            (gradedPieceFiniteGrothendieckGroupClassZero 𝒜 ℳ n)) := by
    simpa [Function.comp] using
      IsNumericalPolynomial.comp hK (finiteGrothendieckGroup_lengthMap_owner (𝒜 0))
  have hQ :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((finiteGrothendieckGroup_lengthMap_owner (𝒜 0)
            (gradedPieceFiniteGrothendieckGroupClassZero 𝒜 ℳ n) : ℤ) : ℚ)) := by
    -- Cast the integer length realization to the rational-valued surface used by Proposition 10.59.5.
    simpa [Function.comp, Int.coe_castAddHom] using
      IsNumericalPolynomial.comp hZ (Int.castAddHom ℚ)
  -- Evaluate the length map on each generator class of the corrected K0 function.
  simpa [finiteGrothendieckGroup_lengthMap_owner_apply_classZero (𝒜 := 𝒜) (ℳ := ℳ)] using hQ

end DegreeZeroPieces

namespace Ideal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Chap10 Proposition 10 59 5: use the canonical commutative ring structure on the
degree-zero owner piece `(gr_I R)_0`. -/
noncomputable local instance associatedGradedRingGradeZeroCommRing
    (I : Ideal R) :
    CommRing (idealAssociatedGradedRingGrade I 0) :=
  SetLike.GradeZero.instCommRing (idealAssociatedGradedRingGrade (R := R) I)

/-- Helper for Chap10 Proposition 10 59 5: view `R ⧸ I` as an algebra over the degree-zero
owner piece `(gr_I R)_0` through the quotient bridge. -/
noncomputable local instance associatedGradedRingGradeZeroAlgebraQuotient
    (I : Ideal R) :
    Algebra (idealAssociatedGradedRingGrade I 0) (R ⧸ I) :=
  (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm.toRingEquiv.toRingHom.toAlgebra

/-- Helper for Chap10 Proposition 10 59 5: the scalar action of `(gr_I R)_0` on `R ⧸ I`
induced by the quotient bridge. -/
noncomputable local instance associatedGradedRingGradeZeroModuleQuotient
    (I : Ideal R) :
    Module (idealAssociatedGradedRingGrade I 0) (R ⧸ I) :=
  RingHom.toModule
    (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm.toRingHom

/-- Helper for Chap10 Proposition 10 59 5: expose the degree-zero scalar action on `R ⧸ I`
without reopening typeclass search through the owner-ring subtype. -/
noncomputable local instance associatedGradedRingGradeZeroSMulQuotient
    (I : Ideal R) :
    SMul (idealAssociatedGradedRingGrade I 0) (R ⧸ I) :=
  (associatedGradedRingGradeZeroModuleQuotient (R := R) I).toDistribMulAction.toMulAction.toSMul

/-- Helper for Chap10 Proposition 10 59 5: the degree-zero quotient bridge gives a surjective
algebra map `(gr_I R)_0 → R ⧸ I`. -/
lemma associatedGradedRingGradeZero_algebraMap_quotient_surjective
    (I : Ideal R) :
    Function.Surjective (algebraMap (idealAssociatedGradedRingGrade I 0) (R ⧸ I)) := by
  -- This records the exact side condition used whenever a finite quotient-linear module is
  -- restricted to the degree-zero owner ring.
  simpa using
    (AlgEquiv.surjective (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm)

/-- Helper for Chap10 Proposition 10 59 5: restrict the associated graded module's `R ⧸ I`
module structure along `(gr_I R)_0 → R ⧸ I`. -/
noncomputable local instance associatedGradedModuleGradeZeroModule
    (I : Ideal R) :
    Module (idealAssociatedGradedRingGrade I 0)
      (RingTheory.Sequence.idealAssociatedGradedModule I M) :=
  Module.compHom (RingTheory.Sequence.idealAssociatedGradedModule I M)
    (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm.toRingHom

/-- Helper for Chap10 Proposition 10 59 5: expose the restricted `(gr_I R)_0` action on
`gr_I(M)` without repeated instance search. -/
noncomputable local instance associatedGradedModuleGradeZeroSMul
    (I : Ideal R) :
    SMul (idealAssociatedGradedRingGrade I 0)
      (RingTheory.Sequence.idealAssociatedGradedModule I M) :=
  (associatedGradedModuleGradeZeroModule (R := R) (M := M) I).toDistribMulAction.toMulAction.toSMul

/-- Helper for Chap10 Proposition 10 59 5: the degree-zero owner action on `gr_I(M)` is
compatible with the intermediate quotient-ring action. -/
noncomputable local instance associatedGradedModuleGradeZeroScalarTower
    (I : Ideal R) :
    IsScalarTower (idealAssociatedGradedRingGrade I 0) (R ⧸ I)
      (RingTheory.Sequence.idealAssociatedGradedModule I M) where
  smul_assoc r s x := by
    -- Both scalar actions are induced by the same quotient-bridge ring hom, so compatibility
    -- reduces to associativity of the original `R ⧸ I`-module structure.
    exact mul_smul ((idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm r) s x

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero family of homogeneous
pieces of `gr_I(M)`, obtained from the existing `R ⧸ I` pieces by restriction of scalars along
`(gr_I R)_0 → R ⧸ I`. -/
noncomputable def associatedGradedIntGradingDegreeZero
    (I : Ideal R) :
    ℤ → Submodule (idealAssociatedGradedRingGrade I 0)
      (RingTheory.Sequence.idealAssociatedGradedModule I M) :=
  fun n ↦ Submodule.restrictScalars (idealAssociatedGradedRingGrade I 0)
    (associatedGradedIntGrading (R := R) (M := M) I n)

omit [Module.Finite R M] in
/-- Helper for Chap10 Proposition 10 59 5: membership in the corrected degree-zero piece is the
same as membership in the original `R ⧸ I`-linear associated graded piece. -/
lemma associatedGradedIntGradingDegreeZero_mem_iff
    (I : Ideal R) (n : ℤ)
    (x : RingTheory.Sequence.idealAssociatedGradedModule I M) :
    x ∈ associatedGradedIntGradingDegreeZero (R := R) (M := M) I n ↔
      x ∈ associatedGradedIntGrading (R := R) (M := M) I n := by
  -- The corrected family is only a restriction of scalars; its carrier is unchanged.
  exact Iff.rfl

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero piece has the same
underlying additive group as the original quotient-linear integer piece. -/
noncomputable def associatedGradedIntGradingDegreeZero_addEquiv
    (I : Ideal R) (n : ℤ) :
    associatedGradedIntGrading (R := R) (M := M) I n ≃+
      associatedGradedIntGradingDegreeZero (R := R) (M := M) I n where
  toFun x :=
    ⟨x, (associatedGradedIntGradingDegreeZero_mem_iff (R := R) (M := M) I n x).2 x.2⟩
  invFun x :=
    ⟨x, (associatedGradedIntGradingDegreeZero_mem_iff (R := R) (M := M) I n x).1 x.2⟩
  left_inv x := by
    -- Both directions preserve the ambient associated-graded-module element.
    ext
    rfl
  right_inv x := by
    -- Both directions preserve the ambient associated-graded-module element.
    ext
    rfl
  map_add' x y := by
    -- The transported equivalence is carrier-identical, so additivity is extensional.
    ext
    rfl

/-- Helper for Chap10 Proposition 10 59 5: the pointwise additive equivalence from the original
integer grading to the corrected degree-zero grading preserves ambient elements. -/
@[simp] lemma associatedGradedIntGradingDegreeZero_addEquiv_coe
    (I : Ideal R) (n : ℤ)
    (x : associatedGradedIntGrading (R := R) (M := M) I n) :
    ((associatedGradedIntGradingDegreeZero_addEquiv (R := R) (M := M) I n x :
        associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :
      RingTheory.Sequence.idealAssociatedGradedModule I M) = x := by
  -- The equivalence only changes the scalar owner attached to the submodule.
  rfl

/-- Helper for Chap10 Proposition 10 59 5: the inverse pointwise additive equivalence also
preserves the ambient associated-graded-module element. -/
@[simp] lemma associatedGradedIntGradingDegreeZero_addEquiv_symm_coe
    (I : Ideal R) (n : ℤ)
    (x : associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :
    (((associatedGradedIntGradingDegreeZero_addEquiv (R := R) (M := M) I n).symm x :
        associatedGradedIntGrading (R := R) (M := M) I n) :
      RingTheory.Sequence.idealAssociatedGradedModule I M) = x := by
  -- The inverse equivalence also only changes the scalar owner attached to the same carrier.
  rfl

/-- Helper for Chap10 Proposition 10 59 5: an ideal of definition makes the degree-zero piece of
the owner associated graded ring Artinian. -/
lemma idealAssociatedGradedRingGradeZero_isArtinianRing
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsArtinianRing (idealAssociatedGradedRingGrade I 0) := by
  -- Transport Artinianness from the ordinary quotient through the canonical degree-zero bridge.
  letI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_isIdealOfDefinition (R := R) I hI
  exact (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).toRingEquiv.isArtinianRing

omit [IsLocalRing R] in
/-- Helper for Chap10 Proposition 10 59 5: each textbook associated graded piece is finite over
the quotient ring `R ⧸ I`. -/
lemma idealAssociatedGradedPiece_moduleFinite_over_quotient
    (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (RingTheory.Sequence.idealAssociatedGradedPiece I M n) := by
  -- Prove finite generation on the internal quotient model and transport it to the textbook piece.
  let Q :=
    RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
      ((I) • (⊤ : Submodule R (RingTheory.Sequence.idealAssociatedGradedStage I M n)))
  have hQFiniteR : Module.Finite R Q := by
    dsimp [Q]
    infer_instance
  have hQFiniteQuot : Module.Finite (R ⧸ I) Q := by
    -- The quotient action is the one induced by the surjection `R → R ⧸ I`.
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) Q
  -- The internal quotient equivalence carries finite generation to the textbook quotient.
  exact Module.Finite.equiv
    (idealAssociatedGradedInternalPieceEquivQuotient (R := R) (M := M) I n)

/-- Helper for Chap10 Proposition 10 59 5: every integer-reindexed associated graded piece is
finite over the quotient ring `R ⧸ I`. -/
lemma associatedGradedIntGrading_moduleFinite_over_quotient
    (I : Ideal R) (n : ℤ) :
    Module.Finite (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n) := by
  -- Split the integer grading into the genuine nonnegative summands and the trivial negative part.
  by_cases hn : 0 ≤ n
  · rw [associatedGradedIntGrading_eq_range_of_nonneg (R := R) (M := M) I hn]
    have hpiece :
        Module.Finite (R ⧸ I)
          (RingTheory.Sequence.idealAssociatedGradedPiece I M n.toNat) :=
      idealAssociatedGradedPiece_moduleFinite_over_quotient (R := R) (M := M) I n.toNat
    exact Module.Finite.equiv
      (idealAssociatedGradedPiece_range_equiv (R := R) (M := M) I n.toNat)
  · have hneg : n < 0 := lt_of_not_ge hn
    rw [associatedGradedIntGrading_eq_bot_of_neg (R := R) (M := M) I hneg]
    infer_instance

/-- Helper for Chap10 Proposition 10 59 5: every corrected degree-zero associated graded piece is
finite over `(gr_I R)_0`. -/
lemma associatedGradedIntGradingDegreeZero_moduleFinite
    (I : Ideal R) (n : ℤ) :
    Module.Finite (idealAssociatedGradedRingGrade I 0)
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) := by
  -- Start with finite generation over `R ⧸ I`, then restrict the generators along the surjective
  -- degree-zero quotient bridge.
  refine Module.Finite.of_fg ?_
  have hfgOld :
      (associatedGradedIntGrading (R := R) (M := M) I n).FG := by
    exact Module.Finite.iff_fg.mp
      (associatedGradedIntGrading_moduleFinite_over_quotient (R := R) (M := M) I n)
  have hsurj :
      Function.Surjective (algebraMap (idealAssociatedGradedRingGrade I 0) (R ⧸ I)) := by
    exact associatedGradedRingGradeZero_algebraMap_quotient_surjective (R := R) I
  exact Submodule.FG.restrictScalars_of_surjective
    (R := idealAssociatedGradedRingGrade I 0) (A := R ⧸ I)
    (M := RingTheory.Sequence.idealAssociatedGradedModule I M)
    (S := associatedGradedIntGrading (R := R) (M := M) I n) hfgOld hsurj

/-- Helper for Chap10 Proposition 10 59 5: expose finite generation of the corrected
degree-zero pieces as a local instance for the K0 class function. -/
local instance associatedGradedIntGradingDegreeZero_moduleFiniteInstance
    (I : Ideal R) (n : ℤ) :
    Module.Finite (idealAssociatedGradedRingGrade I 0)
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :=
  associatedGradedIntGradingDegreeZero_moduleFinite (R := R) (M := M) I n

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero pieces are additive groups
with the ring spelling used for length computations. -/
local instance associatedGradedIntGradingDegreeZero_addCommGroup
    (I : Ideal R) (n : ℤ) :
    AddCommGroup
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :=
  Submodule.addCommGroup _

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero pieces inherit their
module structure with the ring spelling used for length computations. -/
local instance associatedGradedIntGradingDegreeZero_module
    (I : Ideal R) (n : ℤ) :
    Module (idealAssociatedGradedRingGrade I 0)
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :=
  Submodule.module _

/-- Helper for Chap10 Proposition 10 59 5: for an ideal of definition, every corrected
degree-zero associated graded piece has finite length over `(gr_I R)_0`. -/
lemma associatedGradedIntGradingDegreeZero_isFiniteLength
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℤ) :
    IsFiniteLength (idealAssociatedGradedRingGrade I 0)
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) := by
  -- The corrected pieces are finite over the degree-zero owner ring, and that ring is Artinian
  -- for ideals of definition; Hopkins-Levitzki converts the pair into finite length.
  letI : IsArtinianRing (idealAssociatedGradedRingGrade I 0) :=
    idealAssociatedGradedRingGradeZero_isArtinianRing (R := R) I hI
  exact
    ((IsArtinianRing.tfae (idealAssociatedGradedRingGrade I 0)
      (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).out 0 3).mp
      (associatedGradedIntGradingDegreeZero_moduleFinite (R := R) (M := M) I n)

/-- Helper for Chap10 Proposition 10 59 5: for an ideal of definition, the length of a corrected
degree-zero associated graded piece is finite. -/
lemma associatedGradedIntGradingDegreeZero_length_ne_top
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℤ) :
    Module.length (idealAssociatedGradedRingGrade I 0)
        (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) ≠ ⊤ := by
  -- Record the finite-length side condition in the exact form needed by length-valued arguments.
  rw [Module.length_ne_top_iff]
  exact associatedGradedIntGradingDegreeZero_isFiniteLength (R := R) (M := M) I hI n

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero piece and the original
quotient-linear piece have the same length. -/
lemma associatedGradedIntGradingDegreeZero_length_eq_quotient
    (I : Ideal R) (n : ℤ) :
    Module.length (idealAssociatedGradedRingGrade I 0)
        (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) =
      Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) := by
  -- The corrected piece is only a restriction of scalars along the surjective degree-zero bridge.
  have hsurj :
      Function.Surjective (algebraMap (idealAssociatedGradedRingGrade I 0) (R ⧸ I)) :=
    -- Build this in the local transported ring/algebra spelling used by `Module.length`.
    (AlgEquiv.surjective (idealAssociatedGradedRingGradeZeroQuotientBridge (R := R) I).symm)
  simpa [associatedGradedIntGradingDegreeZero] using
    (Submodule.length_restrictScalars_eq_of_surjective
      (A := idealAssociatedGradedRingGrade I 0) (B := R ⧸ I)
      (G := RingTheory.Sequence.idealAssociatedGradedModule I M)
      (associatedGradedIntGrading (R := R) (M := M) I n) hsurj)

/-- Helper for Chap10 Proposition 10 59 5: the corrected degree-zero length function and the
quotient-linear associated-graded length function agree pointwise, hence eventually. -/
lemma associatedGradedIntGradingDegreeZero_length_eventuallyEq_quotientLength
    (I : Ideal R) :
    (fun n : ℤ ↦
        ((Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ) := by
  -- Package the already proved pointwise length comparison in the exact eventual-equality shape
  -- consumed by the numerical-polynomial transport lemmas below.
  refine Filter.Eventually.of_forall ?_
  intro n
  have hlen :
      Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) =
        Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) :=
    associatedGradedIntGradingDegreeZero_length_eq_quotient
      (R := R) (M := M) I n
  have hnat :
      (Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat =
        (Module.length (R ⧸ I)
          (associatedGradedIntGrading (R := R) (M := M) I n)).toNat :=
    congrArg ENat.toNat hlen
  exact congrArg (fun m : ℕ ↦ (m : ℚ)) hnat

/-- Helper for Chap10 Proposition 10 59 5: corrected degree-zero K0 polynomiality realizes as
numerical polynomiality of the corrected degree-zero length function. -/
lemma associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_of_classZero
    (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (hK :
      IsNumericalPolynomial
        (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I))) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- Transport the K0-valued corrected statement through the Artinian length realization of
  -- the degree-zero owner ring.
  letI : IsArtinianRing (idealAssociatedGradedRingGrade I 0) :=
    idealAssociatedGradedRingGradeZero_isArtinianRing (R := R) I hI
  exact gradedPieceLengthZero_isNumericalPolynomial_of_classZero
    (𝒜 := idealAssociatedGradedRingGrade I)
    (ℳ := associatedGradedIntGradingDegreeZero (R := R) (M := M) I) hK

/-- Helper for Chap10 Proposition 10 59 5: a corrected degree-zero K0 Hilbert-Serre theorem
implies numerical polynomiality of the original quotient-length function. -/
lemma associatedGradedIntGrading_quotientLength_isNumericalPolynomial_of_classZero
    (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (hK :
      IsNumericalPolynomial
        (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I))) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- First realize the corrected K0-polynomial by lengths over the owner degree-zero ring.
  have hzero :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (idealAssociatedGradedRingGrade I 0)
              (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) := by
    exact associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_of_classZero
      (R := R) (M := M) I hI hK
  -- Then replace owner degree-zero lengths by the quotient lengths pointwise.
  refine isNumericalPolynomial_of_eventuallyEq hzero (Filter.Eventually.of_forall ?_)
  intro n
  have hlen :
      Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) =
        Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :=
    (associatedGradedIntGradingDegreeZero_length_eq_quotient
      (R := R) (M := M) I n).symm
  have hnat :
      (Module.length (R ⧸ I)
          (associatedGradedIntGrading (R := R) (M := M) I n)).toNat =
        (Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat :=
    congrArg ENat.toNat hlen
  exact congrArg (fun m : ℕ ↦ (m : ℚ)) hnat

/-- Helper for Chap10 Proposition 10 59 5: on the nonnegative tail, the corrected degree-zero
length function agrees with the Hilbert-Samuel `φ`-function. -/
lemma associatedGradedIntGradingDegreeZero_length_eventuallyEq_hilbertSamuelPhi
    (I : Ideal R) :
    (fun n : ℤ ↦
        ((Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- On the nonnegative tail, first compare the corrected piece with the quotient-linear piece,
  -- then use the source length computation for that quotient-linear piece.
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  have hlen :
      Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) =
        Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) :=
    associatedGradedIntGradingDegreeZero_length_eq_quotient
      (R := R) (M := M) I n
  have hquot :
      Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) =
        φ_ I M n.toNat :=
    associatedGradedIntGrading_length_over_quotient_eq_phi_of_nonneg
      (R := R) (M := M) I hn
  have hlen_phi :
      Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) =
        φ_ I M n.toNat :=
    hlen.trans hquot
  have hnat :
      (Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat =
        (φ_ I M n.toNat).toNat :=
    congrArg ENat.toNat hlen_phi
  exact congrArg (fun m : ℕ ↦ (m : ℚ)) hnat

/-- Helper for Chap10 Proposition 10 59 5: numerical polynomiality of the Hilbert-Samuel
`φ`-function transfers to the corrected degree-zero associated graded length function. -/
lemma associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_of_hilbertSamuelPhi
    (I : Ideal R)
    (hphi : IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ)) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- The corrected degree-zero lengths and the Hilbert-Samuel `φ`-function agree on the
  -- nonnegative tail, so the same eventual binomial expansion applies.
  exact isNumericalPolynomial_of_eventuallyEq hphi
    (associatedGradedIntGradingDegreeZero_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I)

/-- Helper for Chap10 Proposition 10 59 5: corrected degree-zero associated graded length
polynomiality is equivalent to Hilbert-Samuel `φ` polynomiality on the nonnegative tail. -/
lemma associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_iff_hilbertSamuelPhi
    (I : Ideal R) :
    IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (idealAssociatedGradedRingGrade I 0)
              (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) ↔
      IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- This records the transport boundary separately from the Hilbert-Serre argument.
  exact isNumericalPolynomial_eventuallyEq_iff
    (associatedGradedIntGradingDegreeZero_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I)

/-- Helper for Chap10 Proposition 10 59 5: for an ideal of definition, every integer-reindexed
associated graded piece has finite length over `R ⧸ I`. -/
lemma associatedGradedIntGrading_isFiniteLength_over_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℤ) :
    IsFiniteLength (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n) := by
  -- Over the Artinian quotient ring, finite generation of each piece implies finite length.
  letI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_isIdealOfDefinition (R := R) I hI
  exact
    ((IsArtinianRing.tfae (R ⧸ I)
      (associatedGradedIntGrading (R := R) (M := M) I n)).out 0 3).mp
      (associatedGradedIntGrading_moduleFinite_over_quotient
        (R := R) (M := M) I n)

/-- Helper for Chap10 Proposition 10 59 5: on the nonnegative tail, the quotient length of the
integer-reindexed associated graded piece agrees with the Hilbert-Samuel `φ`-value. -/
lemma associatedGradedIntGrading_length_eventuallyEq_hilbertSamuelPhi
    (I : Ideal R) :
    (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- Restrict to the nonnegative tail, where the integer grading is the original associated
  -- graded summand and its quotient length is the defining `φ`-length.
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  have hlen :
      Module.length (R ⧸ I) (associatedGradedIntGrading (R := R) (M := M) I n) =
        φ_ I M n.toNat :=
    associatedGradedIntGrading_length_over_quotient_eq_phi_of_nonneg
      (R := R) (M := M) I hn
  have hnat :
      (Module.length (R ⧸ I)
          (associatedGradedIntGrading (R := R) (M := M) I n)).toNat =
        (φ_ I M n.toNat).toNat :=
    congrArg ENat.toNat hlen
  exact_mod_cast hnat

/-- Helper for Chap10 Proposition 10 59 5: polynomiality of the associated-graded length
function transfers to the Hilbert-Samuel `φ`-function on the nonnegative tail. -/
lemma hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_associatedGradedLength
    (I : Ideal R)
    (hLen :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (R ⧸ I)
              (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ))) :
    IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- Reverse the eventual length/`φ` identification so the numerical-polynomial witness for
  -- associated-graded lengths becomes a witness for the Hilbert-Samuel `φ`-function.
  exact isNumericalPolynomial_of_eventuallyEq hLen
    (associatedGradedIntGrading_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I).symm

/-- Helper for Chap10 Proposition 10 59 5: associated-graded length polynomiality is equivalent
to Hilbert-Samuel `φ` polynomiality after passing to the nonnegative tail. -/
lemma associatedGradedIntGrading_length_isNumericalPolynomial_iff_hilbertSamuelPhi
    (I : Ideal R) :
    IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (R ⧸ I)
              (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) ↔
      IsNumericalPolynomial fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- Package the eventual length/`φ` comparison as an iff so the final proof only has to provide
  -- one independent Hilbert-Serre input, not redo tail transport in both directions.
  exact isNumericalPolynomial_eventuallyEq_iff
    (associatedGradedIntGrading_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I)

/-- Helper for Chap10 Proposition 10 59 5: after realizing the corrected degree-zero K0 class by
the Artinian length map, the resulting rational-valued function agrees with the Hilbert-Samuel
`φ`-function on the nonnegative tail. -/
lemma associatedGradedIntGradingDegreeZero_classZero_length_eventuallyEq_hilbertSamuelPhi
    (I : Ideal R) [IsArtinianRing (idealAssociatedGradedRingGrade I 0)] :
    (fun n : ℤ ↦
        ((finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0)
          (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n) : ℤ) : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℚ) := by
  -- Realize the corrected K0 class by the degree-zero owner length, then reuse the established
  -- eventual comparison between those lengths and the Hilbert-Samuel `φ`-function.
  filter_upwards
    [associatedGradedIntGradingDegreeZero_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I] with n hn
  have hlen :
      finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0)
          (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n) =
        ((Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℤ) := by
    exact finiteGrothendieckGroup_lengthMap_owner_apply_classZero
      (𝒜 := idealAssociatedGradedRingGrade I)
      (ℳ := associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n
  rw [hlen]
  exact hn

/-- Helper for Chap10 Proposition 10 59 5: the integer-valued owner length realization of the
corrected degree-zero K0 class agrees eventually with the integer Hilbert-Samuel `φ`-function. -/
lemma associatedGradedIntGradingDegreeZero_classZero_lengthInt_eventuallyEq_hilbertSamuelPhi
    (I : Ideal R) [IsArtinianRing (idealAssociatedGradedRingGrade I 0)] :
    (fun n : ℤ ↦
        finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0)
          (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n)) =ᶠ[atTop]
      fun n : ℤ ↦ ((φ_ I M n.toNat).toNat : ℤ) := by
  -- Use the already proved degree-zero length comparison and keep the result in `ℤ`, avoiding
  -- the rational cast used by the final length-valued statement.
  filter_upwards
    [associatedGradedIntGradingDegreeZero_length_eventuallyEq_hilbertSamuelPhi
      (R := R) (M := M) I] with n hn
  have hlen :
      finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0)
          (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n) =
        ((Module.length (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℤ) := by
    exact finiteGrothendieckGroup_lengthMap_owner_apply_classZero
      (𝒜 := idealAssociatedGradedRingGrade I)
      (ℳ := associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n
  rw [hlen]
  exact_mod_cast hn

/-- Helper for Chap10 Proposition 10 59 5: corrected degree-zero K0 polynomiality implies
polynomiality of the integer-valued owner length realization. -/
lemma associatedGradedIntGradingDegreeZero_classZero_lengthInt_isNumericalPolynomial_of_classZero
    (I : Ideal R) [IsArtinianRing (idealAssociatedGradedRingGrade I 0)]
    (hK :
      IsNumericalPolynomial
        (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I))) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0)
          (gradedPieceFiniteGrothendieckGroupClassZero (idealAssociatedGradedRingGrade I)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I) n)) := by
  -- Postcompose the corrected K0 polynomial with the Artinian owner length map.
  simpa [Function.comp] using
    IsNumericalPolynomial.comp hK
      (finiteGrothendieckGroup_lengthMap_owner (idealAssociatedGradedRingGrade I 0))

/-- Helper for Chap10 Proposition 10 59 5: the pointwise length bridge between corrected
degree-zero pieces and quotient-linear pieces transports numerical-polynomiality in both
directions. -/
lemma associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_iff_quotientLength
    (I : Ideal R) :
    IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (idealAssociatedGradedRingGrade I 0)
              (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) ↔
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (R ⧸ I)
              (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- The named pointwise bridge keeps this transport boundary separate from the Hilbert-Serre
  -- input; both directions are just eventual-equality invariance.
  exact isNumericalPolynomial_eventuallyEq_iff
    (associatedGradedIntGradingDegreeZero_length_eventuallyEq_quotientLength
      (R := R) (M := M) I)

/-- Helper for Chap10 Proposition 10 59 5: the corrected length-valued Hilbert-Serre input for
the degree-zero pieces of `gr_I(M)`. -/
lemma associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- Route correction: the previous frontier asked for the full corrected K0 class of the
  -- degree-zero pieces. That is stronger than the final theorem needs and still forces the wrong
  -- owner-module normal form. The source proof only needs the length shadow: a Hilbert-Serre
  -- theorem for degree-zero modules with positive-degree owner scalars acting by degree shifts.
  have hfinitePieces :
      ∀ n : ℤ,
        IsFiniteLength (idealAssociatedGradedRingGrade I 0)
          (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) :=
    associatedGradedIntGradingDegreeZero_isFiniteLength (R := R) (M := M) I hI
  have hlengthFinite :
      ∀ n : ℤ,
        Module.length (idealAssociatedGradedRingGrade I 0)
            (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n) ≠ ⊤ :=
    associatedGradedIntGradingDegreeZero_length_ne_top (R := R) (M := M) I hI
  -- The finite-length side conditions are now normalized for the corrected length-valued
  -- Hilbert-Serre theorem; what remains is the finite homogeneous shifted-action argument.
  have _ := hfinitePieces
  have _ := hlengthFinite
  -- TODO(Chap10 Proposition 10 59 5): prove the Hilbert-Samuel `φ`-function is numerical
  -- polynomial from corrected shifted-action data, finite homogeneous generators of `gr_I(M)`,
  -- and the degree-one Hilbert-Serre first-difference argument; the tail transport to this
  -- corrected length function is now isolated in the preceding helper.
  refine associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial_of_hilbertSamuelPhi
    (R := R) (M := M) I ?_
  sorry

/-- Helper for Chap10 Proposition 10 59 5: numerical polynomiality of the corrected degree-zero
lengths implies numerical polynomiality of the original quotient-length function. -/
lemma associatedGradedIntGrading_quotientLength_isNumericalPolynomial_of_degreeZeroLength
    (I : Ideal R)
    (hzero :
      IsNumericalPolynomial
        (fun n : ℤ ↦
          ((Module.length (idealAssociatedGradedRingGrade I 0)
              (associatedGradedIntGradingDegreeZero (R := R) (M := M) I n)).toNat : ℚ))) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- Replace owner degree-zero lengths by quotient lengths through the named transport bridge.
  exact isNumericalPolynomial_of_eventuallyEq hzero
    (associatedGradedIntGradingDegreeZero_length_eventuallyEq_quotientLength
      (R := R) (M := M) I).symm

/-- Helper for Chap10 Proposition 10 59 5: the remaining Hilbert-Serre input for the associated
graded module, in the target-facing quotient-length form. -/
lemma associatedGradedIntGrading_length_isNumericalPolynomial_from_zeroPieceHilbertSerre
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- Consume the corrected length-valued theorem through the quotient-length adapter.
  exact associatedGradedIntGrading_quotientLength_isNumericalPolynomial_of_degreeZeroLength
    (R := R) (M := M) I
    (associatedGradedIntGradingDegreeZero_length_isNumericalPolynomial
      (R := R) (M := M) I hI)

/-- Helper for Chap10 Proposition 10 59 5: the length function of the integer-reindexed
associated graded pieces is numerical polynomial. This is the target-facing Hilbert-Serre bridge
left after reducing the proof to the owner `gr_I(R)` action and degree-zero length transport. -/
lemma associatedGradedIntGrading_length_isNumericalPolynomial_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦
        ((Module.length (R ⧸ I)
            (associatedGradedIntGrading (R := R) (M := M) I n)).toNat : ℚ)) := by
  -- The final theorem consumes the target-facing Hilbert-Serre input directly; the tail
  -- comparison with `φ` remains available for downstream users but is no longer used circularly.
  exact associatedGradedIntGrading_length_isNumericalPolynomial_from_zeroPieceHilbertSerre
    (R := R) (M := M) I hI

end Ideal

end
