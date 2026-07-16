import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped BigOperators TensorProduct Pointwise

universe u v

noncomputable section

/-- The quotient-Rees model of the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)` of an
ideal `I`. -/
abbrev idealAssociatedGradedRing {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I

/-- The degree-one monomial attached to an element of `I` lies in the Rees algebra of `I`. -/
theorem idealAssociatedGradedDegreeOne_mem {R : Type u} [CommRing R] {I : Ideal R} (x : I) :
    monomial 1 (x : R) ∈ reesAlgebra I := by
  refine (reesAlgebra.monomial_mem (I := I) (i := 1) (r := (x : R))).2 ?_
  simpa [pow_one] using x.2

/-- The degree-one class in the associated graded ring determined by an element of `I`. -/
def idealAssociatedGradedDegreeOne {R : Type u} [CommRing R] {I : Ideal R} (x : I) :
    idealAssociatedGradedRing I :=
  Ideal.Quotient.mk _ ⟨monomial 1 (x : R), idealAssociatedGradedDegreeOne_mem x⟩

theorem idealAssociatedGradedIdeal_le_comap
    {R : Type u} [CommRing R] {I : Ideal R}
    {S : Type v} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) :
    Ideal.map (algebraMap R (reesAlgebra I)) I ≤
      Ideal.comap (reesAlgebraMap f hIJ)
        (Ideal.map (algebraMap S (reesAlgebra J)) J) := by
  -- Check the defining Rees-ideal containment on the degree-zero generators coming from `I`.
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  have hfr : f r ∈ J := Ideal.mem_comap.mp (hIJ hr)
  have hmem :
      algebraMap S (reesAlgebra J) (f r) ∈ Ideal.map (algebraMap S (reesAlgebra J)) J := by
    -- The image of `f r` is one of the target generators.
    exact Ideal.mem_map_of_mem (algebraMap S (reesAlgebra J)) hfr
  have hmap :
      reesAlgebraMap f hIJ (algebraMap R (reesAlgebra I) r) =
        algebraMap S (reesAlgebra J) (f r) := by
    -- On constants, `reesAlgebraMap` acts coefficientwise by `f`.
    apply Subtype.ext
    simp [reesAlgebraMap]
  -- Rewriting the source generator image lands it in the target mapped ideal.
  simpa [Ideal.mem_comap, hmap] using hmem

/-- The canonical map on quotient-Rees models of associated graded rings induced by a ring map
sending `I` into `J`. -/
def idealAssociatedGradedMap
    {R : Type u} [CommRing R] {I : Ideal R}
    {S : Type v} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) :
    idealAssociatedGradedRing I →+* idealAssociatedGradedRing J :=
  Ideal.quotientMap
    (Ideal.map (algebraMap S (reesAlgebra J)) J)
    (reesAlgebraMap f hIJ)
    (idealAssociatedGradedIdeal_le_comap f hIJ)

section

variable {R : Type u} [CommRing R]

/-- The quotient-Rees model of `gr_I(R)` is naturally an algebra over `R / I`. -/
instance idealAssociatedGradedRing.algebraQuotient (I : Ideal R) :
    Algebra (R ⧸ I) (idealAssociatedGradedRing I) :=
  Ideal.Quotient.algebraQuotientMapQuotient

section

variable [IsLocalRing R]

/-- For the maximal ideal of a local ring, the associated graded ring is naturally an algebra over
the residue field. -/
instance idealAssociatedGradedRing.algebraResidueField :
    Algebra (IsLocalRing.ResidueField R)
      (idealAssociatedGradedRing (IsLocalRing.maximalIdeal R)) := by
  simpa [IsLocalRing.ResidueField] using
    (idealAssociatedGradedRing.algebraQuotient (I := IsLocalRing.maximalIdeal R))

end

abbrev idealAssociatedGradedRingQuotientMap (I : Ideal R) :
    reesAlgebra I →ₐ[R] idealAssociatedGradedRing I :=
  Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)

/-- The degree-`n` homogeneous piece of the quotient-Rees model of the associated graded ring. -/
def idealAssociatedGradedRingGrade (I : Ideal R) (n : ℕ) :
    Submodule R (idealAssociatedGradedRing I) :=
  (reesAlgebraGrade I n).map (idealAssociatedGradedRingQuotientMap I).toLinearMap

/-- The class of an element of `I` in degree one is homogeneous of degree one. -/
theorem idealAssociatedGradedDegreeOne_mem_grade {I : Ideal R} (x : I) :
    idealAssociatedGradedDegreeOne x ∈ idealAssociatedGradedRingGrade I 1 := by
  refine ⟨reesAlgebraDegreeOne I x, reesAlgebraDegreeOne_mem I x, rfl⟩

/-- The canonical map on associated graded rings induced by `f` preserves the degree-`n`
homogeneous pieces. -/
theorem idealAssociatedGradedMap_mem_grade
    {S : Type v} [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ)
    {x : idealAssociatedGradedRing I}
    (hx : x ∈ idealAssociatedGradedRingGrade I n) :
    idealAssociatedGradedMap f hIJ x ∈ idealAssociatedGradedRingGrade J n := by
  -- Unpack the source homogeneous class to a homogeneous Rees representative.
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨reesAlgebraMap f hIJ y, ?_, rfl⟩
  -- Mapping the degree-`n` Rees representative preserves its homogeneous degree.
  rcases hy with ⟨z, rfl⟩
  refine ⟨⟨f z.1, ?_⟩, ?_⟩
  · have hmap : f z.1 ∈ Ideal.map f (I ^ n) := Ideal.mem_map_of_mem f z.2
    have hpow : Ideal.map f (I ^ n) ≤ J ^ n := by
      simpa [Ideal.map_pow] using
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) n :
          Ideal.map f I ^ n ≤ J ^ n)
    exact hpow hmap
  · -- The Rees-algebra map keeps the unique degree-`n` monomial shape unchanged.
    apply Subtype.ext
    exact (Polynomial.map_monomial (f := f) (n := n) (a := z.1)).symm

/-- The degree-`n` component of the canonical map on associated graded rings induced by `f`. -/
def idealAssociatedGradedGradeMap
    {S : Type v} [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ) :
    idealAssociatedGradedRingGrade I n → idealAssociatedGradedRingGrade J n :=
  fun x ↦
    ⟨idealAssociatedGradedMap f hIJ x,
      idealAssociatedGradedMap_mem_grade I J f hIJ n x.2⟩

end

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `n`-th stage `I^n M` of the `I`-adic filtration. -/
abbrev idealAssociatedGradedStage (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R M :=
  ((I ^ n) • ⊤ : Submodule R M)

/-- The degree-`n` graded piece `I^n M / I^(n + 1) M`, written as the quotient of the subtype
`I^n M` by its next filtration step. -/
abbrev idealAssociatedGradedPiece (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  idealAssociatedGradedStage I M n ⧸
    (idealAssociatedGradedStage I M (n + 1)).submoduleOf
      (idealAssociatedGradedStage I M n)

/-- The associated graded module `⊕_{n ≥ 0} I^n M / I^(n + 1) M` of the `I`-adic filtration. -/
abbrev idealAssociatedGradedModule (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Type v :=
  DirectSum ℕ (idealAssociatedGradedPiece I M)

noncomputable def idealAssociatedGradedInternalPieceEquiv
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (idealAssociatedGradedStage I M n ⧸
        ((I) • ⊤ : Submodule R (idealAssociatedGradedStage I M n))) ≃ₗ[R]
      idealAssociatedGradedPiece I M n :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_top_iff]
    change ((x : M) ∈ I • idealAssociatedGradedStage I M n) ↔
      ((x : M) ∈ idealAssociatedGradedStage I M (n + 1))
    rw [← mul_smul]
    rw [show I * I ^ n = I ^ (n + 1) by
      rw [Ideal.mul_comm, ← pow_succ]])

noncomputable instance (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (idealAssociatedGradedPiece I M n) :=
  (idealAssociatedGradedInternalPieceEquiv I M n).symm.toAddEquiv.module _

abbrev quasiRegularIdeal (rs : List R) : Ideal R :=
  Ideal.ofList rs

/-- The internal quotient model `J^n M / J (J^n M)` used to build the polynomial action before
identifying it with the textbook quotient. -/
abbrev quasiRegularAssociatedGradedInternalPiece
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  idealAssociatedGradedStage (quasiRegularIdeal rs) M n ⧸
    ((quasiRegularIdeal rs) • ⊤ :
      Submodule R (idealAssociatedGradedStage (quasiRegularIdeal rs) M n))

/-- The internal direct-sum model built from `J^n M / J (J^n M)`. -/
abbrev quasiRegularAssociatedGradedInternal
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  DirectSum ℕ (quasiRegularAssociatedGradedInternalPiece rs M)

abbrev quasiRegularTotalDegree {rs : List R} (e : Fin rs.length →₀ ℕ) : ℕ :=
  e.degree

abbrev quasiRegularStage (rs : List R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R M :=
  idealAssociatedGradedStage (quasiRegularIdeal rs) M n

abbrev quasiRegularDenominator (rs : List R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R (quasiRegularStage rs M n) :=
  ((quasiRegularIdeal rs) • ⊤ : Submodule R (quasiRegularStage rs M n))

/-- Helper for 10.69.0.1: every module element lies in the zeroth filtration stage. -/
theorem quasiRegularStage_zero_mem
    (rs : List R) (m : M) :
    m ∈ quasiRegularStage rs M 0 := by
  -- The stage `J^0 M` is just the whole module.
  simpa [quasiRegularStage, idealAssociatedGradedStage]

/-- Helper for 10.69.0.1: multiplying the stage `I^n M` by `I^d` shifts the filtration index by
`d`. -/
theorem idealAssociatedGradedStage_pow_smul_eq
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d n : ℕ) :
    ((I ^ d) • idealAssociatedGradedStage I M n : Submodule R M) =
      idealAssociatedGradedStage I M (n + d) := by
  -- Rewrite `I^d • (I^n M)` as `I^(d + n) M`, then commute the nat addition in the stage index.
  calc
    ((I ^ d) • idealAssociatedGradedStage I M n : Submodule R M)
        = ((I ^ d) • ((I ^ n) • (⊤ : Submodule R M)) : Submodule R M) := rfl
    _ = (((I ^ d) * (I ^ n)) • (⊤ : Submodule R M) : Submodule R M) := by
      rw [← mul_smul]
    _ = ((I ^ (d + n)) • (⊤ : Submodule R M) : Submodule R M) := by
      rw [← pow_add]
    _ = idealAssociatedGradedStage I M (n + d) := by
      simp [idealAssociatedGradedStage, Nat.add_comm]

/-- Helper for 10.69.0.1: multiplying the denominator `I(I^n M)` by `I^d` gives the denominator
inside the shifted stage `I^(n + d) M`. -/
theorem idealAssociatedGradedDenominator_pow_smul_eq
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d n : ℕ) :
    ((I ^ d) • (I • idealAssociatedGradedStage I M n) : Submodule R M) =
      I • idealAssociatedGradedStage I M (n + d) := by
  -- Commute the extra `I`-factor to the front and then reuse the stage-shift lemma.
  calc
    ((I ^ d) • (I • idealAssociatedGradedStage I M n) : Submodule R M)
        = (((I ^ d) * I) • idealAssociatedGradedStage I M n : Submodule R M) := by
            rw [← mul_smul]
    _ = ((I * I ^ d) • idealAssociatedGradedStage I M n : Submodule R M) := by
      rw [Ideal.mul_comm]
    _ = (I • ((I ^ d) • idealAssociatedGradedStage I M n) : Submodule R M) := by
      rw [mul_smul]
    _ = I • idealAssociatedGradedStage I M (n + d) := by
      rw [idealAssociatedGradedStage_pow_smul_eq]

/-- The internal quotient model of the degree-`n` piece is canonically identified with the
textbook quotient `J^n M / J^(n + 1) M`. -/
noncomputable def quasiRegularAssociatedGradedInternalPieceEquiv
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    quasiRegularAssociatedGradedInternalPiece rs M n ≃ₗ[R]
      idealAssociatedGradedPiece (quasiRegularIdeal rs) M n :=
  idealAssociatedGradedInternalPieceEquiv (quasiRegularIdeal rs) M n

noncomputable def quasiRegularAssociatedGradedAddEquiv
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] :
    idealAssociatedGradedModule (quasiRegularIdeal rs) M ≃+
      quasiRegularAssociatedGradedInternal rs M :=
  DirectSum.congrAddEquiv fun n ↦
    (quasiRegularAssociatedGradedInternalPieceEquiv rs M n).symm.toAddEquiv

end RingTheory.Sequence

end
