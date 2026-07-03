import StacksProject_2024.Chap10.Lemma_10_150_6.AssociatedGradedAPI

-- Proof rescue support for Lemma 10.106.1: quotient-Rees stage classes and the
-- degree-piece comparison `gr_I(R)_n ≃ I^n / I^(n + 1)`.

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.106.1: the degree-`n` monomial representative of a stage element belongs
to the Rees algebra. -/
private theorem ideal_associated_graded_stage_monomial_mem
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    Polynomial.monomial n (x : R) ∈ reesAlgebra I := by
  -- The stage hypothesis says exactly that the coefficient lies in `I ^ n`.
  refine reesAlgebra.monomial_mem.mpr ?_
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.106.1: the stage representative in degree `n` defines a class in the
quotient-Rees model of `gr_I(R)`. -/
def idealAssociatedGradedStageClass
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedRing I :=
  Ideal.Quotient.mk _ ⟨Polynomial.monomial n (x : R),
    ideal_associated_graded_stage_monomial_mem I n x⟩

/-- Helper for Lemma 10.106.1: the stage class of an `n`-stage representative lies in the degree
`n` owner piece of the associated graded ring. -/
theorem idealAssociatedGradedStageClass_mem_grade
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass I n x ∈ idealAssociatedGradedRingGrade I n := by
  -- The owner-grade witness is the same degree-`n` monomial used to define the stage class.
  refine ⟨⟨Polynomial.monomial n (x : R), ideal_associated_graded_stage_monomial_mem I n x⟩,
    ?_, rfl⟩
  refine ⟨⟨(x : R), ?_⟩, rfl⟩
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.106.1: multiplying representatives from stages `m` and `n` lands in the
stage `m + n`. -/
private theorem ideal_associated_graded_stage_mul_mem
    (I : Ideal R) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    ((x : R) * (y : R)) ∈ RingTheory.Sequence.idealAssociatedGradedStage I R (m + n) := by
  -- The adic filtration is multiplicative because `I ^ m * I ^ n = I ^ (m + n)`.
  have hx : (x : R) ∈ I ^ m := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  have hy : (y : R) ∈ I ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using y.2
  have hxy : (x : R) * (y : R) ∈ I ^ m * I ^ n := Ideal.mul_mem_mul hx hy
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
    pow_add] using hxy

/-- Helper for Lemma 10.106.1: multiplication in the quotient-Rees presentation is induced by
multiplication of stage representatives. -/
theorem idealAssociatedGradedStageClass_mul_local
    (I : Ideal R) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass I (m + n)
        ⟨(x : R) * (y : R), ideal_associated_graded_stage_mul_mem I x y⟩ =
      idealAssociatedGradedStageClass I m x * idealAssociatedGradedStageClass I n y := by
  -- Compare both sides on the explicit quotient classes of Rees monomials.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        (⟨Polynomial.monomial (m + n) ((x : R) * (y : R)), _⟩ : reesAlgebra I) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ((⟨Polynomial.monomial m (x : R), _⟩ : reesAlgebra I) *
          (⟨Polynomial.monomial n (y : R), _⟩ : reesAlgebra I))
  congr 1
  -- The Rees representatives agree as monomials with multiplied coefficients.
  apply Subtype.ext
  simp [Polynomial.monomial_mul_monomial]

/-- Helper for Lemma 10.106.1: the stage-to-Rees construction is linear before passing to the
quotient. -/
private noncomputable def idealAssociatedGradedStageToReesLinear
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] reesAlgebra I :=
  LinearMap.codRestrict (reesAlgebra I).toSubmodule
    ((Polynomial.monomial n).comp
      (show RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] R from
        (RingTheory.Sequence.idealAssociatedGradedStage I R n).subtype))
    (ideal_associated_graded_stage_monomial_mem I n)

/-- Helper for Lemma 10.106.1: the linear stage map to the owner ring lands in the degree-`n`
grade subtype. -/
private noncomputable def idealAssociatedGradedStageClassLinear
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] idealAssociatedGradedRingGrade I n :=
  LinearMap.codRestrict (idealAssociatedGradedRingGrade I n)
    (((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap).comp
      (idealAssociatedGradedStageToReesLinear I n))
    (idealAssociatedGradedStageClass_mem_grade I n)

/-- Helper for Lemma 10.106.1: forgetting the grade subtype identifies the linear stage map with
the explicit stage class. -/
private theorem idealAssociatedGradedStageClassLinear_apply
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    ((idealAssociatedGradedStageClassLinear I n x :
      idealAssociatedGradedRingGrade I n) : idealAssociatedGradedRing I) =
      idealAssociatedGradedStageClass I n x := by
  -- Both constructions are the same quotient class of the same degree-`n` monomial.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ((idealAssociatedGradedStageToReesLinear I n) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ⟨Polynomial.monomial n (x : R), ideal_associated_graded_stage_monomial_mem I n x⟩
  congr 1

/-- Helper for Lemma 10.106.1: taking the `n`-th coefficient sends the denominator ideal of the
quotient-Rees presentation into `I^(n + 1)`. -/
private theorem rees_algebra_coeff_mem_pow_succ_of_mem_denominator
    (I : Ideal R) (n : ℕ)
    {y : reesAlgebra I}
    (hy : y ∈ Ideal.map (algebraMap R (reesAlgebra I)) I) :
    y.1.coeff n ∈ I ^ (n + 1) := by
  have hy' : y ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    -- Rewrite the defining ideal as the ambient scalar multiple `I • ⊤`.
    simpa [Ideal.smul_top_eq_map] using hy
  -- Check the coefficient condition on generators and extend by additivity.
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr z hz
    have hzcoeff : z.1.coeff n ∈ I ^ n := z.2 n
    change (r • z.1).coeff n ∈ I ^ (n + 1)
    simpa [Polynomial.coeff_smul, smul_eq_mul, pow_succ', Ideal.mul_comm] using
      Ideal.mul_mem_mul hr hzcoeff
  · intro x y hx hy
    simpa [Polynomial.coeff_add] using Ideal.add_mem (I ^ (n + 1)) hx hy

/-- Helper for Lemma 10.106.1: a degree-`n` monomial with coefficient in `I^(n + 1)` already
lies in the quotient-Rees denominator ideal. -/
private theorem monomial_mem_denominator_of_mem_pow_succ
    (I : Ideal R) (n : ℕ) {a : R}
    (ha : a ∈ I ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
      reesAlgebra I) ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
  have hsmul :
      (⟨Polynomial.monomial n a,
          reesAlgebra.monomial_mem.mpr
            ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
        reesAlgebra I) ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    let x : reesAlgebra I :=
      ⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩
    let φ : R →ₗ[R] Polynomial R := Polynomial.monomial n
    have ha' : a ∈ I • (I ^ n : Submodule R R) := by
      -- This is the source identity `I * I^n = I^(n + 1)`.
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm] using ha
    let RI : Submodule R (Polynomial R) := Subalgebra.toSubmodule (reesAlgebra I)
    have hmap0 :
        (Submodule.map φ (I ^ n : Submodule R R) : Submodule R (Polynomial R)) ≤ RI := by
      intro p hp
      rcases hp with ⟨b, hb, rfl⟩
      exact reesAlgebra.monomial_mem.mpr hb
    have hmap :
        (Submodule.map φ (I • (I ^ n : Submodule R R)) : Submodule R (Polynomial R)) ≤
          (I • RI : Submodule R (Polynomial R)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.mpr ?_
      intro r hr p hp
      exact Submodule.smul_mem_smul hr (hmap0 hp)
    have hambient : (x : Polynomial R) ∈ I • RI := by
      have hxmap : φ a ∈ Submodule.map φ (I • (I ^ n : Submodule R R)) := by
        exact Submodule.mem_map_of_mem ha'
      exact hmap <| by simpa [φ, x] using hxmap
    exact (Submodule.mem_smul_top_iff (I := I) (N := RI) (x := x)).2 hambient
  simpa [Ideal.smul_top_eq_map] using hsmul

/-- Helper for Lemma 10.106.1: a stage class vanishes exactly when its representative already
lies in the next filtration step. -/
private theorem idealAssociatedGradedStageClass_zero_iff
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass I n x = 0 ↔
      (x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1) := by
  constructor
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
          ⟨Polynomial.monomial n (x : R), ideal_associated_graded_stage_monomial_mem I n x⟩ = 0
      at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    -- Vanishing in the quotient forces the coefficient into the next ideal power.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using rees_algebra_coeff_mem_pow_succ_of_mem_denominator I n hx
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
          ⟨Polynomial.monomial n (x : R), ideal_associated_graded_stage_monomial_mem I n x⟩ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hx' : (x : R) ∈ I ^ (n + 1) := by
      -- Re-express the next stage as the ideal power `I^(n + 1)`.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx
    simpa using monomial_mem_denominator_of_mem_pow_succ I n hx'

/-- Helper for Lemma 10.106.1: every degree-`n` owner class is represented by an `n`-stage
element. -/
private theorem idealAssociatedGradedStageClassLinear_surjective
    (I : Ideal R) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageClassLinear I n) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  rcases hy with ⟨a, rfl⟩
  refine ⟨⟨a.1, ?_⟩, ?_⟩
  · -- A homogeneous Rees generator of degree `n` is exactly an element of `I ^ n`.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  · -- The given owner class is already represented by that canonical stage element.
    exact Subtype.ext <| by
      simpa [idealAssociatedGradedStageClassLinear, idealAssociatedGradedStageToReesLinear] using hxy

/-- Helper for Lemma 10.106.1: the kernel of the stage-to-grade map is exactly the next
filtration step. -/
private theorem idealAssociatedGradedStageClassLinear_ker_eq
    (I : Ideal R) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageClassLinear I n) =
      (RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage I R n) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (((idealAssociatedGradedStageClassLinear I n x : idealAssociatedGradedRingGrade I n) :
            idealAssociatedGradedRing I)) = 0 := by
      exact congrArg (fun z : idealAssociatedGradedRingGrade I n ↦ (z : idealAssociatedGradedRing I)) hx
    -- Forgetting the grade subtype reduces kernel membership to vanishing of the stage class.
    change idealAssociatedGradedStageClass I n x = 0 at hx'
    exact (idealAssociatedGradedStageClass_zero_iff I n x).1 hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- The zero criterion identifies the next stage with the kernel.
    change idealAssociatedGradedStageClass I n x = 0
    exact (idealAssociatedGradedStageClass_zero_iff I n x).2 hx

/-- Helper for Lemma 10.106.1: the degree-`n` owner piece of `gr_I(R)` is canonically identified
with the textbook quotient `I^n / I^(n + 1)`. -/
noncomputable def idealAssociatedGradedRingGrade_equiv_piece
    (I : Ideal R) (n : ℕ) :
    idealAssociatedGradedRingGrade I n ≃ₗ[R] RingTheory.Sequence.idealAssociatedGradedPiece I R n :=
  ((idealAssociatedGradedStageClassLinear I n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageClassLinear_surjective I n)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageClassLinear_ker_eq I n))

/-- Helper for Lemma 10.106.1: the owner-grade/piece equivalence sends a stage class to the
corresponding quotient class modulo `I^(n + 1)`. -/
theorem idealAssociatedGradedRingGrade_equiv_piece_apply_stage
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedRingGrade_equiv_piece I n
      ⟨idealAssociatedGradedStageClass I n x, idealAssociatedGradedStageClass_mem_grade I n x⟩ =
        Submodule.Quotient.mk x := by
  have hlinear :
      idealAssociatedGradedStageClassLinear I n x =
        ⟨idealAssociatedGradedStageClass I n x, idealAssociatedGradedStageClass_mem_grade I n x⟩ := by
    apply Subtype.ext
    exact idealAssociatedGradedStageClassLinear_apply I n x
  -- Once the stage class is rewritten through the linear presentation, both quotient equivalences
  -- act trivially on the chosen representative.
  rw [← hlinear]
  simp [idealAssociatedGradedRingGrade_equiv_piece]

end
