import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_150_6.AssociatedGradedAPI
import stacks_proof.stacks_project.Chap10.Lemma_10_58_10
import stacks_proof.stacks_project.Chap10.Lemma_10_59_9
import stacks_proof.stacks_project.Chap10.Proposition_10_59_5.OwnerPackaging
import stacks_proof.stacks_project.Chap10.Proposition_10_60_9
import stacks_proof.stacks_project.Chap10.Lemma_10_106_1.Index
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.Tactic.StacksAttribute

-- Semantic search tool unavailable in this session; statement surface verified locally against
-- `IsRegularSystemOfParameters`, `idealAssociatedGradedRing`, and `idealAssociatedGradedDegreeOne`.

open Filter IsLocalRing
open scoped Ideal

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "κ" => ResidueField R
local notation "grR" => idealAssociatedGradedRing (maximalIdeal R)

/-- Helper for Lemma 10.106.1: expose the quotient-Rees commutative ring structure so local owner
grading proofs do not repeatedly unfold the quotient model. -/
local instance (I : Ideal R) : CommRing (idealAssociatedGradedRing I) := by
  infer_instance

/-- Helper for Lemma 10.106.1: expose the additive structure on a quotient-Rees associated graded
ring for direct-sum packaging. -/
local instance (I : Ideal R) : AddCommMonoid (idealAssociatedGradedRing I) := by
  infer_instance

/-- Helper for Lemma 10.106.1: expose the multiplicative structure on a quotient-Rees associated
graded ring for owner grading. -/
local instance (I : Ideal R) : Monoid (idealAssociatedGradedRing I) := by
  infer_instance

/-- Helper for Lemma 10.106.1: expose the base-ring module structure on a quotient-Rees
associated graded ring. -/
local instance (I : Ideal R) : Module R (idealAssociatedGradedRing I) := by
  infer_instance

/-- Helper for Lemma 10.106.1: expose the base-ring algebra structure on a quotient-Rees
associated graded ring. -/
local instance (I : Ideal R) : Algebra R (idealAssociatedGradedRing I) := by
  infer_instance

/-- Helper for Lemma 10.106.1: the owner pieces of a quotient-Rees associated graded ring form
an internally graded multiplicative family. -/
local instance (I : Ideal R) :
    SetLike.GradedMonoid (idealAssociatedGradedRingGrade (R := R) I) where
  one_mem := by
    -- The unit is represented by the Rees unit in degree zero.
    refine ⟨1, SetLike.one_mem_graded (reesAlgebraGrade I), rfl⟩
  mul_mem := by
    -- Multiplying homogeneous Rees representatives preserves the sum of their degrees.
    intro i j x y hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    exact ⟨x' * y', SetLike.mul_mem_graded hx' hy', rfl⟩

/-- Helper for Lemma 10.106.1: the public owner-packaging decomposition equips the associated
graded ring with its internal grading. -/
local instance (I : Ideal R) :
    GradedAlgebra (idealAssociatedGradedRingGrade (R := R) I) :=
  -- The decomposition maps are the quotient-Rees owner decomposition from Proposition 10.59.5.
  GradedAlgebra.ofAlgHom (idealAssociatedGradedRingGrade (R := R) I)
    (Ideal.idealAssociatedGradedRing_decomposeAlgHom (R := R) I)
    (Ideal.idealAssociatedGradedRing_decomposeAlgHom_right_inv (R := R) I)
    (Ideal.idealAssociatedGradedRing_decomposeAlgHom_left_inv (R := R) I)

local instance : CommRing grR :=
  inferInstanceAs (CommRing (idealAssociatedGradedRing (maximalIdeal R)))

local instance : Algebra κ grR :=
  inferInstance

local instance : SMul κ grR where
  smul c z := algebraMap κ grR c * z

local instance : Module κ grR := by
  let _ : Module grR grR := Semiring.toModule
  exact Module.compHom grR (algebraMap κ grR)

local instance (n : ℕ) :
    Module κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  exact inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n))

local instance (n : ℕ) :
    Module κ
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
  exact inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))))

local instance (n : ℕ) :
    IsScalarTower R κ
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
  exact inferInstanceAs
    (IsScalarTower R (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))))

/-- Helper for Lemma 10.106.1: each owner grade of `grR` inherits the ambient residue-field
scalar action. -/
local instance (n : ℕ) : SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Transport the residue-field scalar action from the textbook quotient piece through the
  -- canonical owner-grade/piece equivalence.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  show SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) from
    (e.toAddEquiv.module κ).toSMul

/-- Helper for Lemma 10.106.1: each owner grade of `grR` is a `κ`-module via the ambient scalar
action on `grR`. -/
local instance (n : ℕ) : Module κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Route correction: transport the module structure from the textbook quotient piece instead of
  -- rebuilding the stage-class action inside `grR`.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  e.toAddEquiv.module κ



/-- Helper for Lemma 10.106.1: each coefficient-bearing support monomial of a homogeneous
polynomial evaluates into the expected filtration stage of the maximal ideal. -/
private theorem homogeneous_parameter_monomial_mem_stage {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n)
    (e : Fin d →₀ ℕ) :
    p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈
      RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n := by
  by_cases he : e ∈ p.support
  · -- A support monomial of a homogeneous polynomial has the common total degree `n`.
    have hdegree : e.degree = n := by
      have hcoeff : p.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
      by_contra hne
      exact hcoeff (hp.coeff_eq_zero hne)
    have hsum_degree : (∑ i : Fin d, e i) = e.degree := by
      simpa using (Finsupp.degree_eq_sum e).symm
    have hprod :
        ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈ maximalIdeal R ^ e.degree := by
      -- The parameter monomial lands in the power indexed by its total degree.
      simpa [hsum_degree] using
        parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ
    have hmul :
        p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈ maximalIdeal R ^ e.degree :=
      Ideal.mul_mem_left _ _ hprod
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
      hdegree] using hmul
  · -- Outside the support, the coefficient is zero, so the evaluated monomial is zero.
    have hcoeff : p.coeff e = 0 := MvPolynomial.notMem_support_iff.mp he
    simp [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.mul_top, hcoeff]

/-- Helper for Lemma 10.106.1: the support sum of a homogeneous polynomial in the chosen
parameters defines an element of the `n`-th stage of the maximal-ideal filtration. -/
private noncomputable def homogeneous_parameter_support_stage {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n) :
    RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
  ⟨Finset.sum p.support (fun e ↦ p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i)),
    by
      let a : (Fin d →₀ ℕ) →
          RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
        fun e ↦
          ⟨p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
            homogeneous_parameter_monomial_mem_stage (R := R) x hp e⟩
      simpa [a] using idealAssociatedGradedStage_finset_sum_mem (R := R) p.support a⟩

/-- Helper for Lemma 10.106.1: evaluating a homogeneous polynomial in the chosen parameters lands
in the stage indexed by its degree. -/
private theorem homogeneous_parameter_eval_eq_support_stage {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n) :
    p.eval (fun i ↦ ((x i : maximalIdeal R) : R)) =
      (homogeneous_parameter_support_stage (R := R) x hp : R) := by
  -- Route correction: the support-stage object was defined to be exactly the `MvPolynomial.eval_eq'`
  -- expansion specialized to the chosen parameters.
  simpa [homogeneous_parameter_support_stage, MvPolynomial.eval_eq'] using
    (MvPolynomial.eval_eq' (X := fun i ↦ ((x i : maximalIdeal R) : R)) p)

/-- Helper for Lemma 10.106.1: evaluating a homogeneous polynomial in the chosen parameters lands
in the stage indexed by its degree. -/
private theorem homogeneous_parameter_eval_mem_stage {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n) :
    p.eval (fun i ↦ ((x i : maximalIdeal R) : R)) ∈
      RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n := by
  let supportStage := homogeneous_parameter_support_stage (R := R) x hp
  have heval :
      p.eval (fun i ↦ ((x i : maximalIdeal R) : R)) = (supportStage : R) :=
    homogeneous_parameter_eval_eq_support_stage (R := R) x hp
  simpa [heval] using supportStage.2

/-- Helper for Lemma 10.106.1: a homogeneous polynomial maps to the stage class of the support sum
obtained by evaluating each support monomial in the chosen parameters. -/
theorem associatedGradedPresentation_homogeneous_support_sum_eq_stageClass {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n) :
    associatedGradedPresentation x (p.map (Ideal.Quotient.mk (maximalIdeal R))) =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        (homogeneous_parameter_support_stage (R := R) x hp) := by
  classical
  let a : (Fin d →₀ ℕ) → RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
    fun e ↦
      ⟨p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
        homogeneous_parameter_monomial_mem_stage (R := R) x hp e⟩
  have hp_expand :
      p.map (Ideal.Quotient.mk (maximalIdeal R)) =
        ∑ e ∈ p.support,
          MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
            (MvPolynomial.monomial e (p.coeff e)) := by
    calc
      p.map (Ideal.Quotient.mk (maximalIdeal R)) =
        MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
          (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) := by
            rw [← MvPolynomial.as_sum p]
      _ =
        ∑ e ∈ p.support,
          MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
            (MvPolynomial.monomial e (p.coeff e)) := by
              rw [map_sum]
  have hpresentation_sum :
      associatedGradedPresentation x
          (∑ e ∈ p.support,
            MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
              (MvPolynomial.monomial e (p.coeff e))) =
        ∑ e ∈ p.support,
          associatedGradedPresentation x
            (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
              (MvPolynomial.monomial e (p.coeff e))) := by
    -- Distribute the algebra hom over the finite support sum explicitly.
    induction p.support using Finset.induction_on with
    | empty =>
        simp
    | @insert e s he ih =>
        simp [Finset.sum_insert, he, map_add]
  -- Expand `p` into its support sum and rewrite each support monomial by the already-proved
  -- monomial-to-stage-class formula.
  calc
    associatedGradedPresentation x (p.map (Ideal.Quotient.mk (maximalIdeal R))) =
      ∑ e ∈ p.support,
        associatedGradedPresentation x
          (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
            (MvPolynomial.monomial e (p.coeff e))) := by
          rw [hp_expand]
          exact hpresentation_sum
    _ =
      ∑ e ∈ p.support, idealAssociatedGradedStageClass (maximalIdeal R) n (a e) := by
        refine Finset.sum_congr rfl ?_
        intro e hmem
        have hdegree : e.degree = n := by
          have hcoeff : p.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp hmem
          exact by
            by_contra hne
            exact hcoeff (hp.coeff_eq_zero hne)
        have hsum : (∑ i : Fin d, e i) = n := by
          calc
            ∑ i : Fin d, e i = e.degree := (Finsupp.degree_eq_sum e).symm
            _ = n := hdegree
        -- Support monomials of a homogeneous polynomial all have the common total degree `n`.
        calc
          associatedGradedPresentation x
              (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
                (MvPolynomial.monomial e (p.coeff e))) =
            idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i)
              ⟨p.coeff e * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
                by
                  have hprod :
                      ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈
                        maximalIdeal R ^ (∑ i : Fin d, e i) := by
                    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                      Ideal.mul_top] using
                        parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e
                          Finset.univ
                  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                    Ideal.mul_top] using
                    Ideal.mul_mem_left (maximalIdeal R ^ (∑ i : Fin d, e i)) (p.coeff e) hprod⟩ := by
              exact associatedGradedPresentation_monomial_map_eq_stageClass (R := R) x e (p.coeff e)
          _ = idealAssociatedGradedStageClass (maximalIdeal R) n (a e) := by
              cases hsum
              rfl
    _ =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        (homogeneous_parameter_support_stage (R := R) x hp) := by
          -- Collapse the support sum back to the stage representative used in the definition.
          simpa [homogeneous_parameter_support_stage, a] using
            idealAssociatedGradedStageClass_finset_sum_same_degree (R := R) p.support a

/-- Helper for Lemma 10.106.1: evaluating a homogeneous polynomial in the chosen parameters gives
the corresponding stage class in the associated graded ring. -/
theorem associatedGradedPresentation_homogeneous_eval_eq_stageClass {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) R} (hp : p.IsHomogeneous n) :
    associatedGradedPresentation x (p.map (Ideal.Quotient.mk (maximalIdeal R))) =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨p.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hp⟩ := by
  -- Replace the support-sum representative by the actual polynomial evaluation using the direct
  -- `MvPolynomial.eval_eq'` normal form.
  rw [associatedGradedPresentation_homogeneous_support_sum_eq_stageClass (R := R) x hp]
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial n ((homogeneous_parameter_support_stage (R := R) x hp : R)), _⟩ :
          reesAlgebra (maximalIdeal R)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial n (p.eval fun i ↦ ((x i : maximalIdeal R) : R)), _⟩ :
          reesAlgebra (maximalIdeal R))
  congr 1
  apply Subtype.ext
  simp [homogeneous_parameter_eval_eq_support_stage (R := R) x hp]

/-- Helper for Lemma 10.106.1: every homogeneous polynomial over the residue field lifts to a
homogeneous polynomial over `R` with the same image modulo the maximal ideal. -/
private theorem exists_homogeneous_polynomial_lift {d n : ℕ}
    (p : MvPolynomial (Fin d) κ) (hp : p.IsHomogeneous n) :
    ∃ q : MvPolynomial (Fin d) R,
      q.IsHomogeneous n ∧
        q.map (Ideal.Quotient.mk (maximalIdeal R)) = p := by
  classical
  let liftCoeff : (Fin d →₀ ℕ) → R :=
    fun e ↦ Classical.choose (Ideal.Quotient.mk_surjective (p.coeff e))
  have hliftCoeff : ∀ e : Fin d →₀ ℕ,
      (Ideal.Quotient.mk (maximalIdeal R)) (liftCoeff e) = p.coeff e := by
    intro e
    exact Classical.choose_spec (Ideal.Quotient.mk_surjective (p.coeff e))
  let q : MvPolynomial (Fin d) R :=
    ∑ e ∈ p.support, MvPolynomial.monomial e (liftCoeff e)
  refine ⟨q, ?_, ?_⟩
  · -- Each support monomial of `p` has total degree `n`, so the chosen lift stays homogeneous.
    dsimp [q]
    apply MvPolynomial.IsHomogeneous.sum
    intro e he
    have hdeg : e.degree = n := by
      have hcoeff : p.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
      by_contra hne
      exact hcoeff (hp.coeff_eq_zero hne)
    simpa [hdeg] using
      (MvPolynomial.isHomogeneous_monomial (R := R) (d := e) (r := liftCoeff e) hdeg)
  · -- Mapping the chosen coefficient lifts back to `κ` recovers the original support expansion.
    calc
      q.map (Ideal.Quotient.mk (maximalIdeal R)) =
          ∑ e ∈ p.support,
            MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))
              (MvPolynomial.monomial e (liftCoeff e)) := by
            simp [q]
      _ = ∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            rw [MvPolynomial.map_monomial, hliftCoeff]
            rfl
      _ = p := by
            rw [← MvPolynomial.as_sum p]

/-- Helper for Lemma 10.106.1: a homogeneous residue-field polynomial maps into the matching owner
grade of the associated graded ring. -/
private theorem associatedGradedPresentation_mem_grade_of_homogeneous {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) κ} (hp : p.IsHomogeneous n) :
    associatedGradedPresentation x p ∈ idealAssociatedGradedRingGrade (maximalIdeal R) n := by
  obtain ⟨q, hq_hom, hq_map⟩ :=
    exists_homogeneous_polynomial_lift (R := R) (n := n) p hp
  rw [← hq_map]
  -- The explicit stage-class formula from the lifted homogeneous polynomial lands in grade `n`.
  simpa [associatedGradedPresentation_homogeneous_eval_eq_stageClass (R := R) x hq_hom] using
    idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n
      ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
        homogeneous_parameter_eval_mem_stage (R := R) x hq_hom⟩

/-- Helper for Lemma 10.106.1: the degree-`n` part of the polynomial presentation lands in the
degree-`n` owner piece of the associated graded ring. -/
private theorem associatedGradedPresentation_on_homogeneousSubmodule_mem_grade {d n : ℕ}
    (x : Fin d → maximalIdeal R)
    (p : MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
    associatedGradedPresentation x (p : MvPolynomial (Fin d) κ) ∈
      idealAssociatedGradedRingGrade (maximalIdeal R) n := by
  have hp : (p : MvPolynomial (Fin d) κ).IsHomogeneous n := by
    exact (MvPolynomial.mem_homogeneousSubmodule n (p : MvPolynomial (Fin d) κ)).1 p.2
  -- Forget the subtype proof and apply the homogeneous owner-grade bridge.
  simpa using associatedGradedPresentation_mem_grade_of_homogeneous (R := R) x hp

/-- Helper for Lemma 10.106.1: every stage class in the quotient-Rees model lies in the range of
the polynomial presentation attached to a regular system of parameters. -/
theorem associatedGradedPresentation_stageClass_mem_range {d n : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedStageClass (maximalIdeal R) n a ∈ Set.range (associatedGradedPresentation x) := by
  have ha : (a : R) ∈ maximalIdeal R ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  rcases exists_isHomogeneous_polynomial_eval_eq_of_mem_maximalIdeal_pow (R := R) (x := x) hx ha with
    ⟨p, hp, hEval⟩
  refine ⟨p.map (Ideal.Quotient.mk (maximalIdeal R)), ?_⟩
  calc
    associatedGradedPresentation x (p.map (Ideal.Quotient.mk (maximalIdeal R))) =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨p.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hp⟩ := by
            exact associatedGradedPresentation_homogeneous_eval_eq_stageClass (R := R) x hp
    _ = idealAssociatedGradedStageClass (maximalIdeal R) n a := by
      -- The stage class only depends on the represented element modulo the next filtration step,
      -- so the evaluation witness can be replaced by the target representative.
      change
        Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (⟨Polynomial.monomial n (p.eval fun i ↦ ((x i : maximalIdeal R) : R)), _⟩ :
              reesAlgebra (maximalIdeal R)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (⟨Polynomial.monomial n (a : R), _⟩ : reesAlgebra (maximalIdeal R))
      congr 1
      apply Subtype.ext
      simp [hEval]

/-- Helper for Lemma 10.106.1: the `n`-th coefficient of a Rees-algebra element defines the
corresponding `n`-stage representative of the maximal-ideal filtration. -/
private theorem rees_coefficient_mem_stage (y : reesAlgebra (maximalIdeal R)) (n : ℕ) :
    y.1.coeff n ∈ RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n := by
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using y.2 n

/-- Helper for Lemma 10.106.1: the `n`-th coefficient of a Rees-algebra element defines the
corresponding `n`-stage representative of the maximal-ideal filtration. -/
private noncomputable def rees_coefficient_stage (y : reesAlgebra (maximalIdeal R)) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
  ⟨y.1.coeff n, rees_coefficient_mem_stage (R := R) y n⟩

/-- Helper for Lemma 10.106.1: every quotient-Rees class is the finite sum of the stage classes of
its polynomial coefficients. -/
theorem idealAssociatedGradedClass_eq_sum_stage_classes_local
    (y : reesAlgebra (maximalIdeal R)) :
    (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
      y : grR) =
      Finset.sum y.1.support
        (fun n ↦ idealAssociatedGradedStageClass (maximalIdeal R) n
          (rees_coefficient_stage (R := R) y n)) := by
  classical
  let J : Ideal (reesAlgebra (maximalIdeal R)) :=
    Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R)
  let q : reesAlgebra (maximalIdeal R) →ₐ[R] grR := Ideal.Quotient.mkₐ R J
  let c : ℕ → reesAlgebra (maximalIdeal R) :=
    fun n ↦
      ⟨Polynomial.monomial n (y.1.coeff n),
        reesAlgebra.monomial_mem.mpr (y.2 n)⟩
  have hy_sum : y = ∑ n ∈ y.1.support, c n := by
    -- Expand the Rees representative as the finite sum of its coefficient monomials.
    apply Subtype.ext
    simpa [Polynomial.sum, c] using (Polynomial.sum_monomial_eq y.1).symm
  have hq_sum :
      q (∑ n ∈ y.1.support, c n) =
        ∑ n ∈ y.1.support, q (c n) := by
    -- Distribute the quotient map over the finite sum of coefficient monomials.
    simpa using q.map_sum (fun n ↦ c n) y.1.support
  calc
    (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
      y : grR) =
      q y := by
        rfl
    _ =
      q (∑ n ∈ y.1.support, c n) := by
          simpa using congrArg q hy_sum
    _ =
      ∑ n ∈ y.1.support,
        q (c n) := by
          exact hq_sum
    _ =
      Finset.sum y.1.support
        (fun n ↦ idealAssociatedGradedStageClass (maximalIdeal R) n
          (rees_coefficient_stage (R := R) y n)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rfl

/-- Helper for Lemma 10.106.1: the canonical polynomial presentation attached to a regular system
of parameters is surjective onto the associated graded ring. -/
theorem associatedGradedPresentation_surjective {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    Function.Surjective (associatedGradedPresentation x) := by
  classical
  intro z
  rcases Ideal.Quotient.mk_surjective z with ⟨y, rfl⟩
  have hstage :
      ∀ n : ℕ, ∃ q : MvPolynomial (Fin d) κ,
        associatedGradedPresentation x q =
          idealAssociatedGradedStageClass (maximalIdeal R) n
            (rees_coefficient_stage (R := R) y n) := by
    intro n
    simpa [Set.mem_range] using
      associatedGradedPresentation_stageClass_mem_range (R := R) x hx
        (rees_coefficient_stage (R := R) y n)
  choose q hq using hstage
  have hpresentation_sum :
      associatedGradedPresentation x (∑ n ∈ y.1.support, q n) =
        ∑ n ∈ y.1.support, associatedGradedPresentation x (q n) := by
    -- Distribute the polynomial presentation over the chosen finite sum of preimages.
    induction y.1.support using Finset.induction_on with
    | empty =>
        simp
    | @insert n s hn ih =>
        simp [Finset.sum_insert, hn, map_add, ih]
  refine ⟨∑ n ∈ y.1.support, q n, ?_⟩
  calc
    associatedGradedPresentation x (∑ n ∈ y.1.support, q n) =
      ∑ n ∈ y.1.support, associatedGradedPresentation x (q n) := by
        exact hpresentation_sum
    _ =
      ∑ n ∈ y.1.support,
        idealAssociatedGradedStageClass (maximalIdeal R) n
          (rees_coefficient_stage (R := R) y n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact hq n
    _ =
      (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        y : grR) := by
          symm
          exact idealAssociatedGradedClass_eq_sum_stage_classes_local (R := R) y

/-- Helper for Lemma 10.106.1: multiplying a degree-`n` stage class by a degree-zero residue-field
coefficient just multiplies the chosen stage representative. -/
private theorem idealAssociatedGradedStageClass_constant_mul {n : ℕ}
    (r : R) (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) *
        idealAssociatedGradedStageClass (maximalIdeal R) n a =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨r * (a : R), by
          have ha_mem : (a : R) ∈ maximalIdeal R ^ n := by
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
              using a.2
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.mul_mem_left (maximalIdeal R ^ n) r ha_mem⟩ := by
  let r0 : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R 0 :=
    ⟨r, by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]⟩
  let ra : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
    ⟨r * (a : R), by
      have ha_mem : (a : R) ∈ maximalIdeal R ^ n := by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using a.2
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using Ideal.mul_mem_left (maximalIdeal R ^ n) r ha_mem⟩
  have hmul :
      idealAssociatedGradedStageClass (maximalIdeal R) (0 + n)
          ⟨(r0 : R) * (a : R), by
            have ha_mem : (a : R) ∈ maximalIdeal R ^ n := by
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using a.2
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using
              Ideal.mul_mem_left (maximalIdeal R ^ n) (r0 : R) ha_mem⟩ =
        idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 *
          idealAssociatedGradedStageClass (maximalIdeal R) n a := by
    -- Multiply the degree-zero coefficient class with the chosen stage representative.
    simpa [r0] using idealAssociatedGradedStageClass_mul_local (maximalIdeal R) r0 a
  calc
    algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) *
        idealAssociatedGradedStageClass (maximalIdeal R) n a =
      idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 *
        idealAssociatedGradedStageClass (maximalIdeal R) n a := by
          rw [associatedGradedPresentation_constant_map_eq_stageClass_zero]
    _ =
      idealAssociatedGradedStageClass (maximalIdeal R) (0 + n)
        ⟨(r0 : R) * (a : R), by
          have ha_mem : (a : R) ∈ maximalIdeal R ^ n := by
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using a.2
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
            Ideal.mul_top] using
            Ideal.mul_mem_left (maximalIdeal R ^ n) (r0 : R) ha_mem⟩ := by
          symm
          exact hmul
    _ = idealAssociatedGradedStageClass (maximalIdeal R) n ra := by
          simpa [ra, r0] using idealAssociatedGradedStageClass_zero_add (R := R) ra

/-- Helper for Lemma 10.106.1: after coercing an owner-grade element back to `grR`, the
transported residue-field scalar action agrees with ambient multiplication in `grR`. -/
private theorem idealAssociatedGradedRingGrade_eq_stageClass_local (n : ℕ)
    (y : idealAssociatedGradedRingGrade (maximalIdeal R) n) :
    ∃ a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n,
      y =
        ⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ := by
  let e := idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
  let N :
      Submodule R
        (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :=
    ((RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (n + 1)).submoduleOf
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n))
  rcases Submodule.Quotient.mk_surjective N (e y) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  -- Represent the owner-grade element by a stage class through the textbook quotient piece.
  apply e.injective
  rw [idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear_apply_stage]
  exact ha.symm

/-- Helper for Lemma 10.106.1: after coercing an owner-grade element back to `grR`, the
transported residue-field scalar action agrees with ambient multiplication in `grR`. -/
private theorem idealAssociatedGradedPiece_residue_smul_mk (n : ℕ)
    (r : R) (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    ((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      Submodule.Quotient.mk (r • a) := by
  let e := idealAssociatedGradedPiece_internal_quotient_equiv_quotient (R := R) n
  -- First rewrite the textbook quotient piece through the intrinsic quotient by
  -- `(maximalIdeal R) • ⊤`, where `Module.Quotient.mk_smul_mk` applies directly.
  calc
    ((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      ((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
        e (Submodule.Quotient.mk a) := by
          rw [idealAssociatedGradedPiece_internal_quotient_equiv_quotient_apply_stage (R := R)]
    _ =
      e (((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
            ((maximalIdeal R) •
              (⊤ : Submodule R
                (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n))))) := by
          symm
          exact e.map_smul _ _
    _ =
      e (Submodule.Quotient.mk (r • a) :
        RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
          ((maximalIdeal R) •
            (⊤ : Submodule R
              (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
          have hsmul_mk :
              (((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
                  (Submodule.Quotient.mk a :
                    RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                      ((maximalIdeal R) •
                        (⊤ : Submodule R
                          (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n))))) =
                Submodule.Quotient.mk (r • a) := by
            -- In the intrinsic quotient model, the residue-field scalar action is literally the
            -- scalar action on stage representatives.
            simpa using
              (Module.Quotient.mk_smul_mk
                (I := maximalIdeal R) (r := r) (m := a)).symm
          rw [hsmul_mk]
    _ =
      (Submodule.Quotient.mk (r • a) :
        RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
          exact idealAssociatedGradedPiece_internal_quotient_equiv_quotient_apply_stage
            (R := R) n (r • a)

/-- Helper for Lemma 10.106.1: after coercing an owner-grade element back to `grR`, the
transported residue-field scalar action agrees with ambient multiplication in `grR`. -/
private theorem idealAssociatedGradedRingGrade_smul_coe_local (n : ℕ) (c : κ)
    (y : idealAssociatedGradedRingGrade (maximalIdeal R) n) :
    ((c • y : idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) =
      algebraMap κ grR c * (y : grR) := by
  rcases Ideal.Quotient.mk_surjective c with ⟨r, rfl⟩
  rcases idealAssociatedGradedRingGrade_eq_stageClass_local (R := R) n y with ⟨a, rfl⟩
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  let ra : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n := r • a
  have hsymm :
      e.toAddEquiv.symm
          (Submodule.Quotient.mk (r • a :
            RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
            RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        (⟨idealAssociatedGradedStageClass (maximalIdeal R) n ra,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n ra⟩ :
          idealAssociatedGradedRingGrade (maximalIdeal R) n) := by
    -- The inverse comparison sends the quotient class of a stage representative back to its
    -- owner-grade stage class.
    apply e.toAddEquiv.injective
    rw [AddEquiv.apply_symm_apply]
    exact (idealAssociatedGradedRingGrade_equiv_piece_apply_stage
      (R := R) (I := maximalIdeal R) n ra).symm
  have hpiece :
      (((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
          (Submodule.Quotient.mk a :
            RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)) =
        Submodule.Quotient.mk (r • a :
          RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :=
    idealAssociatedGradedPiece_residue_smul_mk (R := R) n r a
  have hstagePiece :
      e.toAddEquiv.toEquiv
          (⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
            idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ :
            idealAssociatedGradedRingGrade (maximalIdeal R) n) =
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    idealAssociatedGradedRingGrade_equiv_piece_apply_stage
      (R := R) (I := maximalIdeal R) n a
  -- Unfold the transported scalar action once, compute it in the textbook quotient piece, and
  -- return through the inverse comparison.
  rw [Equiv.smul_def]
  change
    ((e.toAddEquiv.symm
        (((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
          e.toAddEquiv.toEquiv
            (⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
              idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ :
              idealAssociatedGradedRingGrade (maximalIdeal R) n)) :
        idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) =
      algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) *
        ((⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ :
          idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR)
  rw [hstagePiece]
  calc
    ((e.toAddEquiv.symm
        (((Ideal.Quotient.mk (maximalIdeal R)) r : κ) •
          (Submodule.Quotient.mk a :
            RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)) :
        idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) =
      ((e.toAddEquiv.symm
        (Submodule.Quotient.mk (r • a :
          RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :
        idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) := by
        exact congrArg
          (fun z : RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n ↦
            ((e.toAddEquiv.symm z : idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR))
          hpiece
    _ =
      ((⟨idealAssociatedGradedStageClass (maximalIdeal R) n ra,
        idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n ra⟩ :
        idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) := by
        rw [hsymm]
    _ =
      algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) *
        ((⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ :
          idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) := by
        simpa [ra, smul_eq_mul] using
          (idealAssociatedGradedStageClass_constant_mul (R := R) r a).symm

/-- Helper for Lemma 10.106.1: the explicit degree-`n` codomain lift preserves addition on the
homogeneous polynomial piece. -/
private theorem associatedGradedPresentation_degree_piece_to_grade_map_add {d n : ℕ}
    (x : Fin d → maximalIdeal R)
    (p q : MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
    (⟨associatedGradedPresentation x ((p + q : MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
        MvPolynomial (Fin d) κ),
      associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x (p + q)⟩ :
      idealAssociatedGradedRingGrade (maximalIdeal R) n) =
      ⟨associatedGradedPresentation x (p : MvPolynomial (Fin d) κ),
        associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x p⟩ +
        ⟨associatedGradedPresentation x (q : MvPolynomial (Fin d) κ),
          associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x q⟩ := by
  -- The subtype lift is additive because the underlying presentation map is additive.
  apply Subtype.ext
  simp

/-- Helper for Lemma 10.106.1: the explicit degree-`n` codomain lift preserves residue-field
scalar multiplication on the homogeneous polynomial piece. -/
private theorem associatedGradedPresentation_degree_piece_to_grade_map_smul {d n : ℕ}
    (x : Fin d → maximalIdeal R) (c : κ)
    (p : MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
    (⟨associatedGradedPresentation x ((c • p : MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
        MvPolynomial (Fin d) κ),
      associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x (c • p)⟩ :
      idealAssociatedGradedRingGrade (maximalIdeal R) n) =
      c • ⟨associatedGradedPresentation x (p : MvPolynomial (Fin d) κ),
        associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x p⟩ := by
  -- The owner-grade scalar action agrees with ambient multiplication after coercing back to `grR`.
  apply Subtype.ext
  rw [idealAssociatedGradedRingGrade_smul_coe_local (R := R)]
  change
    associatedGradedPresentation x (c • (p : MvPolynomial (Fin d) κ)) =
      algebraMap κ grR c * associatedGradedPresentation x (p : MvPolynomial (Fin d) κ)
  calc
    associatedGradedPresentation x (c • (p : MvPolynomial (Fin d) κ)) =
      associatedGradedPresentation x ((algebraMap κ (MvPolynomial (Fin d) κ)) c *
        (p : MvPolynomial (Fin d) κ)) := by
          rw [Algebra.smul_def]
    _ =
      associatedGradedPresentation x (MvPolynomial.C c) *
        associatedGradedPresentation x (p : MvPolynomial (Fin d) κ) := by
          rw [show (algebraMap κ (MvPolynomial (Fin d) κ)) c = MvPolynomial.C c by rfl, map_mul]
    _ =
      algebraMap κ grR c * associatedGradedPresentation x (p : MvPolynomial (Fin d) κ) := by
          rw [show associatedGradedPresentation x (MvPolynomial.C c) = algebraMap κ grR c by
            simp [associatedGradedPresentation]]

/-- Helper for Lemma 10.106.1: restricting the polynomial presentation to homogeneous degree `n`
lands in the owner grade `grR_n`. -/
private noncomputable def associatedGradedPresentation_degree_piece_to_grade {d : ℕ}
    (x : Fin d → maximalIdeal R) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin d) κ n →ₗ[κ]
      idealAssociatedGradedRingGrade (maximalIdeal R) n :=
  { toFun := fun p ↦
      ⟨associatedGradedPresentation x (p : MvPolynomial (Fin d) κ),
        associatedGradedPresentation_on_homogeneousSubmodule_mem_grade (R := R) x p⟩
    map_add' := associatedGradedPresentation_degree_piece_to_grade_map_add (R := R) x
    map_smul' := associatedGradedPresentation_degree_piece_to_grade_map_smul (R := R) x }

/-- Helper for Lemma 10.106.1: the degree-`n` polynomial presentation can be read directly in the
textbook quotient `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
private noncomputable def associatedGradedPresentation_degree_piece_map {d : ℕ}
    (x : Fin d → maximalIdeal R) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin d) κ n →ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  (idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n).toLinearMap.comp
    (associatedGradedPresentation_degree_piece_to_grade (R := R) x n)

/-- Helper for Lemma 10.106.1: a homogeneous polynomial over `R` defines the corresponding
homogeneous source element over the residue field. -/
private noncomputable def homogeneousPolynomialResidueFieldLift {d n : ℕ}
    (q : MvPolynomial (Fin d) R) (hq : q.IsHomogeneous n) :
    MvPolynomial.homogeneousSubmodule (Fin d) κ n :=
  ⟨q.map (Ideal.Quotient.mk (maximalIdeal R)),
    (MvPolynomial.mem_homogeneousSubmodule n
      (q.map (Ideal.Quotient.mk (maximalIdeal R)))).2
      (hq.map (Ideal.Quotient.mk (maximalIdeal R)))⟩

/-- Helper for Lemma 10.106.1: on a homogeneous lift, the degree-`n` presentation is exactly the
textbook quotient class of the parameter evaluation. -/
theorem associatedGradedPresentation_degree_piece_map_apply_stage {d n : ℕ}
    (x : Fin d → maximalIdeal R) {q : MvPolynomial (Fin d) R} (hq : q.IsHomogeneous n) :
    associatedGradedPresentation_degree_piece_map (R := R) x n
        (homogeneousPolynomialResidueFieldLift (R := R) (n := n) q hq) =
      Submodule.Quotient.mk
        ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hq⟩ := by
  -- Evaluate the degree piece through the homogeneous stage-class formula, then pass from the
  -- owner grade to the textbook quotient piece.
  have htoGrade :
      associatedGradedPresentation_degree_piece_to_grade (R := R) x n
          (homogeneousPolynomialResidueFieldLift (R := R) (n := n) q hq) =
        ⟨idealAssociatedGradedStageClass (maximalIdeal R) n
            ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
              homogeneous_parameter_eval_mem_stage (R := R) x hq⟩,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n
            ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
              homogeneous_parameter_eval_mem_stage (R := R) x hq⟩⟩ := by
    apply Subtype.ext
    simpa [associatedGradedPresentation_degree_piece_to_grade,
      homogeneousPolynomialResidueFieldLift] using
      associatedGradedPresentation_homogeneous_eval_eq_stageClass (R := R) x hq
  rw [associatedGradedPresentation_degree_piece_map]
  change
    idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
        (associatedGradedPresentation_degree_piece_to_grade (R := R) x n
          (homogeneousPolynomialResidueFieldLift (R := R) (n := n) q hq)) =
      Submodule.Quotient.mk
        ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hq⟩
  rw [htoGrade]
  exact
    idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear_apply_stage (R := R) n
      ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
        homogeneous_parameter_eval_mem_stage (R := R) x hq⟩

/-- Helper for Lemma 10.106.1: every degree-`n` quotient class of
`maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)` is represented by a degree-`n` homogeneous
polynomial in the chosen regular system of parameters. -/
theorem associatedGradedPresentation_degree_piece_surjective {d n : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    Function.Surjective (associatedGradedPresentation_degree_piece_map (R := R) x n) := by
  intro a
  rcases Submodule.Quotient.mk_surjective
      ((RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)) a with ⟨b, rfl⟩
  have hb : (b : R) ∈ maximalIdeal R ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using b.2
  rcases exists_isHomogeneous_polynomial_eval_eq_of_mem_maximalIdeal_pow
      (R := R) (x := x) hx hb with ⟨q, hq, hq_eval⟩
  refine ⟨homogeneousPolynomialResidueFieldLift (R := R) (n := n) q hq, ?_⟩
  have hstage :
      (⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hq⟩ :
        RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) = b := by
    -- The quotient class depends only on the represented stage element, and here the
    -- homogeneous lift evaluates to the chosen representative exactly.
    apply Subtype.ext
    exact hq_eval
  calc
    associatedGradedPresentation_degree_piece_map (R := R) x n
        (homogeneousPolynomialResidueFieldLift (R := R) (n := n) q hq) =
      Submodule.Quotient.mk
        ⟨q.eval (fun i ↦ ((x i : maximalIdeal R) : R)),
          homogeneous_parameter_eval_mem_stage (R := R) x hq⟩ := by
            exact associatedGradedPresentation_degree_piece_map_apply_stage (R := R) x hq
    _ = Submodule.Quotient.mk b := by
          simpa [hstage]

/-- Helper for Lemma 10.106.1: the kernel of the degree-`n` presentation is exactly the degree-`n`
part of the algebra kernel of `associatedGradedPresentation x`. -/
theorem associatedGradedPresentation_degree_piece_kernel_eq {d n : ℕ}
    (x : Fin d → maximalIdeal R) :
    LinearMap.ker (associatedGradedPresentation_degree_piece_map (R := R) x n) =
      Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin d) κ n).subtype
        ((RingHom.ker (associatedGradedPresentation x).toRingHom).restrictScalars κ) := by
  ext p
  constructor
  · intro hp
    rw [LinearMap.mem_ker] at hp
    let e := idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
    have hp_grade :
        associatedGradedPresentation_degree_piece_to_grade (R := R) x n p = 0 := by
      change
        e
            (associatedGradedPresentation_degree_piece_to_grade (R := R) x n p) = 0 at hp
      have hp' : e (associatedGradedPresentation_degree_piece_to_grade (R := R) x n p) = e 0 := by
        exact hp.trans e.map_zero.symm
      exact e.injective hp'
    -- Forgetting the owner-grade subtype turns the kernel statement back into vanishing in `grR`.
    change associatedGradedPresentation x (p : MvPolynomial (Fin d) κ) = 0
    have hp_underlying :
        ((associatedGradedPresentation_degree_piece_to_grade (R := R) x n p :
          idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) = 0 := by
      exact congrArg
        (fun z : idealAssociatedGradedRingGrade (maximalIdeal R) n ↦ (z : grR))
        hp_grade
    change
      ((associatedGradedPresentation_degree_piece_to_grade (R := R) x n p :
        idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) = 0
    exact hp_underlying
  · intro hp
    change associatedGradedPresentation x (p : MvPolynomial (Fin d) κ) = 0 at hp
    rw [LinearMap.mem_ker]
    have hp_grade :
        associatedGradedPresentation_degree_piece_to_grade (R := R) x n p = 0 := by
      -- The cod-restricted degree piece vanishes because its underlying associated-graded class
      -- already vanishes in `grR`.
      apply Subtype.ext
      change
        ((associatedGradedPresentation_degree_piece_to_grade (R := R) x n p :
          idealAssociatedGradedRingGrade (maximalIdeal R) n) : grR) = 0
      exact hp
    let e := idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
    change
      e
          (associatedGradedPresentation_degree_piece_to_grade (R := R) x n p) = 0
    calc
      e (associatedGradedPresentation_degree_piece_to_grade (R := R) x n p) = e 0 := by
        exact congrArg (fun z : idealAssociatedGradedRingGrade (maximalIdeal R) n ↦ e z) hp_grade
      _ = 0 := e.map_zero

/-- Helper for Lemma 10.106.1: the first-isomorphism quotient of the degree-`n` presentation is
already the textbook associated graded piece `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
private noncomputable def associatedGradedPresentation_degree_piece_quotient_equiv_piece
    {d n : ℕ} (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    (MvPolynomial.homogeneousSubmodule (Fin d) κ n ⧸
        LinearMap.ker (associatedGradedPresentation_degree_piece_map (R := R) x n)) ≃ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  (associatedGradedPresentation_degree_piece_map (R := R) x n).quotKerEquivOfSurjective
    (associatedGradedPresentation_degree_piece_surjective (R := R) x hx)

/-- Helper for Lemma 10.106.1: the quotient of the degree-`n` polynomial piece by the degreewise
kernel has `κ`-dimension equal to the maximal-ideal Hilbert-Samuel `φ`-value. -/
private theorem associatedGradedPresentation_degree_piece_quotient_finrank_eq_phi
    {d n : ℕ} (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    Module.finrank κ
        (MvPolynomial.homogeneousSubmodule (Fin d) κ n ⧸
          LinearMap.ker (associatedGradedPresentation_degree_piece_map (R := R) x n)) =
      (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
  -- Transfer the quotient finrank through the explicit first-isomorphism equivalence.
  exact
    (LinearEquiv.finrank_eq
      (associatedGradedPresentation_degree_piece_quotient_equiv_piece (R := R) x hx)).trans
      (idealAssociatedGradedPiece_finrank_eq_phi_local (R := R) n)

/-- Helper for Lemma 10.106.1: the image of a homogeneous degree piece in the quotient by the
presentation kernel has the same dimension as the first-isomorphism quotient of that degree
piece. -/
private theorem associatedGradedPresentation_kernel_degreePiece_finrank_eq_phi
    {d n : ℕ} (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    Module.finrank κ
        ((MvPolynomial.homogeneousSubmodule (Fin d) κ n).map
          (Ideal.Quotient.mkₐ κ
            (RingHom.ker (associatedGradedPresentation x).toRingHom)).toLinearMap) =
      (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
  let q :
      MvPolynomial.homogeneousSubmodule (Fin d) κ n →ₗ[κ]
        MvPolynomial (Fin d) κ ⧸ RingHom.ker (associatedGradedPresentation x).toRingHom :=
    (Ideal.Quotient.mkₐ κ
      (RingHom.ker (associatedGradedPresentation x).toRingHom)).toLinearMap.comp
        (MvPolynomial.homogeneousSubmodule (Fin d) κ n).subtype
  have hrange :
      LinearMap.range q =
        (MvPolynomial.homogeneousSubmodule (Fin d) κ n).map
          (Ideal.Quotient.mkₐ κ
            (RingHom.ker (associatedGradedPresentation x).toRingHom)).toLinearMap := by
    -- The range of the restricted quotient map is exactly the image submodule used by the
    -- quotient-Hilbert-function definition.
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hker :
      LinearMap.ker q =
        LinearMap.ker (associatedGradedPresentation_degree_piece_map (R := R) x n) := by
    -- Both kernels consist of homogeneous polynomials whose underlying polynomial lies in the
    -- algebra kernel of the presentation.
    rw [associatedGradedPresentation_degree_piece_kernel_eq (R := R) x]
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker] at hp
      change
        Ideal.Quotient.mk
            (RingHom.ker (associatedGradedPresentation x).toRingHom)
            (p : MvPolynomial (Fin d) κ) = 0 at hp
      exact (Ideal.Quotient.eq_zero_iff_mem).1 hp
    · intro hp
      rw [LinearMap.mem_ker]
      change
        Ideal.Quotient.mk
            (RingHom.ker (associatedGradedPresentation x).toRingHom)
            (p : MvPolynomial (Fin d) κ) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hp
  calc
    Module.finrank κ
        ((MvPolynomial.homogeneousSubmodule (Fin d) κ n).map
          (Ideal.Quotient.mkₐ κ
            (RingHom.ker (associatedGradedPresentation x).toRingHom)).toLinearMap) =
      Module.finrank κ (LinearMap.range q) := by
        rw [hrange]
    _ =
      Module.finrank κ
        (MvPolynomial.homogeneousSubmodule (Fin d) κ n ⧸ LinearMap.ker q) := by
        exact (LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange q)).symm
    _ =
      Module.finrank κ
        (MvPolynomial.homogeneousSubmodule (Fin d) κ n ⧸
          LinearMap.ker (associatedGradedPresentation_degree_piece_map (R := R) x n)) := by
        rw [hker]
    _ = (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
        exact associatedGradedPresentation_degree_piece_quotient_finrank_eq_phi (R := R) x hx

/-- Helper for Lemma 10.106.1: the polynomial presentation preserves each homogeneous degree
piece of the source grading. -/
private theorem associatedGradedPresentation_gradedRingHom_map_mem {d n : ℕ}
    (x : Fin d → maximalIdeal R) {p : MvPolynomial (Fin d) κ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin d) κ n) :
    associatedGradedPresentation x p ∈ idealAssociatedGradedRingGrade (maximalIdeal R) n := by
  -- Membership in the homogeneous submodule is exactly homogeneity of degree `n`.
  have hp_hom : p.IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
  exact associatedGradedPresentation_mem_grade_of_homogeneous (R := R) x hp_hom

/-- Helper for Lemma 10.106.1: the associated graded presentation is a graded ring homomorphism
from the standard polynomial grading to the maximal-ideal associated graded ring. -/
private noncomputable def associatedGradedPresentation_gradedRingHom {d : ℕ}
    (x : Fin d → maximalIdeal R) :
    MvPolynomial.homogeneousSubmodule (Fin d) κ →+*ᵍ
      idealAssociatedGradedRingGrade (maximalIdeal R) :=
  { toRingHom := (associatedGradedPresentation x).toRingHom
    map_mem := associatedGradedPresentation_gradedRingHom_map_mem (R := R) x }

/-- Helper for Lemma 10.106.1: the algebra kernel of the associated graded presentation is
already homogeneous, so the source Hilbert-function estimate can be applied to the actual kernel
ideal instead of its homogeneous hull. -/
private theorem associatedGradedPresentation_kernel_isHomogeneous {d : ℕ}
    (x : Fin d → maximalIdeal R) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) κ)
      (RingHom.ker (associatedGradedPresentation x).toRingHom) := by
  let f := associatedGradedPresentation_gradedRingHom (R := R) x
  -- Pull back the bottom homogeneous ideal along the graded presentation; its underlying ideal is
  -- exactly the ordinary algebra kernel.
  have hker :
      RingHom.ker (associatedGradedPresentation x).toRingHom =
        ((⊥ : HomogeneousIdeal (idealAssociatedGradedRingGrade (maximalIdeal R))).comap f).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_comap]
    simpa [f, associatedGradedPresentation_gradedRingHom] using
      (RingHom.ker_eq_comap_bot (associatedGradedPresentation x).toRingHom)
  rw [hker]
  exact HomogeneousIdeal.isHomogeneous
    ((⊥ : HomogeneousIdeal (idealAssociatedGradedRingGrade (maximalIdeal R))).comap f)

/-- Helper for Lemma 10.106.1: package the actual algebra kernel of the polynomial presentation
as a homogeneous ideal, matching the source proof's kernel-quotient route. -/
private def associatedGradedPresentation_kernel_homogeneousIdeal {d : ℕ}
    (x : Fin d → maximalIdeal R) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) κ) :=
  ⟨RingHom.ker (associatedGradedPresentation x).toRingHom,
    associatedGradedPresentation_kernel_isHomogeneous (R := R) x⟩

/-- Helper for Lemma 10.106.1: the packaged homogeneous ideal is definitionally the actual kernel
ideal of `associatedGradedPresentation x`. -/
private theorem associatedGradedPresentation_kernel_homogeneousIdeal_toIdeal {d : ℕ}
    (x : Fin d → maximalIdeal R) :
    (associatedGradedPresentation_kernel_homogeneousIdeal (R := R) x).toIdeal =
      RingHom.ker (associatedGradedPresentation x).toRingHom := by
  -- The homogeneous-ideal wrapper only records the previously proved homogeneity of the kernel.
  rfl

/-- Helper for Lemma 10.106.1: in nonnegative degree, the quotient Hilbert function of the
presentation kernel equals the Hilbert-Samuel `φ`-value. -/
private theorem associatedGradedPresentation_kernelHilbertFunction_eq_phi_of_nonneg {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x)
    (z : ℤ) (hz : 0 ≤ z) :
    homogeneousIdealQuotientHilbertFunction
        (associatedGradedPresentation_kernel_homogeneousIdeal (R := R) x) z =
      ((Ideal.hilbertSamuelPhi (maximalIdeal R) R z.toNat).toNat : ℤ) := by
  -- First unfold the public Hilbert-function wrapper; the remaining issue is the comparison
  -- between the quotient-map image of the source degree piece and the first-isomorphism quotient
  -- already used for the presentation degree piece.
  rw [homogeneousIdealQuotientHilbertFunction, if_pos hz]
  change
    (Module.finrank κ
        ((MvPolynomial.homogeneousSubmodule (Fin d) κ z.toNat).map
          (Ideal.Quotient.mkₐ κ
            (RingHom.ker (associatedGradedPresentation x).toRingHom)).toLinearMap) : ℤ) =
      ((Ideal.hilbertSamuelPhi (maximalIdeal R) R z.toNat).toNat : ℤ)
  exact_mod_cast
    associatedGradedPresentation_kernel_degreePiece_finrank_eq_phi (R := R) x hx

/-- Helper for Lemma 10.106.1: the quotient Hilbert function of the presentation kernel
eventually agrees with the Hilbert-Samuel `φ`-function. -/
private theorem associatedGradedPresentation_kernelHilbertFunction_eventuallyEq_phi {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    homogeneousIdealQuotientHilbertFunction
        (associatedGradedPresentation_kernel_homogeneousIdeal (R := R) x) =ᶠ[Filter.atTop]
      fun z : ℤ => ((Ideal.hilbertSamuelPhi (maximalIdeal R) R z.toNat).toNat : ℤ) := by
  -- On a tail of nonnegative integer degrees, the pointwise comparison just proved applies.
  filter_upwards [Filter.eventually_ge_atTop (0 : ℤ)] with z hz
  exact associatedGradedPresentation_kernelHilbertFunction_eq_phi_of_nonneg (R := R) x hx z hz

/-- Helper for Chap10 Lemma 10 106 1: the rational polynomial attached to a finite
binomial-coefficient expansion. -/
private noncomputable def numericalPolynomialCandidateForDegreeBound {r : ℕ}
    (a : Fin (r + 1) → ℚ) : Polynomial ℚ :=
  ∑ i : Fin (r + 1), a i • Polynomial.preHilbertPoly ℚ i i

/-- Helper for Chap10 Lemma 10 106 1: the candidate polynomial evaluates to the corresponding
binomial expansion on a natural-number tail. -/
private theorem numericalPolynomialCandidateForDegreeBound_spec_nat {r : ℕ}
    (a : Fin (r + 1) → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      (numericalPolynomialCandidateForDegreeBound a).eval (n : ℚ) =
        ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
  -- On the tail `r ≤ n`, `preHilbertPoly` computes the binomial coefficient term by term.
  filter_upwards [eventually_ge_atTop r] with n hn
  simp only [numericalPolynomialCandidateForDegreeBound, Polynomial.eval_finset_sum,
    Polynomial.eval_smul, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add]
  · rw [Nat.sub_add_cancel (le_trans (Nat.lt_succ_iff.mp i.2) hn)]
    simp [Ring.choose_natCast, mul_comm]
  · exact le_trans (Nat.lt_succ_iff.mp i.2) hn

/-- Helper for Chap10 Lemma 10 106 1: a candidate indexed up to `r` has degree at most `r`. -/
private theorem numericalPolynomialCandidateForDegreeBound_degree_le {r : ℕ}
    (a : Fin (r + 1) → ℚ) :
    (numericalPolynomialCandidateForDegreeBound a).degree ≤ (r : WithBot ℕ) := by
  -- Bound the degree of the finite sum by the largest degree of its pre-Hilbert basis terms.
  calc
    (numericalPolynomialCandidateForDegreeBound a).degree ≤
        Finset.univ.sup fun i : Fin (r + 1) ↦
          (a i • Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).degree := by
      exact Polynomial.degree_sum_le _ _
    _ ≤ (r : WithBot ℕ) := by
      refine Finset.sup_le ?_
      intro i _
      refine (Polynomial.degree_smul_le (a i)
        (Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ))).trans ?_
      calc
        (Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).degree ≤
            ((Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).natDegree : WithBot ℕ) :=
          Polynomial.degree_le_natDegree
        _ = (i : ℕ) := by
          rw [Polynomial.natDegree_preHilbertPoly]
        _ ≤ (r : WithBot ℕ) := by
          exact_mod_cast Nat.lt_succ_iff.mp i.2

/-- Helper for Chap10 Lemma 10 106 1: eventual equality transports the source-facing numerical
degree bound. -/
private theorem hasNumericalPolynomialDegreeLT_congr_eventuallyEq {A : Type u} [AddCommGroup A]
    {f g : ℤ → A} {m : ℤ} (hfg : f =ᶠ[atTop] g) :
    HasNumericalPolynomialDegreeLT f m → HasNumericalPolynomialDegreeLT g m := by
  -- Transport either the eventual-zero branch or the explicit binomial expansion branch.
  intro hf
  rcases hf with hzero | ⟨r, hr, a, ha⟩
  · exact Or.inl (hfg.symm.trans hzero)
  · exact Or.inr ⟨r, hr, a, hfg.symm.trans ha⟩

/-- Helper for Chap10 Lemma 10 106 1: a source-facing degree `< d - 1` bound gives a rational
polynomial representative of ordinary degree `< d - 1`. -/
private theorem exists_ratPolynomial_degree_lt_of_hasNumericalPolynomialDegreeLT_pred
    {f : ℤ → ℤ} {d : ℕ} (hdpos : 0 < d)
    (hf : HasNumericalPolynomialDegreeLT f ((d : ℤ) - 1)) :
    ∃ P : Polynomial ℚ,
      (∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = (f n : ℚ)) ∧
        P.degree < ((d - 1 : ℕ) : WithBot ℕ) := by
  -- Convert the source's two cases into an ordinary rational polynomial and record its degree.
  rcases hf with hzero | ⟨r, hr, a, ha⟩
  · refine ⟨0, ?_, ?_⟩
    · have hzeroNat : (fun n : ℕ ↦ f n) =ᶠ[atTop] fun _ ↦ (0 : ℤ) := by
        simpa using hzero.comp_tendsto
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
      filter_upwards [hzeroNat] with n hn
      simp [hn]
    · simp
  · let aq : Fin (r + 1) → ℚ := fun i ↦ (a i : ℚ)
    refine ⟨numericalPolynomialCandidateForDegreeBound aq, ?_, ?_⟩
    · have haNat :
          (fun n : ℕ ↦ f n) =ᶠ[atTop]
            fun n ↦ ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
          simpa using ha.comp_tendsto
            (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
      filter_upwards [haNat, numericalPolynomialCandidateForDegreeBound_spec_nat aq] with n hn hP
      calc
        (numericalPolynomialCandidateForDegreeBound aq).eval (n : ℚ) =
            ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • aq i := hP
        _ = (f n : ℚ) := by
          simpa [aq, hn, zsmul_eq_mul]
    · have hpredInt : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
        exact Int.ofNat_sub (Nat.one_le_of_lt hdpos)
      have hrNat : r < d - 1 := by
        have hr' : (r : ℤ) < ((d - 1 : ℕ) : ℤ) := by
          simpa [hpredInt] using hr
        exact_mod_cast hr'
      exact lt_of_le_of_lt (numericalPolynomialCandidateForDegreeBound_degree_le aq)
        (by exact_mod_cast hrNat)

/-- Helper for Chap10 Lemma 10 106 1: an eventual `χ`-polynomial for `R` produces the backward
difference polynomial for the corresponding `φ`-function. -/
private theorem eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi_self
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {Q : Polynomial ℚ}
    (hQ : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_ I R n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
        ((φ_ I R n).toNat : ℚ) := by
  -- Compare `χ(n)` and `χ(n - 1)` on a common tail, then use the public `χ/φ` successor formula.
  rcases eventually_atTop.mp hQ with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  have hQn : Q.eval (n : ℚ) = ((χ_ I R n).toNat : ℚ) := by
    exact hN n (le_trans (Nat.le_succ N) hn)
  have hQpred : Q.eval ((n - 1 : ℕ) : ℚ) = ((χ_ I R (n - 1)).toNat : ℚ) := by
    apply hN (n - 1)
    omega
  have hchiNat :
      (χ_ I R n).toNat = (χ_ I R (n - 1)).toNat + (φ_ I R n).toNat := by
    have hsucc :=
      hilbertSamuelChi_succ_toNat_eq_add_hilbertSamuelPhi_toNat_of_isIdealOfDefinition
        (R := R) (I := I) hI (n - 1)
    simpa [Nat.sub_add_cancel hnpos] using hsucc
  have hphi :
      ((φ_ I R n).toNat : ℚ) =
        ((χ_ I R n).toNat : ℚ) - ((χ_ I R (n - 1)).toNat : ℚ) := by
    have hchiRat :
        ((χ_ I R n).toNat : ℚ) =
          ((χ_ I R (n - 1)).toNat : ℚ) + ((φ_ I R n).toNat : ℚ) := by
      exact_mod_cast hchiNat
    linarith
  calc
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
        Q.eval (n : ℚ) - Q.eval ((n - 1 : ℕ) : ℚ) := by
          rw [Polynomial.eval_sub, Polynomial.eval_comp]
          simp [hnpos, sub_eq_add_neg]
    _ = ((φ_ I R n).toNat : ℚ) := by
      rw [hQn, hQpred, hphi]

/-- Helper for Chap10 Lemma 10 106 1: the first forward difference of a positive-degree
polynomial drops the degree by one. -/
private theorem degree_forward_difference_eq_sub_one_of_degree_pos_forHilbert
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q.comp (Polynomial.X + Polynomial.C 1) - Q).degree = (Q.natDegree - 1 : ℕ) := by
  let D : Polynomial ℚ := Q.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q
  have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
  have hnatPos : 0 < Q.natDegree := by
    rw [Polynomial.degree_eq_natDegree hQ0, Nat.cast_pos] at hQdeg
    exact hQdeg
  have hdegComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree = Q.degree := by
    calc
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree =
          Q.degree * (Polynomial.X + Polynomial.C (1 : ℚ)).degree := by
            exact Polynomial.degree_comp (p := Q) (q := Polynomial.X + Polynomial.C (1 : ℚ)) <| by
              rw [Polynomial.degree_X_add_C (1 : ℚ)]
              decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_add_C (1 : ℚ)]
        simp
  have hlcComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [Polynomial.leadingCoeff_X_add_C]
      simp
    · rw [Polynomial.natDegree_X_add_C (1 : ℚ)]
      decide
  have hUpperLt' : D.degree < (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree := by
    -- The top coefficients cancel in the translated difference.
    simpa [D] using
      (Polynomial.degree_sub_lt hdegComp
        ((Polynomial.comp_X_add_C_ne_zero_iff (p := Q) (t := (1 : ℚ))).2 hQ0)
        hlcComp)
  have hUpperLt : D.degree < Q.degree := by
    exact hdegComp ▸ hUpperLt'
  have hUpper : D.degree ≤ (Q.natDegree - 1 : ℕ) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hDnat : D.natDegree < Q.natDegree := by
        exact (Polynomial.natDegree_lt_iff_degree_lt hD0).2 <| by
          simpa [Polynomial.degree_eq_natDegree hQ0] using hUpperLt
      rw [Polynomial.degree_eq_natDegree hD0]
      exact WithBot.coe_le_coe.2 (Nat.le_pred_of_lt hDnat)
  have hLower : ((Q.natDegree - 1 : ℕ) : WithBot ℕ) ≤ D.degree := by
    -- The coefficient in degree `natDegree Q - 1` is nonzero.
    let H : Polynomial ℚ := Polynomial.hasseDeriv (Q.natDegree - 1) Q
    have hcoeffComp :
        (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).coeff (Q.natDegree - 1) =
          H.eval (1 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (1 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hcoeffQ :
        Q.coeff (Q.natDegree - 1) = H.eval (0 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (0 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hHnat : H.natDegree = 1 := by
      dsimp [H]
      rw [Polynomial.natDegree_hasseDeriv]
      omega
    have hHdeg : H.degree ≤ 1 := by
      exact Polynomial.degree_le_of_natDegree_le (by rw [hHnat]; exact le_rfl)
    have hHshape :
        H = Polynomial.C (H.coeff 1) * Polynomial.X + Polynomial.C (H.coeff 0) := by
      exact Polynomial.eq_X_add_C_of_degree_le_one hHdeg
    have hEvalDiff : H.eval (1 : ℚ) - H.eval (0 : ℚ) = H.coeff 1 := by
      rw [hHshape]
      simp
    have hcoeffH :
        H.coeff 1 = (Q.natDegree : ℚ) * Q.leadingCoeff := by
      dsimp [H]
      rw [Polynomial.hasseDeriv_coeff]
      have hpred : 1 + (Q.natDegree - 1) = Q.natDegree := by
        omega
      have hchoose : (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = Q.natDegree := by
        have hchoose' :
            (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = 1 + (Q.natDegree - 1) := by
          simpa [Nat.add_comm, Nat.succ_eq_add_one] using
            Nat.choose_succ_self_right (Q.natDegree - 1)
        rw [hchoose']
        omega
      rw [hchoose, hpred, Polynomial.leadingCoeff]
    have hcoeffNe : D.coeff (Q.natDegree - 1) ≠ 0 := by
      dsimp [D]
      rw [Polynomial.coeff_sub, hcoeffComp, hcoeffQ, hEvalDiff, hcoeffH]
      exact mul_ne_zero
        (by exact_mod_cast Nat.ne_of_gt hnatPos)
        (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
    exact Polynomial.le_degree_of_ne_zero (n := Q.natDegree - 1) hcoeffNe
  change D.degree = (Q.natDegree - 1 : ℕ)
  exact le_antisymm hUpper hLower

/-- Helper for Chap10 Lemma 10 106 1: the first backward difference of a positive-degree
polynomial drops the degree by one. -/
private theorem degree_backward_difference_eq_sub_one_of_degree_pos_forHilbert
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree = (Q.natDegree - 1 : ℕ) := by
  let Q₁ : Polynomial ℚ := Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))
  have hQ₁deg : Q₁.degree = Q.degree := by
    calc
      Q₁.degree = (Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))).degree := by
        rfl
      _ = Q.degree * (Polynomial.X - Polynomial.C (1 : ℚ)).degree := by
        exact Polynomial.degree_comp (p := Q) (q := Polynomial.X - Polynomial.C (1 : ℚ)) <| by
          rw [Polynomial.degree_X_sub_C (1 : ℚ)]
          decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_sub_C (1 : ℚ)]
        simp
  have hQ₁pos : 0 < Q₁.degree := by
    simpa [hQ₁deg] using hQdeg
  have hQ₁nat : Q₁.natDegree = Q.natDegree := by
    have hQ₁0 : Q₁ ≠ 0 := Polynomial.ne_zero_of_degree_gt hQ₁pos
    have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
    exact WithBot.coe_eq_coe.mp <| by
      simpa [Polynomial.degree_eq_natDegree hQ₁0, Polynomial.degree_eq_natDegree hQ0] using hQ₁deg
  have hrewrite :
      Q₁.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q₁ =
        Q - Q.comp (Polynomial.X - Polynomial.C (1 : ℚ)) := by
    -- Translating `Q(x - 1)` forward by `1` recovers `Q(x)`.
    simp [Q₁, Polynomial.comp_assoc, sub_eq_add_neg, add_left_comm, add_comm]
  rw [← hrewrite, degree_forward_difference_eq_sub_one_of_degree_pos_forHilbert hQ₁pos, hQ₁nat]

/-- Helper for Chap10 Lemma 10 106 1: positive Hilbert-Samuel degree `d` makes the Hilbert
polynomial have degree `d - 1`. -/
private theorem hilbertPolynomial_degree_eq_pred_of_hilbertSamuelPolynomialDegree
    {d : ℕ} (hdpos : 0 < d) (hdeg : hilbertSamuelPolynomialDegree R R = d) :
    (hilbertPolynomial R R).degree = ((d - 1 : ℕ) : WithBot ℕ) := by
  let Q : Polynomial ℚ := hilbertSamuelChiPolynomial R R
  have hQevent :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_ (maximalIdeal R) R n).toNat : ℚ) := by
    simpa [Q] using hilbertSamuelChiPolynomial_eventuallyEq R R
  have hQdeg : Q.degree = (d : WithBot ℕ) := by
    simpa [Q, hilbertSamuelPolynomialDegree] using hdeg
  have hQpos : 0 < Q.degree := by
    rw [hQdeg]
    exact_mod_cast hdpos
  have hbackevent :
      ∀ᶠ n : ℕ in atTop,
        (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
          ((φ_ (maximalIdeal R) R n).toNat : ℚ) :=
    eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi_self
      (R := R) (maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition hQevent
  have hdegreeEq :
      (hilbertPolynomial R R).degree =
        (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree := by
    -- Lemma 10.59.7 identifies the degree of any eventual `φ`-polynomial.
    exact Ideal.hilbertSamuelPhi_degree_eq_of_isIdealOfDefinition
      (R := R) (M := R) (I := maximalIdeal R) (I' := maximalIdeal R)
      Ideal.maximalIdeal_isIdealOfDefinition Ideal.maximalIdeal_isIdealOfDefinition
      (hilbertPolynomial_eventuallyEq R R) hbackevent
  have hQnat : Q.natDegree = d := by
    have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQpos
    have hQdeg' : (Q.natDegree : WithBot ℕ) = (d : WithBot ℕ) := by
      simpa [Polynomial.degree_eq_natDegree hQ0] using hQdeg
    exact WithBot.coe_eq_coe.mp hQdeg'
  calc
    (hilbertPolynomial R R).degree =
        (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree := hdegreeEq
    _ = (Q.natDegree - 1 : ℕ) :=
      degree_backward_difference_eq_sub_one_of_degree_pos_forHilbert hQpos
    _ = ((d - 1 : ℕ) : WithBot ℕ) := by
      rw [hQnat]

/-- Helper for Chap10 Lemma 10 106 1: the maximal-ideal `φ`-function cannot have source-facing
degree `< d - 1` when the Hilbert-Samuel degree is `d > 0`. -/
private theorem not_hasNumericalPolynomialDegreeLT_hilbertSamuelPhi_of_hilbertSamuelPolynomialDegree
    {d : ℕ} (hdpos : 0 < d) (hdeg : hilbertSamuelPolynomialDegree R R = d) :
    ¬ HasNumericalPolynomialDegreeLT
      (fun z : ℤ => ((Ideal.hilbertSamuelPhi (maximalIdeal R) R z.toNat).toNat : ℤ))
      ((d : ℤ) - 1) := by
  -- A source-facing upper bound would force the canonical Hilbert polynomial below degree `d - 1`.
  intro hlt
  rcases exists_ratPolynomial_degree_lt_of_hasNumericalPolynomialDegreeLT_pred
      hdpos hlt with ⟨P, hPevent, hPdeg⟩
  have hPeq : P = hilbertPolynomial R R := by
    exact eq_hilbertPolynomial R R (by simpa using hPevent)
  have hupper : (hilbertPolynomial R R).degree < ((d - 1 : ℕ) : WithBot ℕ) := by
    simpa [← hPeq] using hPdeg
  have hlower :
      (hilbertPolynomial R R).degree = ((d - 1 : ℕ) : WithBot ℕ) :=
    hilbertPolynomial_degree_eq_pred_of_hilbertSamuelPolynomialDegree (R := R) hdpos hdeg
  rw [hlower] at hupper
  exact (not_lt_of_ge le_rfl) hupper

/-- Helper for Chap10 Lemma 10 106 1: the degree-zero residue-field map into the associated
graded ring is injective. -/
private theorem algebraMap_residueField_associatedGraded_injective :
    Function.Injective (algebraMap κ grR) := by
  -- Compare degree-zero stage classes through the canonical `gr₀ ≃ R / maximalIdeal` equivalence.
  intro c c' h
  rcases Ideal.Quotient.mk_surjective c with ⟨r, rfl⟩
  rcases Ideal.Quotient.mk_surjective c' with ⟨s, rfl⟩
  let r0 : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R 0 :=
    ⟨r, by simp [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.mul_top]⟩
  let s0 : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R 0 :=
    ⟨s, by simp [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.mul_top]⟩
  have hrmap : algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) =
      idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 := by
    simpa [r0] using associatedGradedPresentation_constant_map_eq_stageClass_zero (R := R) r
  have hsmap : algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) s) =
      idealAssociatedGradedStageClass (maximalIdeal R) 0 s0 := by
    simpa [s0] using associatedGradedPresentation_constant_map_eq_stageClass_zero (R := R) s
  have hstage : idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 =
      idealAssociatedGradedStageClass (maximalIdeal R) 0 s0 := by
    simpa [hrmap, hsmap] using h
  have hgrade :
      (⟨idealAssociatedGradedStageClass (maximalIdeal R) 0 r0,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) 0 r0⟩ :
        idealAssociatedGradedRingGrade (maximalIdeal R) 0) =
      ⟨idealAssociatedGradedStageClass (maximalIdeal R) 0 s0,
          idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) 0 s0⟩ := by
    exact Subtype.ext hstage
  have hquot := congrArg (idealAssociatedGradedRingGrade_equiv_piece (maximalIdeal R) 0) hgrade
  rw [idealAssociatedGradedRingGrade_equiv_piece_apply_stage,
    idealAssociatedGradedRingGrade_equiv_piece_apply_stage] at hquot
  have hsub := (Submodule.Quotient.eq _).1 hquot
  have hmem : r - s ∈ maximalIdeal R := by
    simpa [r0, s0, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.mul_top] using hsub
  exact (Ideal.Quotient.eq).2 hmem

/-- Helper for Chap10 Lemma 10 106 1: with no variables, the associated-graded presentation is
injective. -/
private theorem associatedGradedPresentation_kernel_eq_bot_of_zero
    (x : Fin 0 → maximalIdeal R) :
    RingHom.ker (associatedGradedPresentation x).toRingHom = ⊥ := by
  -- The zero-variable polynomial algebra is just the residue field, so injectivity is the
  -- degree-zero residue-field injectivity just proved.
  have hinj : Function.Injective (associatedGradedPresentation x) := by
    rw [associatedGradedPresentation]
    exact (MvPolynomial.aeval_injective_iff_of_isEmpty).2
      algebraMap_residueField_associatedGraded_injective
  exact (RingHom.injective_iff_ker_eq_bot
    (f := (associatedGradedPresentation x).toRingHom)).1 hinj

/-- Chap10 Lemma 10 106 1: for a regular system of parameters, the associated-graded polynomial
presentation has trivial kernel. -/
private theorem associatedGradedPresentation_kernel_eq_bot {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    RingHom.ker (associatedGradedPresentation x).toRingHom = ⊥ := by
  -- Split off the empty-variable case; the positive-dimensional branch follows the source
  -- Hilbert-function degree contradiction.
  rcases Nat.eq_zero_or_pos d with hdzero | hdpos
  · subst d
    exact associatedGradedPresentation_kernel_eq_bot_of_zero (R := R) x
  · by_contra hker
    let I := associatedGradedPresentation_kernel_homogeneousIdeal (R := R) x
    have hIne : I ≠ ⊥ := by
      intro hI
      have hto := congrArg HomogeneousIdeal.toIdeal hI
      have hkerbot : RingHom.ker (associatedGradedPresentation x).toRingHom = ⊥ := by
        simpa [I, associatedGradedPresentation_kernel_homogeneousIdeal_toIdeal] using hto
      exact hker hkerbot
    have hkernelDegree :
        HasNumericalPolynomialDegreeLT (homogeneousIdealQuotientHilbertFunction I)
          ((d : ℤ) - 1) :=
      nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound I hIne
    have hphiDegree :
        HasNumericalPolynomialDegreeLT
          (fun z : ℤ => ((Ideal.hilbertSamuelPhi (maximalIdeal R) R z.toNat).toNat : ℤ))
          ((d : ℤ) - 1) :=
      hasNumericalPolynomialDegreeLT_congr_eventuallyEq
        (associatedGradedPresentation_kernelHilbertFunction_eventuallyEq_phi (R := R) x hx)
        hkernelDegree
    have hdim : ringKrullDim R = d :=
      (IsLocalRing.isRegularSystemOfParameters_iff x).1 hx |>.1
    have hdeg : hilbertSamuelPolynomialDegree R R = d :=
      ((local_noetherian_ring_dimension_tfae (R := R) d).out 0 1 rfl rfl).mp hdim
    exact
      (not_hasNumericalPolynomialDegreeLT_hilbertSamuelPhi_of_hilbertSamuelPolynomialDegree
        (R := R) hdpos hdeg) hphiDegree

/-- After choosing a regular system of parameters `x`, one can realize the polynomial presentation
of the associated graded ring by sending `X i` to the degree-one class of `x i`. -/
theorem regularSystemOfParameters_exists_associatedGraded_algEquiv_mvPolynomial {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    ∃ e : MvPolynomial (Fin d) κ ≃ₐ[κ] grR,
      ∀ i : Fin d, e (MvPolynomial.X i) = idealAssociatedGradedDegreeOne (x i) := by
  classical
  let φ : MvPolynomial (Fin d) κ →ₐ[κ] grR := associatedGradedPresentation x
  have hφX : ∀ i : Fin d, φ (MvPolynomial.X i) = idealAssociatedGradedDegreeOne (x i) := by
    -- The chosen presentation already has the required behavior on generators.
    intro i
    simpa [φ] using associatedGradedPresentation_X (R := R) x i
  have hparam : parameterIdeal x = maximalIdeal R :=
    (IsLocalRing.isRegularSystemOfParameters_iff x).1 hx |>.2
  -- Route correction: follow the textbook surjection-plus-kernel route rather than the older
  -- quasi-regular direct-sum bridge.
  -- The verified prefix is now in place: `hparam` identifies the chosen parameters with
  -- generators of `maximalIdeal R`, the previous helper supplies homogeneous polynomial
  -- representatives for every element of every power `maximalIdeal R ^ n`, the new coefficient-free
  -- monomial formula `associatedGradedPresentation_monomial_weight_eq_degree_one_prod` computes
  -- evaluation on pure monomials, and the local support file now exposes the owner-grade/piece equivalence
  -- `idealAssociatedGradedRingGrade_equiv_piece_local`.
  have hφ_surj : Function.Surjective φ :=
    associatedGradedPresentation_surjective (R := R) x hx
  have hφ_ker : RingHom.ker φ.toRingHom = ⊥ :=
    associatedGradedPresentation_kernel_eq_bot (R := R) x hx
  have hφ_inj : Function.Injective φ := by
    exact (RingHom.injective_iff_ker_eq_bot (f := φ.toRingHom)).2 hφ_ker
  refine ⟨AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩, ?_⟩
  exact hφX

/-- Consequence of Chap10 Lemma 10 106 1: if `(R, maximalIdeal R, κ)` is a regular local ring of dimension `d`, then
the associated graded ring `⊕ n, maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)` is isomorphic to
the polynomial `κ`-algebra in `d` variables. -/
@[stacks 00NO]
theorem regularLocalRing_associatedGraded_nonempty_algEquiv_mvPolynomial {d : ℕ}
    (hdim : ringKrullDim R = d) :
    Nonempty (MvPolynomial (Fin d) κ ≃ₐ[κ] grR) := by
  -- Choose a regular system of parameters of length `d` and invoke the parameterized theorem.
  rcases
      (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := R) (d := d) hdim).1
        inferInstance with
    ⟨x, hx⟩
  rcases
      regularSystemOfParameters_exists_associatedGraded_algEquiv_mvPolynomial
        (R := R) hx with
    ⟨e, -⟩
  exact ⟨e⟩

end
