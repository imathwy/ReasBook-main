import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_59_9
import stacks_proof.stacks_project.Chap10.Lemma_10_106_1.StageClassAPI

open IsLocalRing

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "κ" => ResidueField R
local notation "grR" => idealAssociatedGradedRing (maximalIdeal R)

local instance presentationMonomialsCommRingGrR : CommRing grR :=
  inferInstanceAs (CommRing (idealAssociatedGradedRing (maximalIdeal R)))

local instance presentationMonomialsAlgebraGrR : Algebra κ grR :=
  inferInstance

local instance presentationMonomialsSMulGrR : SMul κ grR where
  smul c z := algebraMap κ grR c * z

local instance presentationMonomialsModuleGrR : Module κ grR := by
  let _ : Module grR grR := Semiring.toModule
  exact Module.compHom grR (algebraMap κ grR)

local instance presentationMonomialsPieceModule (n : ℕ) :
    Module κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  exact inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n))

local instance presentationMonomialsStageQuotientModule (n : ℕ) :
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

local instance presentationMonomialsStageQuotientScalarTower (n : ℕ) :
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
local instance presentationMonomialsGradeSMul (n : ℕ) :
    SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Transport the residue-field scalar action from the textbook quotient piece through the
  -- canonical owner-grade/piece equivalence.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  show SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) from
    (e.toAddEquiv.module κ).toSMul

/-- Helper for Lemma 10.106.1: each owner grade of `grR` is a `κ`-module via the ambient scalar
action on `grR`. -/
local instance presentationMonomialsGradeModule (n : ℕ) :
    Module κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Route correction: transport the module structure from the textbook quotient piece instead of
  -- rebuilding the stage-class action inside `grR`.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  e.toAddEquiv.module κ

/-- Helper for Lemma 10.106.1: the canonical polynomial presentation attached to a chosen regular
system of parameters sends each variable to its degree-one class in the associated graded ring. -/
noncomputable def associatedGradedPresentation {d : ℕ} (x : Fin d → maximalIdeal R) :
    MvPolynomial (Fin d) κ →ₐ[κ] grR :=
  MvPolynomial.aeval fun i ↦ idealAssociatedGradedDegreeOne (x i)

/-- Helper for Lemma 10.106.1: the canonical presentation evaluates each variable at the
corresponding degree-one parameter class. -/
@[simp] theorem associatedGradedPresentation_X {d : ℕ} (x : Fin d → maximalIdeal R) (i : Fin d) :
    associatedGradedPresentation x (MvPolynomial.X i) = idealAssociatedGradedDegreeOne (x i) := by
  -- The presentation map is defined by polynomial evaluation on the chosen degree-one classes.
  simp [associatedGradedPresentation]

/-- Helper for Lemma 10.106.1: the `n`-th power of a chosen parameter gives the `n`-th power of
its degree-one class in the associated graded ring. -/
theorem idealAssociatedGradedStageClass_parameter_pow_eq {d n : ℕ}
    (x : Fin d → maximalIdeal R) (i : Fin d) :
    idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨((x i : maximalIdeal R) : R) ^ n, by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.pow_mem_pow (x i).2 n⟩ =
      idealAssociatedGradedDegreeOne (x i) ^ n := by
  -- Repeatedly apply the local stage-class multiplication rule from the helper API.
  induction n with
  | zero =>
      -- In degree zero both sides are represented by the unit monomial.
      change
        (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
          (⟨Polynomial.monomial 0 (((x i : maximalIdeal R) : R) ^ 0),
              _⟩ :
            reesAlgebra (maximalIdeal R)) : grR) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (1 : reesAlgebra (maximalIdeal R))
      congr 1
      -- The degree-zero Rees monomial is literally the unit polynomial.
      apply Subtype.ext
      simp
  | succ n ih =>
      let xn : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
        ⟨((x i : maximalIdeal R) : R) ^ n, by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.pow_mem_pow (x i).2 n⟩
      let x1 : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R 1 :=
        ⟨((x i : maximalIdeal R) : R) ^ 1, by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
            pow_one] using (x i).2⟩
      have hmul :
          idealAssociatedGradedStageClass (maximalIdeal R) (n + 1)
              ⟨((x i : maximalIdeal R) : R) ^ (n + 1), by
                simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                  Ideal.mul_top] using Ideal.pow_mem_pow (x i).2 (n + 1)⟩ =
            idealAssociatedGradedStageClass (maximalIdeal R) n xn *
              idealAssociatedGradedDegreeOne (x i) := by
        -- Route correction: use stage multiplication directly, not repeated quotient-Rees
        -- unfolding in the main theorem.
        simpa [xn, x1, idealAssociatedGradedDegreeOne, pow_succ, pow_one] using
          idealAssociatedGradedStageClass_mul_local (maximalIdeal R) xn x1
      calc
        idealAssociatedGradedStageClass (maximalIdeal R) (n + 1)
            ⟨((x i : maximalIdeal R) : R) ^ (n + 1), by
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using Ideal.pow_mem_pow (x i).2 (n + 1)⟩ =
          idealAssociatedGradedStageClass (maximalIdeal R) n xn *
            idealAssociatedGradedDegreeOne (x i) := hmul
        _ = idealAssociatedGradedDegreeOne (x i) ^ n * idealAssociatedGradedDegreeOne (x i) := by
            rw [ih]
        _ = idealAssociatedGradedDegreeOne (x i) ^ (n + 1) := by
            rw [pow_succ]

/-- Helper for Lemma 10.106.1: before comparing with stage classes, the coefficient-free monomial
already evaluates to the expected product of degree-one parameter classes. -/
theorem associatedGradedPresentation_monomial_weight_eq_degree_one_prod {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) :
    associatedGradedPresentation x
        (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) (MvPolynomial.monomial e (1 : R))) =
      ∏ i : Fin d, idealAssociatedGradedDegreeOne (x i) ^ e i := by
  -- Route correction: isolate the coefficient-free `aeval_monomial` computation before attacking
  -- the quotient-Rees stage-class transport.
  rw [MvPolynomial.map_monomial]
  -- The evaluation map turns a monomial into the product of the chosen images of the variables.
  simpa [associatedGradedPresentation] using
    (MvPolynomial.aeval_monomial
      (g := fun i : Fin d ↦ idealAssociatedGradedDegreeOne (x i))
      (d := e) (r := ((Ideal.Quotient.mk (maximalIdeal R)) 1 : κ)))

/-- Helper for Lemma 10.106.1: over a finite subset of the chosen parameters, the corresponding
parameter monomial lies in the expected stage of the maximal-ideal filtration. -/
theorem parameter_monomial_mem_idealAssociatedGradedStage_finset {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) :
    ∀ s : Finset (Fin d),
      (∏ i ∈ s, (((x i : maximalIdeal R) : R) ^ e i)) ∈
        RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (∑ i ∈ s, e i) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- The empty parameter monomial is the unit in stage zero.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
  | @insert i s hi ih =>
      have hi_mem : (((x i : maximalIdeal R) : R) ^ e i) ∈ maximalIdeal R ^ e i :=
        Ideal.pow_mem_pow (x i).2 (e i)
      -- Multiplying an `e i`-stage parameter power with the monomial on `s` adds the stages.
      simpa [Finset.prod_insert, Finset.sum_insert, hi,
        RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
        pow_add] using Ideal.mul_mem_mul hi_mem ih

/-- Helper for Lemma 10.106.1: over a finite subset of the chosen parameters, the product of the
degree-one classes is the single stage class of the corresponding parameter monomial. -/
private theorem associatedGradedDegreeOne_finset_prod_eq_stageClass_aux {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) :
    ∀ s : Finset (Fin d),
      (∏ i ∈ s, idealAssociatedGradedDegreeOne (x i) ^ e i) =
        idealAssociatedGradedStageClass (maximalIdeal R) (∑ i ∈ s, e i)
          ⟨∏ i ∈ s, (((x i : maximalIdeal R) : R) ^ e i),
            parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e s⟩ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- In degree zero, both sides are represented by the unit Rees monomial.
      change
        (1 : grR) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (⟨Polynomial.monomial 0 1, _⟩ : reesAlgebra (maximalIdeal R))
      congr 1
  | @insert i s hi ih =>
      let xi : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (e i) :=
        ⟨(((x i : maximalIdeal R) : R) ^ e i), by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.pow_mem_pow (x i).2 (e i)⟩
      let xs : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (∑ j ∈ s, e j) :=
        ⟨∏ j ∈ s, (((x j : maximalIdeal R) : R) ^ e j),
          parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e s⟩
      have hmul :
          idealAssociatedGradedStageClass (maximalIdeal R) (e i + ∑ j ∈ s, e j)
              ⟨(((x i : maximalIdeal R) : R) ^ e i) *
                  ∏ j ∈ s, (((x j : maximalIdeal R) : R) ^ e j), by
                simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                  Ideal.mul_top, pow_add] using
                  Ideal.mul_mem_mul (Ideal.pow_mem_pow (x i).2 (e i))
                    (parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e s)⟩ =
            idealAssociatedGradedStageClass (maximalIdeal R) (e i) xi *
              idealAssociatedGradedStageClass (maximalIdeal R) (∑ j ∈ s, e j) xs := by
        -- Route correction: collapse products of degree-one classes by stage multiplication first,
        -- rather than unfolding the quotient-Rees multiplication in the main theorem.
        simpa [xi, xs] using
          idealAssociatedGradedStageClass_mul_local (maximalIdeal R) xi xs
      calc
        ∏ j ∈ insert i s, idealAssociatedGradedDegreeOne (x j) ^ e j =
          idealAssociatedGradedDegreeOne (x i) ^ e i *
            ∏ j ∈ s, idealAssociatedGradedDegreeOne (x j) ^ e j := by
              simp [hi]
        _ =
          idealAssociatedGradedStageClass (maximalIdeal R) (e i) xi *
            idealAssociatedGradedStageClass (maximalIdeal R) (∑ j ∈ s, e j) xs := by
              rw [← idealAssociatedGradedStageClass_parameter_pow_eq (R := R) x i, ih]
        _ =
          idealAssociatedGradedStageClass (maximalIdeal R) (e i + ∑ j ∈ s, e j)
            ⟨(((x i : maximalIdeal R) : R) ^ e i) *
                ∏ j ∈ s, (((x j : maximalIdeal R) : R) ^ e j), by
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top, pow_add] using
                Ideal.mul_mem_mul (Ideal.pow_mem_pow (x i).2 (e i))
                  (parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e s)⟩ := by
              symm
              exact hmul
        _ =
          idealAssociatedGradedStageClass (maximalIdeal R) (∑ j ∈ insert i s, e j)
            ⟨∏ j ∈ insert i s, (((x j : maximalIdeal R) : R) ^ e j),
              parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e
                (insert i s)⟩ := by
              simpa [idealAssociatedGradedStageClass, Finset.sum_insert, hi]

/-- Helper for Lemma 10.106.1: the product of the degree-one classes of the chosen parameters is
the single stage class of the corresponding parameter monomial. -/
theorem associatedGradedDegreeOne_finset_prod_eq_stageClass {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) :
    ∏ i : Fin d, idealAssociatedGradedDegreeOne (x i) ^ e i =
      idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i)
        ⟨∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
          parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ⟩ := by
  -- Specialize the finite-product transport to the full `Fin d` indexing set.
  exact associatedGradedDegreeOne_finset_prod_eq_stageClass_aux (R := R) x e Finset.univ

/-- Helper for Lemma 10.106.1: the coefficient-free monomial representative already maps to the
canonical stage class of the matching parameter monomial. -/
theorem associatedGradedPresentation_monomial_weight_eq_stageClass {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) :
    associatedGradedPresentation x
        (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) (MvPolynomial.monomial e (1 : R))) =
      idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i)
        ⟨∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
          parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ⟩ := by
  -- Compose the coefficient-free `aeval` computation with the new stage-class transport.
  rw [associatedGradedPresentation_monomial_weight_eq_degree_one_prod,
    associatedGradedDegreeOne_finset_prod_eq_stageClass]

/-- Helper for Lemma 10.106.1: residue-field coefficients in the presentation are degree-zero
stage classes in the quotient-Rees model. -/
theorem associatedGradedPresentation_constant_map_eq_stageClass_zero (r : R) :
    algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) =
      idealAssociatedGradedStageClass (maximalIdeal R) 0
        ⟨r, by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]⟩ := by
  -- Both sides are the quotient class of the same constant Rees polynomial.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (algebraMap R (reesAlgebra (maximalIdeal R)) r) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial 0 r, _⟩ : reesAlgebra (maximalIdeal R))
  congr 1

/-- Helper for Lemma 10.106.1: a finite sum of degree-`n` stage representatives still lies in
the `n`-th maximal-ideal power. -/
theorem idealAssociatedGradedStage_finset_sum_mem {α : Type*} {n : ℕ}
    (s : Finset α)
    (a : α → RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    Finset.sum s (fun i ↦ (a i : R)) ∈ maximalIdeal R ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hi_mem : (a i : R) ∈ maximalIdeal R ^ n := by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using (a i).2
      simpa [Finset.sum_insert, hi] using Ideal.add_mem (maximalIdeal R ^ n) hi_mem ih

/-- Helper for Lemma 10.106.1: two stage classes in the same degree add by adding their
representatives before passing to the quotient-Rees model. -/
private theorem idealAssociatedGradedStageClass_add_same_degree {n : ℕ}
    (a b : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨(a : R) + (b : R), by
          have ha_mem : (a : R) ∈ maximalIdeal R ^ n := by
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using a.2
          have hb_mem : (b : R) ∈ maximalIdeal R ^ n := by
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using b.2
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.add_mem (maximalIdeal R ^ n) ha_mem hb_mem⟩ =
      idealAssociatedGradedStageClass (maximalIdeal R) n a +
        idealAssociatedGradedStageClass (maximalIdeal R) n b := by
  -- Addition in the quotient-Rees model is induced by addition of the degree-`n` monomial
  -- representatives.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial n ((a : R) + (b : R)), _⟩ : reesAlgebra (maximalIdeal R)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        ((⟨Polynomial.monomial n (a : R), _⟩ : reesAlgebra (maximalIdeal R)) +
          (⟨Polynomial.monomial n (b : R), _⟩ : reesAlgebra (maximalIdeal R)))
  congr 1
  apply Subtype.ext
  simpa using map_add (Polynomial.monomial n) (a : R) (b : R)

/-- Helper for Lemma 10.106.1: padding a stage class by a zero degree on the left does not change
the quotient-Rees class. -/
theorem idealAssociatedGradedStageClass_zero_add {n : ℕ}
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedStageClass (maximalIdeal R) (0 + n)
        ⟨(a : R), by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using a.2⟩ =
      idealAssociatedGradedStageClass (maximalIdeal R) n a := by
  -- The Rees monomial representative is unchanged because `0 + n = n`.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial (0 + n) (a : R), _⟩ : reesAlgebra (maximalIdeal R)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
        (⟨Polynomial.monomial n (a : R), _⟩ : reesAlgebra (maximalIdeal R))
  congr 1
  apply Subtype.ext
  simp

/-- Helper for Lemma 10.106.1: a finite sum of degree-`n` stage classes is the stage class of the
sum of the representatives. -/
theorem idealAssociatedGradedStageClass_finset_sum_same_degree {α : Type*} {n : ℕ}
    (s : Finset α)
    (a : α → RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    Finset.sum s (fun i ↦ idealAssociatedGradedStageClass (maximalIdeal R) n (a i)) =
      idealAssociatedGradedStageClass (maximalIdeal R) n
        ⟨Finset.sum s (fun i ↦ (a i : R)), by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using idealAssociatedGradedStage_finset_sum_mem (R := R) s a⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is represented by the zero monomial in degree `n`.
      change
        (0 : grR) =
          idealAssociatedGradedStageClass (maximalIdeal R) n
            ⟨0, by
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using idealAssociatedGradedStage_finset_sum_mem (R := R) ∅ a⟩
      change
        Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (0 : reesAlgebra (maximalIdeal R)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra (maximalIdeal R))) (maximalIdeal R))
            (⟨Polynomial.monomial n 0, _⟩ : reesAlgebra (maximalIdeal R))
      congr 1
      apply Subtype.ext
      simp
  | @insert i s hi ih =>
      let tail :
          RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n :=
        ⟨Finset.sum s (fun j ↦ (a j : R)), by
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using idealAssociatedGradedStage_finset_sum_mem (R := R) s a⟩
      -- Collapse the first summand with the induction hypothesis, then use the two-term addition
      -- bridge in the fixed degree `n`.
      calc
        Finset.sum (insert i s)
            (fun j ↦ idealAssociatedGradedStageClass (maximalIdeal R) n (a j)) =
          idealAssociatedGradedStageClass (maximalIdeal R) n (a i) +
            idealAssociatedGradedStageClass (maximalIdeal R) n tail := by
              simp [Finset.sum_insert, hi, ih, tail]
        _ =
          idealAssociatedGradedStageClass (maximalIdeal R) n
            ⟨(a i : R) + (tail : R), by
              have hi_mem : (a i : R) ∈ maximalIdeal R ^ n := by
                simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                  Ideal.mul_top] using (a i).2
              have htail_mem : (tail : R) ∈ maximalIdeal R ^ n := by
                simpa [tail, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                  Ideal.mul_top] using tail.2
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using Ideal.add_mem (maximalIdeal R ^ n) hi_mem htail_mem⟩ := by
              symm
              exact idealAssociatedGradedStageClass_add_same_degree (R := R) (a i) tail
        _ =
          idealAssociatedGradedStageClass (maximalIdeal R) n
            ⟨Finset.sum (insert i s) (fun j ↦ (a j : R)), by
              simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using
                idealAssociatedGradedStage_finset_sum_mem (R := R) (insert i s) a⟩ := by
              simp [tail, Finset.sum_insert, hi]

/-- Helper for Lemma 10.106.1: a coefficient-bearing monomial in the polynomial presentation maps
to the canonical stage class of the matching weighted parameter monomial. -/
theorem associatedGradedPresentation_monomial_map_eq_stageClass {d : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) (r : R) :
    associatedGradedPresentation x
        (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) (MvPolynomial.monomial e r)) =
      idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i)
        ⟨r * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i), by
          have hprod :
              ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈ maximalIdeal R ^ (∑ i : Fin d, e i) := by
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
              using
                parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ
          simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
            using Ideal.mul_mem_left (maximalIdeal R ^ (∑ i : Fin d, e i)) r hprod⟩ := by
  let r0 : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R 0 :=
    ⟨r, by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]⟩
  let xe : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (∑ i : Fin d, e i) :=
    ⟨∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i),
      parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ⟩
  let coeffStage : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (∑ i : Fin d, e i) :=
    ⟨r * ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i), by
      have hprod :
          ∏ i : Fin d, (((x i : maximalIdeal R) : R) ^ e i) ∈ maximalIdeal R ^ (∑ i : Fin d, e i) := by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using parameter_monomial_mem_idealAssociatedGradedStage_finset (R := R) x e Finset.univ
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using Ideal.mul_mem_left (maximalIdeal R ^ (∑ i : Fin d, e i)) r hprod⟩
  have hmul :
      idealAssociatedGradedStageClass (maximalIdeal R) (0 + ∑ i : Fin d, e i)
          ⟨(r0 : R) * (xe : R), by
            have hxe : (xe : R) ∈ maximalIdeal R ^ (∑ i : Fin d, e i) := by
              simpa [xe, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using xe.2
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
            Ideal.mul_top] using
            Ideal.mul_mem_left (maximalIdeal R ^ (∑ i : Fin d, e i)) (r0 : R) hxe⟩ =
        idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 *
          idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i) xe := by
    -- Multiply the degree-zero coefficient class with the coefficient-free monomial class.
    simpa [r0, xe] using idealAssociatedGradedStageClass_mul_local (maximalIdeal R) r0 xe
  have hmap :
      associatedGradedPresentation x
          (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) (MvPolynomial.monomial e r)) =
        idealAssociatedGradedStageClass (maximalIdeal R) (0 + ∑ i : Fin d, e i)
          ⟨(coeffStage : R), by
            simpa [coeffStage, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using coeffStage.2⟩ := by
    calc
      associatedGradedPresentation x
          (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) (MvPolynomial.monomial e r)) =
        algebraMap κ grR ((Ideal.Quotient.mk (maximalIdeal R)) r) *
          ∏ i : Fin d, idealAssociatedGradedDegreeOne (x i) ^ e i := by
            rw [MvPolynomial.map_monomial]
            simpa [associatedGradedPresentation] using
              (MvPolynomial.aeval_monomial
                (g := fun i : Fin d ↦ idealAssociatedGradedDegreeOne (x i))
                (d := e) (r := ((Ideal.Quotient.mk (maximalIdeal R)) r : κ)))
      _ =
        idealAssociatedGradedStageClass (maximalIdeal R) 0 r0 *
          idealAssociatedGradedStageClass (maximalIdeal R) (∑ i : Fin d, e i) xe := by
            rw [associatedGradedPresentation_constant_map_eq_stageClass_zero,
              associatedGradedDegreeOne_finset_prod_eq_stageClass]
      _ =
        idealAssociatedGradedStageClass (maximalIdeal R) (0 + ∑ i : Fin d, e i)
          ⟨(r0 : R) * (xe : R), by
            have hxe : (xe : R) ∈ maximalIdeal R ^ (∑ i : Fin d, e i) := by
              simpa [xe, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
                Ideal.mul_top] using xe.2
            simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using
              Ideal.mul_mem_left (maximalIdeal R ^ (∑ i : Fin d, e i)) (r0 : R) hxe⟩ := by
            symm
            exact hmul
      _ =
        idealAssociatedGradedStageClass (maximalIdeal R) (0 + ∑ i : Fin d, e i)
          ⟨(coeffStage : R), by
            simpa [coeffStage, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
              Ideal.mul_top] using coeffStage.2⟩ := by
            simpa [coeffStage, r0, xe]
  -- The only remaining normalization is `0 + n = n` on the homogeneous degree.
  exact hmap.trans (idealAssociatedGradedStageClass_zero_add (R := R) coeffStage)

/-- Helper for Lemma 10.106.1: every element of `maximalIdeal R ^ n` is the value of a
degree-`n` homogeneous polynomial in a regular system of parameters. -/
theorem exists_isHomogeneous_polynomial_eval_eq_of_mem_maximalIdeal_pow {d n : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) {a : R}
    (ha : a ∈ maximalIdeal R ^ n) :
    ∃ p : MvPolynomial (Fin d) R, p.IsHomogeneous n ∧
      p.eval (fun i ↦ ((x i : maximalIdeal R) : R)) = a := by
  have hparam : parameterIdeal x = maximalIdeal R :=
    (IsLocalRing.isRegularSystemOfParameters_iff x).1 hx |>.2
  have hpow :
      (Ideal.span (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R))) ^ n =
        maximalIdeal R ^ n := by
    -- Passing from the chosen generators to `maximalIdeal R` commutes with taking powers.
    simpa [IsLocalRing.parameterIdeal_eq_span] using congrArg (fun I : Ideal R ↦ I ^ n) hparam
  have hspan :
      a ∈ (Ideal.span (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R))) ^ n := by
    rw [hpow]
    exact ha
  -- Rewrite `maximalIdeal R ^ n` through the chosen generators and use the homogeneous-span
  -- description of powers of a generated ideal.
  exact
    (Ideal.mem_span_pow_iff_exists_isHomogeneous
      (x := fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) (n := n) (y := a)).1 hspan

end
