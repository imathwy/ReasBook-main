import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_106_1 (from Chap10) -/
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
private theorem parameter_monomial_mem_idealAssociatedGradedStage_finset {d : ℕ}
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
private theorem idealAssociatedGradedStage_finset_sum_mem {α : Type*} {n : ℕ}
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
private theorem idealAssociatedGradedStageClass_zero_add {n : ℕ}
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

/-- Helper for Lemma 10.106.1: the textbook quotient
`maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)` agrees with the intrinsic quotient
`maximalIdeal R ^ n / maximalIdeal R · maximalIdeal R ^ n`. -/
private noncomputable def idealAssociatedGradedPiece_internal_quotient_equiv
    (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  -- Replace the intrinsic denominator by the next stage before passing to the quotient.
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_top_iff]
    change ((x : R) ∈ maximalIdeal R •
        RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) ↔
      ((x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (n + 1))
    rw [← mul_smul]
    rw [show maximalIdeal R * maximalIdeal R ^ n = maximalIdeal R ^ (n + 1) by
      rw [Ideal.mul_comm, ← pow_succ]])

/-- Helper for Lemma 10.106.1: the degree-`n` owner piece of `grR` identifies with the textbook
quotient `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
noncomputable abbrev idealAssociatedGradedRingGrade_equiv_piece_local (n : ℕ) :
    idealAssociatedGradedRingGrade (maximalIdeal R) n ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n

/-- Helper for Lemma 10.106.1: on a stage representative, the local owner-grade equivalence is the
obvious quotient class modulo the next maximal-ideal power. -/
theorem idealAssociatedGradedRingGrade_equiv_piece_local_apply_stage (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedRingGrade_equiv_piece_local (R := R) n
      ⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
        idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ =
        Submodule.Quotient.mk a := by
  -- This is the stage-level normal form needed later to compare polynomial evaluation with the
  -- textbook quotient `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`.
  simpa [idealAssociatedGradedRingGrade_equiv_piece_local] using
    idealAssociatedGradedRingGrade_equiv_piece_apply_stage (R := R) (I := maximalIdeal R) n a

/-- Helper for Lemma 10.106.1: the owner-grade/piece comparison is already linear over the
residue field. -/
noncomputable def idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (n : ℕ) :
    idealAssociatedGradedRingGrade (maximalIdeal R) n ≃ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  -- The owner grade now carries the transported `κ`-module structure, so the same additive
  -- equivalence becomes `κ`-linear without further transport data.
  (idealAssociatedGradedRingGrade_equiv_piece_local (R := R) n).toAddEquiv.linearEquiv κ

/-- Helper for Lemma 10.106.1: the residue-field-linear owner-grade/piece equivalence still sends
each stage class to its textbook quotient class. -/
theorem idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear_apply_stage (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
      ⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
        idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ =
        Submodule.Quotient.mk a := by
  -- The `κ`-linear packaging has the same underlying function as the original owner-grade
  -- equivalence, so the stage representative formula is unchanged.
  simpa [idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear] using
    idealAssociatedGradedRingGrade_equiv_piece_local_apply_stage (R := R) n a

/-- Helper for Lemma 10.106.1: the internal quotient model for
`maximalIdeal R ^ n / maximalIdeal R · maximalIdeal R ^ n` is already `κ`-linearly equivalent to
the textbook associated graded piece `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
private noncomputable def idealAssociatedGradedPiece_internal_quotient_equiv_quotient
    (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n := by
  -- The quotient `κ = R ⧸ maximalIdeal R` acts on both sides through the same additive model, so
  -- the existing additive equivalence upgrades directly to a `κ`-linear equivalence.
  simpa using
    (AddEquiv.linearEquiv
      (A := κ)
      ((idealAssociatedGradedPiece_internal_quotient_equiv (R := R) n).symm.toAddEquiv)).symm

/-- Helper for Lemma 10.106.1: after identifying the intrinsic quotient with the textbook quotient,
a stage class is still represented by the same quotient element. -/
private theorem idealAssociatedGradedPiece_internal_quotient_equiv_quotient_apply_stage
    (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedPiece_internal_quotient_equiv_quotient (R := R) n
      (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  -- The quotient equivalence only replaces the denominator by the equal next-stage submodule.
  rfl

/-- Helper for Lemma 10.106.1: the textbook associated graded piece has `κ`-length equal to the
Hilbert-Samuel `φ`-value of the maximal ideal. -/
private theorem idealAssociatedGradedPiece_length_over_quotient_eq_phi_local
    (n : ℕ) :
    Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      Ideal.hilbertSamuelPhi (maximalIdeal R) R n := by
  let Q :=
    RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
      ((maximalIdeal R) •
        (⊤ : Submodule R
          (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))
  have hlengthQ :
      Module.length R Q = Module.length κ Q :=
    Module.length_eq_of_surjective
      (R := κ) (S := R) (M := Q) Ideal.Quotient.mk_surjective
  -- Compare first with the internal quotient model used in the definition of `φ`, then forget the
  -- base ring from `R` to `κ`.
  calc
    Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        Module.length κ Q := by
          exact
            (idealAssociatedGradedPiece_internal_quotient_equiv_quotient n).symm.length_eq
    _ = Module.length R Q := by
          symm
          exact hlengthQ
    _ = Ideal.hilbertSamuelPhi (maximalIdeal R) R n := by
          rfl

/-- Helper for Lemma 10.106.1: the degree-`n` associated graded piece of the maximal-ideal
filtration is finite-dimensional over the residue field. -/
private theorem idealAssociatedGradedPiece_moduleFinite_local
    (n : ℕ) :
    Module.Finite κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  let I : Ideal R := maximalIdeal R
  let N : Submodule R R := RingTheory.Sequence.idealAssociatedGradedStage I R n
  let J : Submodule R R := RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1)
  have hJN : J ≤ N := by
    -- The adic filtration is decreasing, so the `(n + 1)`st stage sits inside the `n`th stage.
    simpa [I, N, J, RingTheory.Sequence.idealAssociatedGradedStage] using
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_succ n)) :
        ((maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R R)) ≤
          (maximalIdeal R ^ n • (⊤ : Submodule R R)))
  have hIdef : I.IsIdealOfDefinition := Ideal.maximalIdeal_isIdealOfDefinition
  have hlen_top :
      Module.length R (R ⧸ J) ≠ ⊤ := by
    exact
      (Module.length_ne_top_iff).2 <|
        by
          simpa [I, J, RingTheory.Sequence.idealAssociatedGradedStage] using
            Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
              (R := R) (M := R) I hIdef n
  have hlen_bottom :
      Module.length R (R ⧸ N) ≠ ⊤ := by
    cases n with
    | zero =>
        -- In degree zero the source quotient is `R ⧸ ⊤`, hence already the zero module.
        simpa [I, N, RingTheory.Sequence.idealAssociatedGradedStage]
    | succ n =>
        exact
          (Module.length_ne_top_iff).2 <|
            by
              simpa [I, N, RingTheory.Sequence.idealAssociatedGradedStage] using
                Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
                  (R := R) (M := R) I hIdef n
  have hdecomp :
      Module.length R (R ⧸ J) =
        Module.length R (R ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
    -- The short exact sequence
    -- `0 → N / J → R / J → R / N → 0`
    -- isolates the degree-`n` piece as the length difference of two Hilbert-Samuel quotients.
    simpa [N, J] using
      Ideal.length_quotient_eq_add_length_submodule_quotient_of_le
        (R := R) (M := R) hJN
  have hpiece_ne_top_R :
      Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) ≠ ⊤ := by
    intro htop
    have : Module.length R (R ⧸ J) = ⊤ := by
      rw [hdecomp, htop]
      simp
    exact hlen_top this
  have hpiece_ne_top_κ :
      Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) ≠ ⊤ := by
    -- The `κ`-length and the `R`-length agree on this quotient, so finiteness transfers across the
    -- residue-field scalar restriction.
    intro htop
    have : Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) = ⊤ := by
      have hcompare :
          Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
            Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
        have e :
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
              ((maximalIdeal R) •
                (⊤ : Submodule R
                  (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[κ]
              RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
          idealAssociatedGradedPiece_internal_quotient_equiv_quotient n
        calc
          Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
              Module.length κ
                (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                  ((maximalIdeal R) •
                    (⊤ : Submodule R
                      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
                exact e.symm.length_eq
          _ = Module.length R
                (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                  ((maximalIdeal R) •
                    (⊤ : Submodule R
                      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
                symm
                exact Module.length_eq_of_surjective
                  (R := κ) (S := R)
                  (M := RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                    ((maximalIdeal R) •
                      (⊤ : Submodule R
                        (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n))))
                  Ideal.Quotient.mk_surjective
          _ = Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
                exact (idealAssociatedGradedPiece_internal_quotient_equiv (R := R) n).length_eq
      simpa [hcompare] using htop
    exact hpiece_ne_top_R this
  have hfiniteLength :
      IsFiniteLength κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
    rw [← Module.length_ne_top_iff]
    exact hpiece_ne_top_κ
  have hNoeth :
      IsNoetherian κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  let _ : IsNoetherian κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    hNoeth
  infer_instance

/-- Helper for Lemma 10.106.1: each degree piece of the maximal-ideal associated graded ring has
dimension equal to the Hilbert-Samuel `φ`-value. -/
theorem idealAssociatedGradedPiece_finrank_eq_phi_local (n : ℕ) :
    Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
  let _ :
      Module.Finite κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    idealAssociatedGradedPiece_moduleFinite_local n
  have hlength :
      Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        Ideal.hilbertSamuelPhi (maximalIdeal R) R n :=
    idealAssociatedGradedPiece_length_over_quotient_eq_phi_local n
  have hlength_toNat :
      (Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)).toNat =
        Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
    simpa using congrArg ENat.toNat
      (Module.length_eq_finrank κ
        (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n))
  -- Once the degree piece is known to be finite-dimensional over `κ`, taking `ENat.toNat`
  -- converts the length identity into the desired finrank identity.
  calc
    Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        (Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)).toNat := by
          symm
          exact hlength_toNat
    _ = (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
          exact congrArg ENat.toNat hlength

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
  -- TODO for Lemma 10.106.1: compare the transported residue-field action on the owner grade with
  -- multiplication by degree-zero stage classes through the stage-class/piece identification.
  sorry

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
  simpa [associatedGradedPresentation_degree_piece_map,
    associatedGradedPresentation_degree_piece_to_grade,
    homogeneousPolynomialResidueFieldLift,
    associatedGradedPresentation_homogeneous_eval_eq_stageClass (R := R) x hq] using
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
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n := by
  let f := associatedGradedPresentation_degree_piece_map (R := R) x n
  -- Route correction: package the source degree piece through `quotKerEquivRange` before
  -- comparing with the textbook quotient model.
  exact f.quotKerEquivOfSurjective
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

/-- Helper for Lemma 10.106.1: the algebra kernel of the associated graded presentation is
already homogeneous, so the source Hilbert-function estimate can be applied to the actual kernel
ideal instead of its homogeneous hull. -/
private theorem associatedGradedPresentation_kernel_isHomogeneous {d : ℕ}
    (x : Fin d → maximalIdeal R) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) κ)
      (RingHom.ker (associatedGradedPresentation x).toRingHom) := by
  -- TODO for Lemma 10.106.1: use the owner decomposition component formula to show that every
  -- homogeneous projection of a kernel element still maps to zero.
  sorry

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

/-- After choosing a regular system of parameters `x`, one can realize the polynomial presentation
of the associated graded ring by sending `X i` to the degree-one class of `x i`. -/
private theorem associatedGradedPresentation_kernel_eq_bot {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : IsRegularSystemOfParameters x) :
    RingHom.ker (associatedGradedPresentation x).toRingHom = ⊥ := by
  -- TODO for Lemma 10.106.1: the direct graded-kernel pivot is now in place via
  -- `associatedGradedPresentation_kernel_homogeneousIdeal`. The remaining source-faithful step is
  -- to compare its quotient Hilbert function with `n ↦ φ_{maximalIdeal R}(n)` and then apply
  -- Lemma 10.58.10 to rule out a nonzero kernel.
  sorry

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

/-- Lemma 10.106.1: if `(R, maximalIdeal R, κ)` is a regular local ring of dimension `d`, then
the associated graded ring `⊕ n, maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)` is isomorphic to
the polynomial `κ`-algebra in `d` variables. -/
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
