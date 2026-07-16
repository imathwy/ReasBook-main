import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.PresentationDenominators

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: once the shifted relations have literal zero constant coefficient,
the zero-evaluation map descends to a retraction onto the coefficient ring, and its kernel is the
image of the variable ideal. -/
theorem shifted_zero_section_retraction_of_zero_constant_relations
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n m : ℕ}
    (πshift : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπshift : Function.Surjective πshift)
    (rels : Fin m → MvPolynomial (Fin n) A)
    (hspan : Ideal.span (Set.range rels) = RingHom.ker πshift.toRingHom)
    (hconst : ∀ j, MvPolynomial.constantCoeff (rels j) = 0) :
    ∃ σ : B →ₐ[A] A, Function.LeftInverse σ (algebraMap A B) ∧
      (∀ φ : MvPolynomial (Fin n) A,
        σ (πshift φ) = MvPolynomial.aeval (R := A) (0 : Fin n → A) φ) ∧
      RingHom.ker σ.toRingHom =
        Ideal.map πshift.toRingHom (MvPolynomial.idealOfVars (Fin n) A) := by
  let evalZero : MvPolynomial (Fin n) A →ₐ[A] A :=
    MvPolynomial.aeval (R := A) (0 : Fin n → A)
  have hker_le :
      RingHom.ker πshift.toRingHom ≤ MvPolynomial.idealOfVars (Fin n) A :=
    ker_le_idealOfVars_of_shifted_generators
      (π := πshift)
      (rels := rels)
      hspan
      hconst
  have hzero :
      ∀ φ : MvPolynomial (Fin n) A, φ ∈ RingHom.ker πshift.toRingHom → evalZero φ = 0 := by
    intro φ hφ
    have hφvar : φ ∈ MvPolynomial.idealOfVars (Fin n) A := hker_le hφ
    rw [← aeval_zero_ker_eq_idealOfVars_local (A := A) (d := n)] at hφvar
    simpa [evalZero, RingHom.mem_ker] using hφvar
  let σquot :
      (MvPolynomial (Fin n) A ⧸ RingHom.ker πshift.toRingHom) →ₐ[A] A :=
    Ideal.Quotient.liftₐ (RingHom.ker πshift.toRingHom) evalZero hzero
  let e :
      (MvPolynomial (Fin n) A ⧸ RingHom.ker πshift.toRingHom) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective hπshift
  let σ : B →ₐ[A] A := σquot.comp e.symm.toAlgHom
  have hσπ : ∀ φ : MvPolynomial (Fin n) A, σ (πshift φ) = evalZero φ := by
    intro φ
    dsimp [σ, e]
    have hσquot :
        σquot ((Ideal.quotientKerAlgEquivOfSurjective hπshift).symm (πshift φ)) =
          σquot (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) φ) := by
      exact congrArg σquot
        (Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := πshift) hπshift φ)
    calc
      σquot ((Ideal.quotientKerAlgEquivOfSurjective hπshift).symm (πshift φ))
          = σquot (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) φ) := hσquot
      _ = evalZero φ := by
            rfl
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro a
    -- Proof comment: the descended zero-evaluation map fixes coefficients, so it is a retraction
    -- of the canonical scalar map.
    have hCa : πshift (MvPolynomial.C a) = algebraMap A B a := by
      simp
    rw [← hCa]
    simpa [evalZero] using hσπ (MvPolynomial.C a)
  · intro φ
    -- Proof comment: the descended retraction computes on the presentation exactly by
    -- zero-evaluation on the polynomial side; later semilocal comparison will use this on the
    -- generators `X i`.
    simpa [evalZero] using hσπ φ
  · ext b
    constructor
    · intro hb
      obtain ⟨φ, rfl⟩ := hπshift b
      have hφ0 : evalZero φ = 0 := by
        have hcomp :
            σ (πshift φ) = 0 := by
          simpa [RingHom.mem_ker] using hb
        exact (hσπ φ).symm.trans hcomp
      have hφvar : φ ∈ MvPolynomial.idealOfVars (Fin n) A := by
        have hφker : φ ∈ RingHom.ker evalZero.toRingHom := by
          simpa [evalZero, RingHom.mem_ker] using hφ0
        rw [aeval_zero_ker_eq_idealOfVars_local (A := A) (d := n)] at hφker
        exact hφker
      exact Ideal.mem_map_of_mem πshift.toRingHom hφvar
    · intro hb
      rcases (Ideal.mem_map_iff_of_surjective πshift.toRingHom hπshift).mp hb with
        ⟨φ, hφvar, hφ⟩
      rw [← hφ, RingHom.mem_ker]
      have hφ0 : evalZero φ = 0 := by
        have hφker : φ ∈ RingHom.ker evalZero.toRingHom := by
          rw [aeval_zero_ker_eq_idealOfVars_local (A := A) (d := n)]
          exact hφvar
        simpa [evalZero, RingHom.mem_ker] using hφker
      exact (hσπ φ).trans hφ0

/-- Helper for Lemma 10.126.6: the kernel of a descended zero-section retraction is finitely
generated, because it is the image of the finitely generated variable ideal under the presentation
map. -/
theorem kernel_fg_of_zero_section_retraction
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n : ℕ} {σ : B →ₐ[A] A} {π : MvPolynomial (Fin n) A →ₐ[A] B}
    (hker :
      RingHom.ker σ.toRingHom =
        Ideal.map π.toRingHom (MvPolynomial.idealOfVars (Fin n) A)) :
    (RingHom.ker σ.toRingHom).FG := by
  -- Proof comment: the variable ideal of a finite polynomial ring is finitely generated, and
  -- mapping a finitely generated ideal along a ring homomorphism preserves finite generation.
  rw [hker]
  exact Ideal.FG.map (MvPolynomial.idealOfVars_fg (σ := Fin n) (R := A)) π.toRingHom

end
