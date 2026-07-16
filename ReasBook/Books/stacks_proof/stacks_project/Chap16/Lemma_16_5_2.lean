import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_138_17
import stacks_proof.stacks_project.Chap15.Lemma_15_94_10
import stacks_proof.stacks_project.Chap16.Lemma_16_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace Algebra

section

variable {R : Type u} {B : Type v} {Λ : Type w}
variable [CommRing R] [CommRing B] [CommRing Λ]
variable [Algebra R B] [Algebra R Λ]

/-- Helper for Lemma 16.5.2: if an algebra map kills each member of a finite generating family,
then it kills the ideal spanned by that family. -/
lemma spanRange_le_ker_of_generatorwise_zero {n : ℕ} {B' : Type*} [CommRing B']
    [Algebra R B'] (α : B →ₐ[R] B') (x : Fin n → B) (hx : ∀ i, α (x i) = 0) :
    Ideal.span (Set.range x) ≤ RingHom.ker α := by
  -- We reduce the span containment to the generators and then rewrite kernel membership pointwise.
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa [RingHom.mem_ker] using hx i

/-- Helper for Lemma 16.5.2: membership in the extended ideal `I B` can be written as a finite
`I`-linear combination inside `B`. -/
lemma exists_eq_sum_mul_of_mem_map_algebraMap (I : Ideal R) {x : B}
    (hx : x ∈ I.map (algebraMap R B)) :
    ∃ m, ∃ ε : Fin m → I, ∃ b : Fin m → B,
      x = ∑ k, algebraMap R B (ε k : R) * b k := by
  -- First rewrite the extended ideal as the module-theoretic smul `I • ⊤`.
  have hx' : x ∈ I • (⊤ : Submodule R B) := by
    simpa [Ideal.smul_top_eq_map] using hx
  -- Then induct on the concrete `I • ⊤` presentation and concatenate the resulting finite sums.
  refine Submodule.smul_induction_on hx' ?_ ?_
  · intro r hr m hm
    refine ⟨1, fun _ ↦ ⟨r, hr⟩, fun _ ↦ m, ?_⟩
    simpa [Algebra.smul_def]
  · intro y z hy hz
    rcases hy with ⟨m, ε, b, rfl⟩
    rcases hz with ⟨n, δ, c, rfl⟩
    refine ⟨m + n, Fin.addCases ε δ, Fin.addCases b c, ?_⟩
    simpa using
      (Fin.sum_univ_add
        (f := fun k : Fin (m + n) ↦
          algebraMap R B ((Fin.addCases ε δ k : I) : R) * Fin.addCases b c k)).symm

/-- Helper for Lemma 16.5.2: the explicit decomposition of a singleton generator and the
vanishing `φ h = 0` produce the flatness relation consumed by the equational criterion. -/
lemma zeroRelation_of_explicitSingletonData
    (I : Ideal R) (φ : B →ₐ[R] Λ) {m : ℕ} (ε : Fin m → I) (b : Fin m → B) (h : B)
    (hh : h = ∑ k, algebraMap R B (ε k : R) * b k) (hφh : φ h = 0) :
    ∑ k, (ε k : R) • φ (b k) = 0 := by
  -- Proof comment: rewrite the chosen decomposition through `φ` and interpret scalar action as
  -- multiplication by the image of the coefficient.
  calc
    ∑ k, (ε k : R) • φ (b k)
        = ∑ k, algebraMap R Λ (ε k : R) * φ (b k) := by
            simp [Algebra.smul_def]
    _ = φ (∑ k, algebraMap R B (ε k : R) * b k) := by
          simp [map_sum, map_mul]
    _ = φ h := by rw [hh]
    _ = 0 := hφh

/-- Helper for Lemma 16.5.2: the auxiliary polynomial relations evaluate to zero under the
chosen flatness witness. -/
lemma auxiliaryRelationEvalZero
    (φ : B →ₐ[R] Λ) {m n : ℕ} (a : Fin m → Fin n → R) (lam : Fin n → Λ) (b : Fin m → B)
    (hphi : ∀ i, φ (b i) = ∑ j, algebraMap R Λ (a i j) * lam j) :
    let _ : Algebra B Λ := φ.toAlgebra
    let rel : Fin m → MvPolynomial (Fin n) B := fun i ↦
      MvPolynomial.C (b i) -
        ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j
    let ψ0 : MvPolynomial (Fin n) B →ₐ[R] Λ := (MvPolynomial.aeval lam).restrictScalars R
    ∀ i, ψ0 (rel i) = 0 := by
  dsimp
  intro i
  letI : Algebra B Λ := φ.toAlgebra
  letI : IsScalarTower R B Λ := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    change (algebraMap R Λ) r = φ ((algebraMap R B) r)
    simpa [RingHom.algebraMap_toAlgebra] using φ.commutes r
  -- Proof comment: evaluating the auxiliary relation produces exactly the chosen equality `hphi`.
  calc
    ((MvPolynomial.aeval lam).restrictScalars R)
        (MvPolynomial.C (b i) -
          ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j)
        = φ (b i) - ∑ j, algebraMap R Λ (a i j) * lam j := by
            simp [RingHom.algebraMap_toAlgebra, map_sum, map_mul]
    _ = 0 := by rw [hphi i, sub_self]

/-- Helper for Lemma 16.5.2: once the auxiliary relations vanish under the polynomial evaluation
map, that map descends to the quotient by the relation ideal. -/
lemma auxiliaryQuotientDescends
    (φ : B →ₐ[R] Λ) {m n : ℕ} (a : Fin m → Fin n → R) (lam : Fin n → Λ) (b : Fin m → B)
    (hphi : ∀ i, φ (b i) = ∑ j, algebraMap R Λ (a i j) * lam j) :
    let _ : Algebra B Λ := φ.toAlgebra
    let rel : Fin m → MvPolynomial (Fin n) B := fun i ↦
      MvPolynomial.C (b i) -
        ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j
    let ψ0 : MvPolynomial (Fin n) B →ₐ[R] Λ := (MvPolynomial.aeval lam).restrictScalars R
    ∃ ψ :
        (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range rel)) →ₐ[R] Λ,
      ψ.comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range rel))) = ψ0 := by
  letI : Algebra B Λ := φ.toAlgebra
  letI : IsScalarTower R B Λ := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    change (algebraMap R Λ) r = φ ((algebraMap R B) r)
    simpa [RingHom.algebraMap_toAlgebra] using φ.commutes r
  let _ : Algebra B Λ := φ.toAlgebra
  let rel : Fin m → MvPolynomial (Fin n) B := fun i ↦
    MvPolynomial.C (b i) -
      ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j
  let ψ0 : MvPolynomial (Fin n) B →ₐ[R] Λ := (MvPolynomial.aeval lam).restrictScalars R
  have hrelZero : ∀ i, ψ0 (rel i) = 0 :=
    auxiliaryRelationEvalZero (R := R) (B := B) (Λ := Λ) φ a lam b hphi
  have hker : Ideal.span (Set.range rel) ≤ RingHom.ker ψ0.toRingHom := by
    -- Proof comment: the quotient ideal is generated by relations that already vanish under `ψ0`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simpa [RingHom.mem_ker] using hrelZero i
  refine
    ⟨Ideal.Quotient.liftₐ (R₁ := R) (I := Ideal.span (Set.range rel)) ψ0
      (fun z hz ↦ by simpa [RingHom.mem_ker] using hker hz), ?_⟩
  -- Proof comment: the descended map was defined by the canonical quotient lift.
  simpa using
    (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := Ideal.span (Set.range rel)) ψ0
      (fun z hz ↦ by simpa [RingHom.mem_ker] using hker hz))

/-- Helper for Lemma 16.5.2: once a chosen generator has been expanded as an explicit finite
`I`-linear combination, the source proof reduces the problem to one square-zero lifting
construction. -/
lemma exists_smooth_factorization_killing_singleton_of_square_zero_explicit
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) {m : ℕ} (ε : Fin m → I) (b : Fin m → B) (h : B)
    (hh : h = ∑ k, algebraMap R B (ε k : R) * b k) (hφh : φ h = 0) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      α h = 0 ∧ β.comp α = φ := by
  -- Route correction: the remaining blocker is exactly the source's principal-generator
  -- construction using the flat trivial-relation witness and Lemma `16.5.1`.
  have hzeroRelation : ∑ k, (ε k : R) • φ (b k) = 0 :=
    zeroRelation_of_explicitSingletonData (R := R) (B := B) (Λ := Λ) I φ ε b h hh hφh
  -- Proof comment: flatness now supplies the matrix data from the source proof in the canonical
  -- `Module.IsTrivialRelation` package.
  rcases Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (M := Λ) (f := fun k ↦ (ε k : R)) (x := fun k ↦ φ (b k)) hzeroRelation with
    ⟨n, a, lam, hphi, hrel⟩
  have hphiMul : ∀ i, φ (b i) = ∑ j, algebraMap R Λ (a i j) * lam j := by
    intro i
    -- Proof comment: rewrite the trivial-relation decomposition into the multiplicative form used
    -- by polynomial evaluation.
    simpa [Algebra.smul_def] using hphi i
  let rel : Fin m → MvPolynomial (Fin n) B := fun i ↦
    MvPolynomial.C (b i) -
      ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j
  let C : Type v := MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range rel)
  let _ : Algebra B Λ := φ.toAlgebra
  let ψ0 : MvPolynomial (Fin n) B →ₐ[R] Λ := (MvPolynomial.aeval lam).restrictScalars R
  obtain ⟨ψ, hψcomp⟩ :=
    auxiliaryQuotientDescends (R := R) (B := B) (Λ := Λ) φ a lam b hphiMul
  let mkRel : MvPolynomial (Fin n) B →ₐ[R] C :=
    Ideal.Quotient.mkₐ R (Ideal.span (Set.range rel))
  let qB : B →ₐ[R] C := IsScalarTower.toAlgHom R B C
  have hψqB : ψ.comp qB = φ := by
    -- Proof comment: on coefficients the descended quotient map still agrees with the original
    -- map `φ`.
    ext x
    have h :=
      congrArg (fun F : MvPolynomial (Fin n) B →ₐ[R] Λ => F (MvPolynomial.C x)) hψcomp
    change
      ψ
          ((Ideal.Quotient.mk
              (Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.C (b i) -
                    ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * MvPolynomial.X j)))
            (MvPolynomial.C x)) = φ x
    have hC : (MvPolynomial.aeval lam) (MvPolynomial.C x) = φ x := by
      simp [RingHom.algebraMap_toAlgebra]
    exact h.trans hC
  let _ : FinitePresentation R (MvPolynomial (Fin n) B) :=
    Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := B) (Fin n)
  have hrelFG : (Ideal.span (Set.range rel)).FG := by
    classical
    simpa using
      (Submodule.fg_span (R := MvPolynomial (Fin n) B) (s := Set.range rel)
        (Set.finite_range rel))
  let _ : FinitePresentation R C := Algebra.FinitePresentation.quotient hrelFG
  -- Proof comment: factor the auxiliary quotient map through a smooth quotient stage from
  -- Lemma `16.5.1`.
  obtain ⟨B₁, _, _, hB₁smooth, J₁, hJ₁le, _, f, g, hgf⟩ :=
    exists_smooth_quotient_factorization_of_square_zero
      (R := R) (A := C) (Λ := Λ) (I := I) (hSq := hSq) (hcolim := hcolim) ψ
  let mkJ : B₁ →ₐ[R] B₁ ⧸ J₁ := Ideal.Quotient.mkₐ R J₁
  have hJ₁sq : J₁ ^ 2 = ⊥ :=
    idealSquareZero_of_le_map_of_squareZero (R := R) (B := B₁) I J₁ hSq hJ₁le
  have hJ₁locnil : J₁.IsLocallyNilpotent :=
    ideal_isLocallyNilpotent_of_sq_eq_bot J₁ hJ₁sq
  -- Proof comment: smoothness of `B` over `R` lifts the map through the locally nilpotent
  -- quotient `B₁ ⧸ J₁`.
  obtain ⟨α, hαlift⟩ :=
    smooth_exists_lift_of_quotient_by_locally_nilpotent
      (R := R) (S := B) (A := B₁) J₁ hJ₁locnil (f.comp qB)
  let β : B₁ →ₐ[R] Λ := g.comp mkJ
  have hβα : β.comp α = φ := by
    -- Proof comment: the lifted map composes back to `φ` because both quotient stages already
    -- match the auxiliary quotient map `ψ`.
    calc
      β.comp α = g.comp (mkJ.comp α) := by
        simp [β, mkJ, AlgHom.comp_assoc]
      _ = g.comp (f.comp qB) := by rw [hαlift]
      _ = (g.comp f).comp qB := by rw [← AlgHom.comp_assoc]
      _ = ψ.comp qB := by rw [hgf]
      _ = φ := hψqB
  choose ξ hξ using fun j : Fin n ↦ Ideal.Quotient.mkₐ_surjective R J₁ (f (mkRel (MvPolynomial.X j)))
  letI : Algebra B B₁ := α.toAlgebra
  letI : IsScalarTower R B B₁ := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    change algebraMap R B₁ r = α ((algebraMap R B) r)
    simpa [RingHom.algebraMap_toAlgebra] using α.commutes r
  let σ : MvPolynomial (Fin n) B →ₐ[R] B₁ := (MvPolynomial.aeval ξ).restrictScalars R
  have hσeval :
      ∀ i, σ (rel i) = α (b i) - ∑ j, algebraMap R B₁ (a i j) * ξ j := by
    -- Proof comment: evaluating the defining relations in `B₁` produces the expected
    -- correction term `σ (rel i)`.
    intro i
    simp [σ, rel, RingHom.algebraMap_toAlgebra, map_sum, map_mul, map_sub]
  have hσrel : ∀ i, σ (rel i) ∈ J₁ := by
    -- Proof comment: reducing the evaluated relation modulo `J₁` recovers the original quotient
    -- relation in `C`, so the error term lies in `J₁`.
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hαbi : mkJ (α (b i)) = f (mkRel (MvPolynomial.C (b i))) := by
      have h := congrArg (fun F : B →ₐ[R] B₁ ⧸ J₁ => F (b i)) hαlift
      simpa [mkJ, qB, mkRel] using h
    have hcoeff :
        ∀ j, f (mkRel (MvPolynomial.C (algebraMap R B (a i j)))) =
          algebraMap R (B₁ ⧸ J₁) (a i j) := by
      intro j
      simpa [mkRel, RingHom.algebraMap_toAlgebra] using (f.comp mkRel).commutes (a i j)
    calc
      mkJ (σ (rel i))
          = f (mkRel (MvPolynomial.C (b i))) -
              ∑ j, f (mkRel (MvPolynomial.C (algebraMap R B (a i j)))) *
                f (mkRel (MvPolynomial.X j)) := by
        rw [hσeval i]
        rw [map_sub, hαbi, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul, hξ j, hcoeff j]
        simp
      _ = f (mkRel (rel i)) := by
        simp [rel, mkRel, map_sum, map_mul, map_sub]
      _ = 0 := by
        have hmem : rel i ∈ Ideal.span (Set.range rel) := Ideal.subset_span ⟨i, rfl⟩
        have hmkRel : mkRel (rel i) = 0 := by
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
        calc
          f (mkRel (rel i)) = f 0 := by rw [hmkRel]
          _ = 0 := map_zero f
  have hrelMul : ∀ j, ∑ k, algebraMap R B₁ ((ε k : R) * a k j) = 0 := by
    -- Proof comment: rewrite the flatness relation `hrel` into the multiplicative normal form
    -- needed after evaluating in `B₁`.
    intro j
    have h := congrArg (algebraMap R B₁) (hrel j)
    simpa [map_sum, map_mul, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hsumMain :
      ∑ k, algebraMap R B₁ (ε k : R) * (∑ j, algebraMap R B₁ (a k j) * ξ j) = 0 := by
    -- Proof comment: the main `ξ`-contribution vanishes exactly by the coefficient relations from
    -- flatness.
    calc
      ∑ k, algebraMap R B₁ (ε k : R) * (∑ j, algebraMap R B₁ (a k j) * ξ j)
          = ∑ k, ∑ j, algebraMap R B₁ ((ε k : R) * a k j) * ξ j := by
              simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
      _ = ∑ j, ∑ k, algebraMap R B₁ ((ε k : R) * a k j) * ξ j := by
            rw [Finset.sum_comm]
      _ = ∑ j, (∑ k, algebraMap R B₁ ((ε k : R) * a k j)) * ξ j := by
            simp_rw [Finset.sum_mul]
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j hj
            rw [hrelMul j, zero_mul]
  have hISq : (I.map (algebraMap R B₁)) ^ 2 = ⊥ := by
    calc
      (I.map (algebraMap R B₁)) ^ 2 = Ideal.map (algebraMap R B₁) (I ^ 2) := by
        rw [Ideal.map_pow]
      _ = ⊥ := by
        rw [hSq, Ideal.map_bot]
  have herrorZero : ∀ k, algebraMap R B₁ (ε k : R) * σ (rel k) = 0 := by
    -- Proof comment: every error term is a product of two elements from `I B₁`, hence square-zero.
    intro k
    have hcoeff : algebraMap R B₁ (ε k : R) ∈ I.map (algebraMap R B₁) :=
      Ideal.mem_map_of_mem (algebraMap R B₁) (ε k).property
    have htheta : σ (rel k) ∈ I.map (algebraMap R B₁) := hJ₁le (hσrel k)
    have hmul :
        algebraMap R B₁ (ε k : R) * σ (rel k) ∈ (I.map (algebraMap R B₁)) ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hcoeff htheta
    have hzero : algebraMap R B₁ (ε k : R) * σ (rel k) ∈ (⊥ : Ideal B₁) := by
      simpa [hISq] using hmul
    simpa using hzero
  have hsumError : ∑ k, algebraMap R B₁ (ε k : R) * σ (rel k) = 0 := by
    -- Proof comment: sum the termwise square-zero annihilation from `herrorZero`.
    refine Finset.sum_eq_zero ?_
    intro k hk
    exact herrorZero k
  refine ⟨B₁, inferInstance, inferInstance, hB₁smooth, α, β, ?_, hβα⟩
  -- Proof comment: expand `α h`, replace each `α (b i)` using the evaluated relation, and then
  -- kill the two resulting sums by `hrel` and `I² = 0`.
  calc
    α h = ∑ k, algebraMap R B₁ (ε k : R) * α (b k) := by
      rw [hh]
      simp [map_sum, map_mul]
    _ = ∑ k, algebraMap R B₁ (ε k : R) *
          ((∑ j, algebraMap R B₁ (a k j) * ξ j) + σ (rel k)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hdecomp :
                α (b k) =
                  (∑ j, algebraMap R B₁ (a k j) * ξ j) + σ (rel k) := by
              calc
                α (b k)
                    = (α (b k) - ∑ j, algebraMap R B₁ (a k j) * ξ j) +
                        ∑ j, algebraMap R B₁ (a k j) * ξ j := by
                          abel
                _ = σ (rel k) + ∑ j, algebraMap R B₁ (a k j) * ξ j := by
                      rw [hσeval k]
                _ = (∑ j, algebraMap R B₁ (a k j) * ξ j) + σ (rel k) := by
                      ac_rfl
            rw [hdecomp]
    _ = (∑ k, algebraMap R B₁ (ε k : R) * (∑ j, algebraMap R B₁ (a k j) * ξ j)) +
          ∑ k, algebraMap R B₁ (ε k : R) * σ (rel k) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
    _ = 0 := by
          rw [hsumMain, hsumError]
          simp

/-- Helper for Lemma 16.5.2: the singleton case is reduced to the explicit source-style
coefficient expansion inside `I B`. -/
lemma exists_smooth_factorization_killing_singleton_of_square_zero
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (h : B) (hhI : h ∈ I.map (algebraMap R B)) (hφh : φ h = 0) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      α h = 0 ∧ β.comp α = φ := by
  -- Expand the chosen generator once so the remaining proof can follow the source verbatim.
  obtain ⟨m, ε, b, hh⟩ := exists_eq_sum_mul_of_mem_map_algebraMap (R := R) (B := B) I hhI
  exact exists_smooth_factorization_killing_singleton_of_square_zero_explicit
    (R := R) (B := B) (Λ := Λ) (I := I) (hSq := hSq) (hcolim := hcolim)
    (φ := φ) ε b h hh hφh

/-- Helper for Lemma 16.5.2: the finite-family induction is quantified over the source algebra,
so the recursive step can run on the intermediate smooth algebra produced by the singleton case. -/
lemma existsSmoothFactorizationKillingSpanRangeOfSquareZeroAux (n : ℕ)
    [Module.Flat R Λ] (I : Ideal R) (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    :
    ∀ {S : Type (max u v w)} [CommRing S] [Algebra R S] [Smooth R S]
      (φ : S →ₐ[R] Λ) (x : Fin n → S),
      (∀ i, x i ∈ I.map (algebraMap R S)) →
      (∀ i, φ (x i) = 0) →
      ∃ (S' : Type (max u v w)) (_ : CommRing S') (_ : Algebra R S') (_ : Smooth R S')
        (α : S →ₐ[R] S') (β : S' →ₐ[R] Λ),
        (∀ i, α (x i) = 0) ∧ β.comp α = φ := by
  induction n with
  | zero =>
      intro S _ _ _ φ x hxI hφx
      refine ⟨S, inferInstance, inferInstance, inferInstance, AlgHom.id R S, φ, ?_, rfl⟩
      -- Proof comment: the empty family has no generators to kill, so the identity factorization
      -- already closes the base case.
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro S _ _ _ φ x hxI hφx
      -- Proof comment: split the family into its last generator and the truncated prefix, kill the
      -- last generator first, and recurse on the transported prefix in the intermediate smooth
      -- algebra.
      obtain ⟨S₁, _, _, hS₁smooth, α₁, β₁, hxα₁, hcomp₁⟩ :=
        exists_smooth_factorization_killing_singleton_of_square_zero
          (R := R) (B := S) (Λ := Λ) (I := I) (hSq := hSq) (hcolim := hcolim)
          (φ := φ) (h := x (Fin.last n)) (hhI := hxI (Fin.last n)) (hφh := hφx (Fin.last n))
      have hxI₁ : ∀ i : Fin n, α₁ ((Fin.init x) i) ∈ I.map (algebraMap R S₁) := by
        intro i
        have hmem :
            α₁ ((Fin.init x) i) ∈ (I.map (algebraMap R S)).map α₁.toRingHom :=
          Ideal.mem_map_of_mem α₁.toRingHom (by simpa [Fin.init_def] using hxI i.castSucc)
        rw [Ideal.map_map] at hmem
        simpa [RingHom.algebraMap_toAlgebra] using hmem
      have hφ₁ : ∀ i : Fin n, β₁ (α₁ ((Fin.init x) i)) = 0 := by
        intro i
        -- Proof comment: the recursive family is still killed because `β₁.comp α₁ = φ`.
        change (β₁.comp α₁) ((Fin.init x) i) = 0
        rw [hcomp₁]
        simpa [Fin.init_def] using hφx i.castSucc
      obtain ⟨S₂, _, _, hS₂smooth, α₂, β₂, hxα₂, hcomp₂⟩ :=
        ih (S := S₁) (φ := β₁) (x := fun i ↦ α₁ ((Fin.init x) i)) hxI₁ hφ₁
      refine ⟨S₂, inferInstance, inferInstance, hS₂smooth, α₂.comp α₁, β₂, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · -- Proof comment: the head step already kills the distinguished last generator.
          change α₂ (α₁ (x (Fin.last n))) = 0
          rw [hxα₁]
          simp
        · intro j
          -- Proof comment: every prefix generator is killed by the recursive factorization.
          simpa [AlgHom.comp_apply, Fin.init_def] using hxα₂ j
      · -- Proof comment: compose the two factorization stages.
        calc
          β₂.comp (α₂.comp α₁) = (β₂.comp α₂).comp α₁ := by rw [← AlgHom.comp_assoc]
          _ = β₁.comp α₁ := by rw [hcomp₂]
          _ = φ := hcomp₁

/-- Helper for Lemma 16.5.2: finite-family version of the square-zero factorization statement.
Killing an arbitrary finitely generated ideal reduces to killing the generators one by one. -/
lemma exists_smooth_factorization_killing_spanRange_of_square_zero {n : ℕ}
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (x : Fin n → B)
    (hxI : ∀ i, x i ∈ I.map (algebraMap R B))
    (hφx : ∀ i, φ (x i) = 0) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      (∀ i, α (x i) = 0) ∧ β.comp α = φ := by
  let B0 := ULift.{max u w, v} B
  let e : B0 ≃ₐ[R] B := (ULift.algEquiv : B0 ≃ₐ[R] B)
  let φ0 : B0 →ₐ[R] Λ := φ.comp e.toAlgHom
  let x0 : Fin n → B0 := fun i ↦ e.symm (x i)
  letI : Smooth R B0 := Smooth.of_equiv e.symm
  have hx0I : ∀ i, x0 i ∈ I.map (algebraMap R B0) := by
    intro i
    -- Proof comment: transport `I B`-membership across the canonical `ULift` algebra equivalence.
    have hmem : e.symm (x i) ∈ (I.map (algebraMap R B)).map e.symm.toRingHom :=
      Ideal.mem_map_of_mem e.symm.toRingHom (hxI i)
    rw [Ideal.map_map] at hmem
    simpa [x0, RingHom.algebraMap_toAlgebra] using hmem
  have hφ0x0 : ∀ i, φ0 (x0 i) = 0 := by
    intro i
    -- Proof comment: the lifted generators are definitionally the same family through `e`.
    simpa [φ0, x0] using hφx i
  obtain ⟨B', _, _, hB'smooth, α0, β, hxα0, hcomp0⟩ :=
    existsSmoothFactorizationKillingSpanRangeOfSquareZeroAux.{u, max u v w, w}
      (R := R) (Λ := Λ) (S := B0) n I hSq hcolim φ0 x0 hx0I hφ0x0
  let α : B →ₐ[R] B' := α0.comp e.symm.toAlgHom
  refine ⟨B', inferInstance, inferInstance, hB'smooth, α, β, ?_, ?_⟩
  · intro i
    -- Proof comment: transport the generatorwise vanishing back from the lifted source algebra.
    simpa [α, x0] using hxα0 i
  · -- Proof comment: composing with the inverse `ULift` equivalence returns the original map `φ`.
    calc
      β.comp α = (β.comp α0).comp e.symm.toAlgHom := by
        simp [α, AlgHom.comp_assoc]
      _ = φ0.comp e.symm.toAlgHom := by rw [hcomp0]
      _ = φ := by
        ext b
        simp [φ0]

/- Domain-style sampling for smooth factorizations killing a finitely generated ideal:
* primary domain: commutative algebra of smooth `R`-algebras, square-zero ideals, and filtered
  colimits of smooth quotient algebras;
* sampled owner declarations:
  `Smooth R B`,
  `(algebraMap (R ⧸ I) _).IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_of_singularIdeal_map_eq_top`;
* best owner abstraction: this item is a source-facing bridge theorem, not a new packaged owner.
  Its canonical surface is the direct existence of a smooth factorization `B ─α→ B' ─β→ Λ`
  subject to the intrinsic ideal-theoretic conditions on `J`.

Source/core/bridge triage:
* `source-facing`: the factorization statement killing a finitely generated ideal `J ⊆ IB`;
* `core/canonical`: `Smooth`, `Ideal`, quotient algebras, and
  `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the comparison maps `α` and `β` exhibiting the refined factorization.

Primitive input data are exactly `J`, the inclusion `J ≤ I.map (algebraMap R B)`, finite
generation of `J`, and the annihilation condition `J ≤ RingHom.ker φ`. The factorization
maps are derived output data, so a wrapper structure would only duplicate the owner declarations
already present upstream in Chapter 16.
-/

-- Proof sketch: argue by induction on the number of generators of `J`, reducing to the principal
-- case. For a generator `h = ∑ εᵢ bᵢ` with `εᵢ ∈ I`, apply the equational criterion of flatness to
-- the relation `∑ εᵢ φ(bᵢ) = 0` in the flat `R`-algebra `Λ`, build the auxiliary algebra
-- `C = B[x₁, …, xₘ]/(bᵢ - ∑ aᵢⱼ xⱼ)`, factor `C → Λ` through Lemma `16.5.1`, and then lift
-- `B → C → B' ⧸ J'` to `α : B → B'` by smoothness of `B` over `R`. The imposed relations and the
-- square-zero hypothesis `I² = 0` force `α` to kill `J`.
/-- Lemma 16.5.2: let `R → Λ` be a flat ring map, let `I ⊂ R` be a square-zero ideal, and assume
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras. If `φ : B → Λ` is an `R`-algebra map
with `B` smooth over `R`, and if `J ⊆ IB` is a finitely generated ideal killed by `φ`, then `φ`
factors as `B ─α→ B' ─β→ Λ` with `B'` smooth over `R` and with `α` killing `J`. -/
@[stacks 07CL]
theorem exists_smooth_factorization_killing_ideal_of_square_zero
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : J ≤ RingHom.ker φ) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      J ≤ RingHom.ker α ∧ β.comp α = φ := by
  -- We first choose an explicit finite generating family for `J` and rewrite the goal in terms of
  -- those generators.
  obtain ⟨n, x, hxJsub⟩ := (Submodule.fg_iff_exists_fin_generating_family).1 hJfg
  have hxJ : Ideal.span (Set.range x) = J := by
    simpa [Ideal.submodule_span_eq] using hxJsub
  have hxI : ∀ i, x i ∈ I.map (algebraMap R B) := by
    intro i
    have hx_mem_span : x i ∈ Ideal.span (Set.range x) := Ideal.subset_span ⟨i, rfl⟩
    have hx_mem_J : x i ∈ J := by
      simpa [hxJ] using hx_mem_span
    exact hJ hx_mem_J
  have hφx : ∀ i, φ (x i) = 0 := by
    intro i
    have hx_mem_span : x i ∈ Ideal.span (Set.range x) := Ideal.subset_span ⟨i, rfl⟩
    have hx_mem_J : x i ∈ J := by
      simpa [hxJ] using hx_mem_span
    have hx_mem_ker : x i ∈ RingHom.ker φ := hφJ hx_mem_J
    simpa [RingHom.mem_ker] using hx_mem_ker
  -- The remaining proof is the finite-family factorization theorem, after which the kernel
  -- containment follows immediately from the span-to-kernel bridge above.
  obtain ⟨B', _, _, hB'smooth, α, β, hxα, hcomp⟩ :=
    exists_smooth_factorization_killing_spanRange_of_square_zero
      (I := I) (hSq := hSq) (hcolim := hcolim) (φ := φ) x hxI hφx
  refine ⟨B', inferInstance, inferInstance, hB'smooth, α, β, ?_, hcomp⟩
  simpa [hxJ] using spanRange_le_ker_of_generatorwise_zero (R := R) α x hxα

end

end Algebra
