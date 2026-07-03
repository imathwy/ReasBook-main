import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_126_6 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

/-- Helper for Lemma 10.126.6: a bijective local ring map `R_𝔭 → S_𝔮` makes `S_𝔮`
quasi-finite over `R`. -/
private theorem quasiFiniteAt_of_bijective_localRingHom
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    Algebra.QuasiFiniteAt R q := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) hq.over).toAlgebra
  have hlocal' :
      Function.Bijective
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    simpa [RingHom.algebraMap_toAlgebra] using hlocal
  let e : Localization.AtPrime p ≃ₐ[Localization.AtPrime p] Localization.AtPrime q :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hlocal'
  let eR : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime p := e.symm.restrictScalars R
  -- The target local ring is already a localization of `R`, hence quasi-finite over `R`.
  exact (Algebra.QuasiFinite.iff_of_algEquiv (R := R) eR).mpr inferInstance

/-- Helper for Lemma 10.126.6: any `A`-algebra which is already `A` isomorphic admits the required
product decomposition with a trivial complementary factor. -/
private theorem exists_trivial_product_factor_of_algEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (e : B ≃ₐ[A] A) :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  let C : Type w := ULift.{w, 0} PUnit
  let eProd : A ≃ₐ[A] (A × C) :=
    AlgEquiv.ofBijective (Algebra.ofId A (A × C)) <| by
      constructor
      · intro x y hxy
        exact congrArg Prod.fst hxy
      · intro x
        refine ⟨x.1, ?_⟩
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
  refine ⟨C, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans eProd⟩

/-- Helper for Lemma 10.126.6: if the away map `R_f → S_f` is bijective, then the desired product
decomposition follows immediately by taking a trivial complementary factor. -/
private theorem exists_product_factor_of_bijective_awayMap
    (f : R) (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
      Nonempty
        (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
          (Localization.Away f × C)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  have hbij' :
      Function.Bijective
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) := by
    simpa [RingHom.algebraMap_toAlgebra] using hbij
  let e : Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f] Localization.Away f :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij').symm
  -- Once the localized algebra is actually `R_f`, the requested product is `R_f × 0`.
  exact exists_trivial_product_factor_of_algEquiv (A := Localization.Away f) e

/-- Helper for Lemma 10.126.6: if a basic-open map `S'_r → S_r` is bijective and `r` avoids the
target prime `q`, then the induced map on the prime localizations `S'_{q'} → S_q` is bijective. -/
private theorem subalgebra_localRingHom_bijective_of_awayMap_bijective
    (S' : Subalgebra R S) (r : S') (hrq : r.1 ∉ q)
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) :
    let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
    Function.Bijective (Localization.localRingHom q' q S'.val.toRingHom rfl) := by
  let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
  letI : q'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom q
  letI : q.LiesOver q' := by
    refine ⟨rfl⟩
  have hsat : S'.saturation (q.primeCompl ⊓ S'.toSubmonoid) (by simp) = ⊤ := by
    -- Proof comment: surjectivity of `S'_r → S_r` says every element of `S` becomes an element of
    -- `S'` after multiplying by a power of `r`, which is exactly the saturation criterion.
    rw [← top_le_iff]
    intro x hx
    obtain ⟨b, n, hb⟩ := (Localization.awayMap_surjective_iff).mp hr.2 x
    refine ⟨r.1 ^ n, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact q.primeCompl.pow_mem (show r.1 ∈ q.primeCompl from hrq) n
      · exact (show r.1 ^ n ∈ S' from S'.pow_mem r.2 n)
    · simpa [smul_eq_mul] using (show r.1 ^ n * x ∈ S' from hb.symm ▸ b.2)
  -- Proof comment: the saturation-top criterion is the canonical bridge from a basic-open
  -- isomorphism to a bijection on the stalk at `q`.
  simpa [q'] using
    (Localization.localRingHom_bijective_of_saturated_inf_eq_top
      (S := S) (P := q) (s := S') (p := q') hsat)

/-- Helper for Lemma 10.126.6: the original local isomorphism `R_p → S_q` factors through the
finite subalgebra neighborhood `S'`, so `R_p → S'_{q'}` is already bijective. -/
private theorem finite_subalgebra_localRingHom_bijective_of_quasiFinite_neighborhood
    (hq : q.LiesOver p)
    (S' : Subalgebra R S) (r : S') (hrq : r.1 ∉ q)
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r))
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
    Function.Bijective
      (Localization.localRingHom p q' (algebraMap R S')
        (by simpa [q', Ideal.comap_comap] using hq.over)) := by
  let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
  letI : q'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom q
  have hq' : p = Ideal.comap (algebraMap R S') q' := by
    simpa [q', Ideal.comap_comap] using hq.over
  have hsub :
      Function.Bijective (Localization.localRingHom q' q S'.val.toRingHom rfl) :=
    subalgebra_localRingHom_bijective_of_awayMap_bijective
      (S' := S') (q := q) r hrq hr
  have hcomp :
      Localization.localRingHom p q (algebraMap R S) hq.over =
        (Localization.localRingHom q' q S'.val.toRingHom rfl).comp
          (Localization.localRingHom p q' (algebraMap R S') hq') := by
    -- Proof comment: localizing along `R → S' → S` is governed by the canonical
    -- `Localization.localRingHom_comp` theorem.
    simpa [q', hq', RingHom.comp_assoc] using
      (Localization.localRingHom_comp
        (I := p)
        (J := q')
        (K := q)
        (f := algebraMap R S')
        (hIJ := hq')
        (g := S'.val.toRingHom)
        (hJK := rfl))
  -- Proof comment: once the second localization step is bijective, bijectivity of the composite
  -- is equivalent to bijectivity of the first step.
  rw [hcomp] at hlocal
  exact (Function.Bijective.of_comp_iff' hsub _).mp hlocal

/-- Helper for Lemma 10.126.6: once a localized retraction has idempotent kernel, the algebra
splits as the base factor times the complementary quotient. -/
private theorem away_product_decomposition_of_idempotent_kernel_retraction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hσ : Function.LeftInverse σ (algebraMap A B))
    {e : B} (he : IsIdempotentElem e)
    (hker : RingHom.ker σ.toRingHom = Ideal.span ({e} : Set B)) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  let C : Type v := B ⧸ Ideal.span ({1 - e} : Set B)
  let quotientEquiv : (B ⧸ Ideal.span ({e} : Set B)) ≃ₐ[A] A :=
    -- Proof comment: rewrite the quotient by the displayed kernel and then apply the first
    -- isomorphism theorem for the retraction `σ`.
    (Ideal.quotientEquivAlgOfEq (R₁ := A) hker.symm).trans <|
      Ideal.quotientKerAlgEquivOfRightInverse (f := σ) (g := algebraMap A B) hσ
  let splitEquiv :
      B ≃ₐ[A] ((B ⧸ Ideal.span ({e} : Set B)) × C) :=
    -- Proof comment: the complementary idempotents `e` and `1 - e` give the standard product
    -- decomposition of `B`.
    AlgEquiv.prodQuotientOfIsIdempotentElem A he he.one_sub (by simp) (by
      rw [mul_sub, mul_one, he.eq, sub_self])
  let finalEquiv : B ≃ₐ[A] (A × C) :=
    splitEquiv.trans <|
      AlgEquiv.prodCongr quotientEquiv (AlgEquiv.refl : C ≃ₐ[A] C)
  refine ⟨C, inferInstance, inferInstance, ⟨finalEquiv⟩⟩

/-- Helper for Lemma 10.126.6: a pure finitely generated ideal of a commutative ring is generated
by an idempotent element. This is the exact algebraic closing step used after the second shrink. -/
private theorem exists_idempotent_generator_of_pure_finitely_generated_ideal
    {A : Type*} [CommRing A] (I : Ideal A)
    (hPure : I.Pure) (hfg : I.FG) :
    ∃ e : A, IsIdempotentElem e ∧ I = Ideal.span ({e} : Set A) := by
  letI : I.Pure := hPure
  -- Proof comment: purity gives ideal idempotence, and finite generation upgrades ideal
  -- idempotence to generation by one idempotent element.
  have hidem : IsIdempotentElem I := Ideal.isIdempotentElem_of_pure I
  exact (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem

/-- Helper for Lemma 10.126.6: once the kernel of a retraction is known to be pure and finitely
generated, it is generated by an idempotent element of the source ring. -/
private theorem exists_idempotent_generator_of_pure_finitely_generated_kernel
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hkerPure : (RingHom.ker σ.toRingHom).Pure)
    (hkerFg : (RingHom.ker σ.toRingHom).FG) :
    ∃ e : B, IsIdempotentElem e ∧
      RingHom.ker σ.toRingHom = Ideal.span ({e} : Set B) := by
  -- Proof comment: specialize the pure-plus-finitely-generated ideal criterion to the kernel ideal
  -- of the retraction produced after the second shrink.
  simpa using
    exists_idempotent_generator_of_pure_finitely_generated_ideal
      (I := RingHom.ker σ.toRingHom) hkerPure hkerFg

/-- Helper for Lemma 10.126.6: a finite family of elements of `R_𝔭` admits one common
denominator away from `p`. -/
private theorem exists_notMem_and_common_denominator_atPrime
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Localization.AtPrime p) :
    ∃ (f : R) (_ : f ∉ p) (a : ι → R), ∀ i,
      algebraMap R (Localization.AtPrime p) f * x i =
        algebraMap R (Localization.AtPrime p) (a i) := by
  choose num den hden using fun i ↦
    IsLocalization.exists_mk'_eq p.primeCompl (x i)
  let fCompl : p.primeCompl := ⟨∏ i, (den i : R), by
    -- Proof comment: the product of finitely many denominators still avoids the prime `p`.
    simpa using p.primeCompl.prod_mem fun i _ ↦ (den i).2⟩
  let a : ι → R := fun i ↦ num i * ∏ j ∈ ({i}ᶜ : Finset ι), (den j : R)
  refine ⟨(fCompl : R), fCompl.2, a, ?_⟩
  intro i
  -- Proof comment: rewrite `x i` with its chosen denominator and absorb all other denominators
  -- into a single common numerator.
  calc
    algebraMap R (Localization.AtPrime p) (fCompl : R) * x i
        = algebraMap R (Localization.AtPrime p) (fCompl : R) *
            IsLocalization.mk' (Localization.AtPrime p) (num i) (den i) := by
              rw [hden i]
    _ = IsLocalization.mk' (Localization.AtPrime p) ((fCompl : R) * num i)
          ((1 : p.primeCompl) * den i) := by
            rw [← IsLocalization.mk'_one (M := p.primeCompl) (S := Localization.AtPrime p)
              (x := (fCompl : R))]
            exact
              (IsLocalization.mk'_mul
                (M := p.primeCompl)
                (S := Localization.AtPrime p)
                (x₁ := (fCompl : R))
                (x₂ := num i)
                (y₁ := (1 : p.primeCompl))
                (y₂ := den i)).symm
    _ = IsLocalization.mk' (Localization.AtPrime p) ((fCompl : R) * num i) (den i) := by
          simp
    _ = algebraMap R (Localization.AtPrime p) (a i) := by
          rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]
          congr 1
          dsimp [a]
          rw [show (fCompl : R) = ∏ j, (den j : R) by rfl]
          rw [Fintype.prod_eq_prod_compl_mul i fun j ↦ (den j : R)]
          ring

/-- Helper for Lemma 10.126.6: evaluating a finite polynomial algebra at the zero tuple kills
exactly the ideal generated by the variables. This is the source-side kernel computation for the
retraction `S_f → R_f` after shifting the presentation variables. -/
private theorem aeval_zero_ker_eq_idealOfVars_local
    {A : Type*} [CommRing A] {d : ℕ} :
    RingHom.ker (MvPolynomial.aeval (R := A) (0 : Fin d → A)).toRingHom =
      MvPolynomial.idealOfVars (Fin d) A := by
  ext φ
  constructor
  · intro hφ
    -- Proof comment: vanishing at the zero tuple forces the constant coefficient to vanish, so
    -- every monomial in the support uses at least one variable and hence lies in the variable
    -- ideal.
    rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hconst : MvPolynomial.constantCoeff φ = 0 := by
      simpa [RingHom.mem_ker, MvPolynomial.aeval_zero] using hφ
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      have hmem : 0 ∈ φ.support := by
        simpa [hm0] using hm
      exact (MvPolynomial.mem_support_iff.mp hmem) <|
        by simpa [MvPolynomial.constantCoeff_eq] using hconst
    obtain ⟨i, hi⟩ : ∃ i : Fin d, m i ≠ 0 := by
      by_contra h
      apply hm_ne_zero
      ext i
      by_contra hmi
      exact h ⟨i, hmi⟩
    exact ⟨i, Set.mem_univ _, hi⟩
  · intro hφ
    -- Proof comment: membership in the variable ideal excludes the constant monomial, so the
    -- zero evaluation indeed lands in the kernel.
    rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image] at hφ
    have hnot : (0 : Fin d →₀ ℕ) ∉ φ.support := by
      intro h0
      rcases hφ 0 h0 with ⟨i, -, hi⟩
      exact hi (by simp)
    have hcoeff : φ.coeff 0 = 0 := Finsupp.notMem_support_iff.mp hnot
    simpa [RingHom.mem_ker, MvPolynomial.aeval_zero, MvPolynomial.constantCoeff_eq] using hcoeff

/-- Helper for Lemma 10.126.6: once a shifted finite family spans the presentation kernel and each
relation has zero constant coefficient, the entire kernel lies in the variable ideal. This is the
exact source-side bridge needed before descending the zero section. -/
private theorem ker_le_idealOfVars_of_shifted_generators
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n m : ℕ}
    (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (rels : Fin m → MvPolynomial (Fin n) A)
    (hspan : Ideal.span (Set.range rels) = RingHom.ker π.toRingHom)
    (hconst : ∀ i, MvPolynomial.constantCoeff (rels i) = 0) :
    RingHom.ker π.toRingHom ≤ MvPolynomial.idealOfVars (Fin n) A := by
  intro φ hφ
  rw [← hspan] at hφ
  -- Proof comment: it is enough to check the spanning generators, and each generator lands in the
  -- zero-evaluation kernel because its constant coefficient vanishes.
  refine (Ideal.span_le.mpr ?_) hφ
  intro ψ hψ
  rcases hψ with ⟨i, rfl⟩
  rw [← aeval_zero_ker_eq_idealOfVars_local (A := A) (d := n)]
  simp [RingHom.mem_ker, hconst i]

/-- Helper for Lemma 10.126.6: translating the polynomial variables by a tuple `u` and then by
`-u` recovers the original polynomial algebra map, and conversely. -/
private theorem mvPolynomial_shift_inverse_identities
    {A : Type*} [CommRing A] {n : ℕ} (u : Fin n → A) :
    let τminus : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A :=
      MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)
    let τplus : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A :=
      MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i)
    τminus.comp τplus = AlgHom.id A (MvPolynomial (Fin n) A) ∧
      τplus.comp τminus = AlgHom.id A (MvPolynomial (Fin n) A) := by
  dsimp
  constructor
  · -- Proof comment: `MvPolynomial.algHom_ext` reduces the equality of the two endomorphisms to
    -- the effect on each polynomial variable.
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp [sub_eq_add_neg]
  · -- Proof comment: the opposite composition uses the same generator calculation.
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp [sub_eq_add_neg]

/-- Helper for Lemma 10.126.6: after shifting the presentation variables by `u`, the constant
coefficient is the original evaluation at `u`. -/
private theorem shift_constantCoeff_eq_aeval_tuple
    {A : Type*} [CommRing A] {n : ℕ} (u : Fin n → A) (φ : MvPolynomial (Fin n) A) :
    MvPolynomial.constantCoeff
      (MvPolynomial.aeval (R := A) (fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i)) φ) =
        MvPolynomial.eval u φ := by
  -- Proof comment: the shifted constant coefficient and evaluation at `u` are both ring maps, so
  -- `MvPolynomial.induction_on` reduces the comparison to constants, sums, and one variable step.
  induction φ using MvPolynomial.induction_on with
  | C a =>
      simp
  | add φ ψ hφ hψ =>
      simpa using congrArg₂ (fun x y ↦ x + y) hφ hψ
  | mul_X φ i hφ =>
      simpa using congrArg (fun x ↦ x * u i) hφ

/-- Helper for Lemma 10.126.6: composing a surjective polynomial presentation with a translation
of the variables is still surjective. -/
private theorem surjective_comp_mvPolynomial_shift
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n : ℕ} (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective π) (u : Fin n → A) :
    Function.Surjective
      (π.comp
        (MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i))) := by
  let τminus : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A :=
    MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)
  let τplus : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A :=
    MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i)
  intro y
  obtain ⟨φ, rfl⟩ := hπ y
  refine ⟨τminus φ, ?_⟩
  -- Proof comment: the inverse translation `τminus` produces a preimage because
  -- `τplus ∘ τminus = id` by the shift-inverse computation proved above.
  change π ((τplus.comp τminus) φ) = π φ
  have hτ : τplus.comp τminus = AlgHom.id A (MvPolynomial (Fin n) A) :=
    (mvPolynomial_shift_inverse_identities (A := A) (n := n) u).2
  have hτφ : (τplus.comp τminus) φ = φ := by
    simpa using
      congrArg (fun F : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A ↦ F φ) hτ
  simpa using congrArg π hτφ

/-- Helper for Lemma 10.126.6: the shifted presentation obtained by substituting `X i - u i`
into a surjective presentation is still surjective. -/
private theorem surjective_shifted_presentation
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n : ℕ}
    (πeval : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπeval : Function.Surjective πeval)
    (u : Fin n → A)
    (πshift : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπshift :
      πshift =
        πeval.comp
          (MvPolynomial.aeval (R := A)
            fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i))) :
    Function.Surjective πshift := by
  let uNeg : Fin n → A := fun i ↦ -u i
  have hsurj :
      Function.Surjective
        (πeval.comp
          (MvPolynomial.aeval (R := A)
            fun i ↦ MvPolynomial.X i + MvPolynomial.C (uNeg i))) :=
    surjective_comp_mvPolynomial_shift (π := πeval) hπeval uNeg
  have hrewrite :
      πeval.comp
          (MvPolynomial.aeval (R := A)
            fun i ↦ MvPolynomial.X i + MvPolynomial.C (uNeg i)) =
        πshift := by
    calc
      πeval.comp
          (MvPolynomial.aeval (R := A)
            fun i ↦ MvPolynomial.X i + MvPolynomial.C (uNeg i))
        =
          πeval.comp
            (MvPolynomial.aeval (R := A)
              fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
            -- Proof comment: rewriting `uNeg i = -u i` converts the plus-shift surjectivity lemma
            -- into the minus-shifted presentation used in the main source proof.
            refine congrArg
              (fun τ :
                MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A ↦
                  πeval.comp τ) ?_
            refine MvPolynomial.algHom_ext fun i ↦ ?_
            simp [uNeg, sub_eq_add_neg]
      _ = πshift := hπshift.symm
  rwa [hrewrite] at hsurj

/-- Helper for Lemma 10.126.6: once a finitely presented algebra is presented by a surjective
polynomial map, the kernel of every translated presentation is finitely generated. -/
private theorem shifted_presentation_kernel_fg
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    {n : ℕ} (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective π) (u : Fin n → A) :
    (RingHom.ker
      (π.comp
        (MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i))).toRingHom).FG := by
  have hsurj :
      Function.Surjective
        (π.comp
          (MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i))) :=
    surjective_comp_mvPolynomial_shift (π := π) hπ u
  -- Proof comment: finite presentation controls the kernel of any surjective polynomial
  -- presentation, so after the variable shift we can invoke the owner theorem directly.
  simpa using
    Algebra.FinitePresentation.ker_fG_of_surjective
      (π.comp
        (MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i + MvPolynomial.C (u i)))
      hsurj

/-- Helper for Lemma 10.126.6: the finitely generated kernel of a translated polynomial
presentation can be represented by an explicit finite indexed family of relations. -/
private theorem exists_shifted_kernel_generators
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    {n : ℕ} (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective π) (u : Fin n → A) :
    ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) A,
      Ideal.span (Set.range rels) =
        RingHom.ker
          (π.comp
            (MvPolynomial.aeval (R := A) fun i ↦
              MvPolynomial.X i + MvPolynomial.C (u i))).toRingHom := by
  have hfg :
      (RingHom.ker
        (π.comp
          (MvPolynomial.aeval (R := A) fun i ↦
            MvPolynomial.X i + MvPolynomial.C (u i))).toRingHom).FG :=
    shifted_presentation_kernel_fg (π := π) hπ u
  -- Proof comment: `Ideal.FG` is definitionally the submodule finiteness predicate, so the
  -- standard finite-family extraction theorem applies verbatim.
  simpa using Submodule.fg_iff_exists_fin_generating_family.mp hfg

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: localizing the coefficients away from `f` localizes the whole
polynomial ring away from `C f`. -/
private theorem localized_mvPolynomial_isLocalization
    {n : ℕ} (f : R) :
    IsLocalization (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (MvPolynomial (Fin n) (Localization.Away f)) := by
  -- Proof comment: `MvPolynomial.isLocalization` already localizes at the image of the chosen
  -- coefficient submonoid, and `Submonoid.map_powers` identifies that image with `powers (C f)`.
  simpa [Submonoid.map_powers] using
    (MvPolynomial.isLocalization (σ := Fin n) (M := Submonoid.powers f)
      (S := Localization.Away f))

/-- Helper for Lemma 10.126.6: the owner-side polynomial localization is canonically equivalent to
the polynomial ring over the localized coefficient ring. -/
private noncomputable abbrev localized_mvPolynomial_algEquiv_over_base
    {n : ℕ} (f : R) :
    Localization.Away (MvPolynomial.C (σ := Fin n) f) ≃ₐ[MvPolynomial (Fin n) R]
      MvPolynomial (Fin n) (Localization.Away f) :=
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (Localization.Away (MvPolynomial.C (σ := Fin n) f))
    (MvPolynomial (Fin n) (Localization.Away f))

/-- Helper for Lemma 10.126.6: under the canonical polynomial-localization equivalence, a
coefficient coming from `R` is sent back to the same coefficient in the owner localization. -/
private theorem localized_mvPolynomial_algEquiv_over_base_symm_C
    {n : ℕ} (f r : R) :
    (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
        (MvPolynomial.C (algebraMap R (Localization.Away f) r)) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.C (σ := Fin n) r) := by
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  -- Proof comment: both sides are the image of `C r / 1`, so
  -- `IsLocalization.algEquiv_symm_mk'` gives the comparison directly.
  simpa [localized_mvPolynomial_algEquiv_over_base, IsLocalization.mk'_one,
    MvPolynomial.isLocalization_C_mk'] using
    (IsLocalization.algEquiv_symm_mk'
      (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := MvPolynomial (Fin n) (Localization.Away f))
      (x := MvPolynomial.C (σ := Fin n) r)
      (y := (1 : Submonoid.powers (MvPolynomial.C (σ := Fin n) f))))

/-- Helper for Lemma 10.126.6: under the canonical polynomial-localization equivalence, a
polynomial variable is sent back to the same variable in the owner localization. -/
private theorem localized_mvPolynomial_algEquiv_over_base_symm_X
    {n : ℕ} (f : R) (i : Fin n) :
    (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
        (MvPolynomial.X i) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.X i) := by
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  -- Proof comment: the variable `X i` is the localization class of `X i / 1`, so the same owner
  -- formula applies with denominator `1`.
  simpa [localized_mvPolynomial_algEquiv_over_base, IsLocalization.mk'_one] using
    (IsLocalization.algEquiv_symm_mk'
      (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := MvPolynomial (Fin n) (Localization.Away f))
      (x := MvPolynomial.X i)
      (y := (1 : Submonoid.powers (MvPolynomial.C (σ := Fin n) f))))

/-- Helper for Lemma 10.126.6: the inverse of the canonical polynomial-localization equivalence is
the canonical localization comparison map induced by the identity on the owner polynomial ring. -/
private theorem localized_mvPolynomial_algEquiv_over_base_symm_eq_localization_map
    {n : ℕ} (f : R) :
    letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
    (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm.toRingHom =
      IsLocalization.map
        (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
        (S := MvPolynomial (Fin n) (Localization.Away f))
        (Q := Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (g := RingHom.id (MvPolynomial (Fin n) R))
        (by
          intro z hz
          simpa using hz) := by
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  -- Proof comment: both maps are ring homs out of the same localization of
  -- `MvPolynomial (Fin n) R`, so it suffices to compare them on the image of the owner
  -- polynomial ring. There, `MvPolynomial.ringHom_ext` reduces the comparison to coefficients and
  -- variables.
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    simpa using localized_mvPolynomial_algEquiv_over_base_symm_C (R := R) (n := n) f r
  · intro i
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    simpa using localized_mvPolynomial_algEquiv_over_base_symm_X (R := R) (n := n) f i

/-- Helper for Lemma 10.126.6: a denominator from `powers f` stays in the powers submonoid after
applying the coefficient embedding into the polynomial ring. -/
private theorem mvPolynomial_C_mem_powers
    {n : ℕ} {f : R} (y : Submonoid.powers f) :
    MvPolynomial.C (σ := Fin n) (y : R) ∈
      Submonoid.powers (MvPolynomial.C (σ := Fin n) f) := by
  rcases y with ⟨y, ⟨m, rfl⟩⟩
  -- Proof comment: coefficient embedding commutes with powers, so `C (f^m) = (C f)^m`.
  exact ⟨m, by simp⟩

/-- Helper for Lemma 10.126.6: under the canonical polynomial-localization equivalence, a
localized coefficient `x / y` is sent back to the owner-side localization class `C x / C y`. -/
private theorem localized_mvPolynomial_algEquiv_over_base_symm_C_mk'
    {n : ℕ} (f x : R) (y : Submonoid.powers f) :
    (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
        (MvPolynomial.C (IsLocalization.mk' (Localization.Away f) x y)) =
      IsLocalization.mk' (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.C (σ := Fin n) x)
        ⟨MvPolynomial.C (σ := Fin n) (y : R),
          mvPolynomial_C_mem_powers (R := R) (n := n) (f := f) y⟩ := by
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  have hid :
      Submonoid.powers (MvPolynomial.C (σ := Fin n) f) ≤
        Submonoid.comap (RingHom.id (MvPolynomial (Fin n) R))
          (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) := by
    intro z hz
    simpa using hz
  -- Proof comment: first rewrite `C (x / y)` as the polynomial-localization class `C x / C y`,
  -- then the new localization-map identification turns the goal into a plain `map_mk'`
  -- computation.
  have hmap :
      IsLocalization.map
          (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
          (S := MvPolynomial (Fin n) (Localization.Away f))
          (Q := Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (g := RingHom.id (MvPolynomial (Fin n) R))
          hid
          (MvPolynomial.C (IsLocalization.mk' (Localization.Away f) x y)) =
        IsLocalization.mk' (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (MvPolynomial.C (σ := Fin n) x)
          ⟨MvPolynomial.C (σ := Fin n) (y : R),
            mvPolynomial_C_mem_powers (R := R) (n := n) (f := f) y⟩ := by
    rw [MvPolynomial.isLocalization_C_mk' (σ := Fin n) (M := Submonoid.powers f)
      (S := Localization.Away f) x y]
    exact
      (IsLocalization.map_mk'
      (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (S := MvPolynomial (Fin n) (Localization.Away f))
      (Q := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (g := RingHom.id (MvPolynomial (Fin n) R))
      (hy := hid)
      (x := MvPolynomial.C (σ := Fin n) x)
      (y := ⟨MvPolynomial.C (σ := Fin n) (y : R),
        mvPolynomial_C_mem_powers (R := R) (n := n) (f := f) y⟩))
  simpa [localized_mvPolynomial_algEquiv_over_base_symm_eq_localization_map
    (R := R) (n := n) f] using hmap

/-- Helper for Lemma 10.126.6: after conjugating the owner-side away presentation by the
canonical polynomial-localization equivalence, the coefficient map is exactly the base away map
`R_f → S_f`. -/
private theorem awayMap_algebraMap_eq_algebraMap (f : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    Localization.awayMap (algebraMap R S) f =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  -- Proof comment: the canonical `Localization.awayMap` is exactly the ring hom underlying the
  -- induced `R_f`-algebra structure on `S_f`.
  simpa [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.126.6: after conjugating the owner-side away presentation by the
canonical polynomial-localization equivalence, the coefficient map is exactly the base away map
`R_f → S_f`. -/
private theorem direct_away_map_on_owner_generators
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R) :
    letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
    let πawayDirect :=
      IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π (MvPolynomial.C (σ := Fin n) f)
    (∀ r,
      πawayDirect
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (MvPolynomial.C (σ := Fin n) r)) =
        algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S r)) ∧
      (∀ i,
        πawayDirect
          (algebraMap (MvPolynomial (Fin n) R)
            (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (MvPolynomial.X i)) =
          algebraMap S (Localization.Away (algebraMap R S f)) (π (MvPolynomial.X i))) := by
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  let hpow :
      Submonoid.powers (MvPolynomial.C (σ := Fin n) f) ≤
        Submonoid.comap π.toRingHom (Submonoid.powers (algebraMap R S f)) := by
    -- Proof comment: the owner denominator `C f` maps to the target denominator `f`, so every
    -- owner-side power of `C f` lands in the powers submonoid generated by `f` in `S`.
    intro z hz
    rw [Submonoid.mem_powers_iff] at hz
    rw [Submonoid.mem_comap, Submonoid.mem_powers_iff]
    rcases hz with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc
      (algebraMap R S f) ^ m = π ((MvPolynomial.C (σ := Fin n) f) ^ m) := by
        simp
      _ = π z := by
        rw [hm]
  dsimp
  constructor
  · intro r
    -- Proof comment: `IsLocalization.map_eq` computes the direct away map on the owner
    -- coefficient generator `C r / 1`, and `convert` rewrites the harmless `π (C r)` output to
    -- the expected `algebraMap R S r`.
    convert (IsLocalization.map_eq
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := Localization.Away (algebraMap R S f))
      (g := π.toRingHom)
      (hy := hpow)
      (x := MvPolynomial.C (σ := Fin n) r)) using 1
    simp
  · intro i
    -- Proof comment: the same localization computation on the owner variable `X i / 1` gives the
    -- image of the corresponding presentation generator in `S_f`.
    convert (IsLocalization.map_eq
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := Localization.Away (algebraMap R S f))
      (g := π.toRingHom)
      (hy := hpow)
      (x := MvPolynomial.X i)) using 1

/-- Helper for Lemma 10.126.6: after conjugating the owner-side away presentation by the
canonical polynomial-localization equivalence, the coefficient map is exactly the base away map
`R_f → S_f`. -/
private theorem transported_away_presentation_coeff_eq_awayMap
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R) :
    letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
    let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
    let πtransport :=
      (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
        (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
    πtransport.toRingHom.comp (MvPolynomial.C : Localization.Away f →+* MvPolynomial (Fin n) (Localization.Away f)) =
      Localization.awayMap (algebraMap R S) f := by
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
  let πtransport :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
        Localization.Away (algebraMap R S f) :=
    (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f)).comp
      (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
  rcases direct_away_map_on_owner_generators (R := R) (S := S) (n := n) π f with ⟨hcoeff, -⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  -- Proof comment: after pulling `C r / 1` back across the polynomial-localization equivalence,
  -- the direct away map sends it to the localized coefficient `r / 1`, which is also exactly what
  -- the base away map does on `R_f`.
  have haway :
      Localization.awayMap (algebraMap R S) f (algebraMap R (Localization.Away f) r) =
        algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S r) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
  change (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) π
      (MvPolynomial.C (σ := Fin n) f))
      (ePoly.symm (MvPolynomial.C (algebraMap R (Localization.Away f) r))) =
    Localization.awayMap (algebraMap R S) f (algebraMap R (Localization.Away f) r)
  rw [localized_mvPolynomial_algEquiv_over_base_symm_C]
  rw [hcoeff r, haway]

/-- Helper for Lemma 10.126.6: the conjugated localized presentation agrees with the canonical
scalar map on explicit coefficient fractions `x / y` in `R_f`. -/
private theorem transported_away_presentation_coeff_mk'
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f x : R) (y : Submonoid.powers f) :
    letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
    let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
    let πtransport :=
      (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
        (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
    πtransport (MvPolynomial.C (IsLocalization.mk' (Localization.Away f) x y)) =
      Localization.awayMap (algebraMap R S) f
        (IsLocalization.mk' (Localization.Away f) x y) := by
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
  let πtransport :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
        Localization.Away (algebraMap R S f) :=
    (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f)).comp
      (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
  -- Proof comment: this is the mk'-specialization of the coefficient ring-hom comparison proved
  -- just above.
  have hcoeff :=
    transported_away_presentation_coeff_eq_awayMap
      (R := R) (S := S) (n := n) (π := π) (f := f)
  exact congrArg
    (fun φ : Localization.Away f →+* Localization.Away (algebraMap R S f) ↦
      φ (IsLocalization.mk' (Localization.Away f) x y)) hcoeff

/-- Helper for Lemma 10.126.6: the conjugated localized presentation agrees with the canonical
coefficient map on every element of the localized coefficient ring `R_f`. -/
private theorem transported_away_presentation_comp_coeff
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R)
    (z : Localization.Away f) :
    letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
    let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
    let πtransport :=
      (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
        (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
    πtransport (MvPolynomial.C z) =
      Localization.awayMap (algebraMap R S) f z := by
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
  let πtransport :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
        Localization.Away (algebraMap R S f) :=
    (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f)).comp
      (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
  -- Proof comment: this is the pointwise form of the coefficient ring-hom comparison.
  have hcoeff :=
    transported_away_presentation_coeff_eq_awayMap
      (R := R) (S := S) (n := n) (π := π) (f := f)
  exact congrArg
    (fun φ : Localization.Away f →+* Localization.Away (algebraMap R S f) ↦
      φ z) hcoeff

/-- Helper for Lemma 10.126.6: the canonical away localization `S_f` carries the expected scalar
tower structure over `R → R_f`. -/
private theorem away_localization_isScalarTower (f : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  -- Proof comment: for the canonical `awayMap` algebra structure, the scalar tower is the
  -- standard localization tower `R → R_f → S_f`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  simpa [Localization.awayMapₐ, RingHom.algebraMap_toAlgebra] using
    (Localization.awayMapₐ (Algebra.ofId R S) f).commutes x |>.symm

/-- Helper for Lemma 10.126.6: after conjugating the owner-side away map by the canonical
polynomial-localization equivalence, one obtains the explicit localized polynomial presentation. -/
private theorem transported_away_presentation_eq_localized_aeval
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R) :
    letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      away_localization_isScalarTower (R := R) (S := S) f
    let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
    let πtransport :=
      (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
        (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
    let πeval :
        MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
          Localization.Away (algebraMap R S f) :=
      AlgHom.restrictScalars R
        (MvPolynomial.aeval
          (fun i ↦
            algebraMap S (Localization.Away (algebraMap R S f))
              (π (MvPolynomial.X i))) :
            MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
              Localization.Away (algebraMap R S f))
    πtransport = πeval := by
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    away_localization_isScalarTower (R := R) (S := S) f
  let ePoly := localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f
  let πtransport :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
        Localization.Away (algebraMap R S f) :=
    (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f)).comp
      (AlgHom.restrictScalars R ePoly.symm.toAlgHom)
  let πeval :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
        Localization.Away (algebraMap R S f) :=
    AlgHom.restrictScalars R
      (MvPolynomial.aeval
        (fun i ↦
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i))) :
          MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
            Localization.Away (algebraMap R S f))
  rcases direct_away_map_on_owner_generators (R := R) (S := S) (n := n) π f with
    ⟨hcoeff, hvars⟩
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.coe_ringHom_injective
    -- Proof comment: on coefficients, the conjugated owner-side presentation is exactly the base
    -- away map, and the explicit localized presentation restricts to the ambient `R_f`-algebra
    -- structure on `S_f`.
    ext z
    change πtransport (MvPolynomial.C z) = πeval (MvPolynomial.C z)
    rw [transported_away_presentation_comp_coeff
      (R := R) (S := S) (n := n) (π := π) (f := f) (z := z)]
    simpa [πeval, awayMap_algebraMap_eq_algebraMap (R := R) (S := S) f]
  · intro i
    -- Proof comment: on variables, `ePoly.symm` sends `X i` back to the owner variable `X i / 1`,
    -- and the direct away map sends that class to the localized generator `π (X i) / 1`.
    change (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f))
        (ePoly.symm (MvPolynomial.X i)) =
      (AlgHom.restrictScalars R
          (MvPolynomial.aeval
            (fun j ↦
              algebraMap S (Localization.Away (algebraMap R S f))
                (π (MvPolynomial.X j))) :
            MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
              Localization.Away (algebraMap R S f))) (MvPolynomial.X i)
    rw [localized_mvPolynomial_algEquiv_over_base_symm_X]
    simpa [πeval] using hvars i

/-- Helper for Lemma 10.126.6: after shrinking at `f`, the canonical maps from the away
localizations to the prime localizations commute with the original local ring map. -/
private theorem away_to_atPrime_square_commutes
    (hq : q.LiesOver p) {f : R} (hf : f ∉ p) :
    let ρR : Localization.Away f →+* Localization.AtPrime p :=
      Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
        (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
    let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
      Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
        (IsLocalization.map_units (Localization.AtPrime q)
          (⟨algebraMap R S f, by
            intro hfq
            exact hf (by
              rw [hq.over]
              simpa [Ideal.mem_comap] using hfq)⟩ : q.primeCompl))
    ρS.comp (Localization.awayMap (algebraMap R S) f) =
      (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR := by
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
      (IsLocalization.map_units (Localization.AtPrime q)
        (⟨algebraMap R S f, by
          intro hfq
          exact hf (by
            rw [hq.over]
            simpa [Ideal.mem_comap] using hfq)⟩ : q.primeCompl))
  -- Proof comment: both maps out of `R_f` are localization lifts, so equality is controlled by
  -- their values on the image of `R`.
  suffices
      ρS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR by
    simpa [ρR, ρS]
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  -- Proof comment: the left side is the direct away-then-stalk map, while the right side is the
  -- stalk map `R_p → S_q` after the canonical map `R_f → R_p`; both send `r` to the same image
  -- in `S_q`.
  have haway :
      (Localization.awayMap (algebraMap R S) f) (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away (algebraMap R S f)) r := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
  have hρR :
      ρR (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.AtPrime p) r := by
    simp [ρR, Localization.awayLift]
  calc
    (ρS.comp (Localization.awayMap (algebraMap R S) f)) (algebraMap R (Localization.Away f) r)
        = ρS (algebraMap R (Localization.Away (algebraMap R S f)) r) := by
            rw [RingHom.comp_apply, haway]
    _ = algebraMap S (Localization.AtPrime q) (algebraMap R S r) := by
          rw [IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) r]
          simp [ρS, Localization.awayLift]
    _ = (Localization.localRingHom p q (algebraMap R S) hq.over)
          (algebraMap R (Localization.AtPrime p) r) := by
          symm
          exact Localization.localRingHom_to_map p q (algebraMap R S) hq.over r
    _ = ((Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR)
          (algebraMap R (Localization.Away f) r) := by
          rw [RingHom.comp_apply, hρR]

/-- Helper for Lemma 10.126.6: after the second shrink from `R_f` to `R_(f * g)`, the matching
second shrink from `S_f` to `S_(f * g)` fits into the expected commuting away square. -/
private theorem final_away_square_commutes
    (f g : R) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
      (Localization.awayMap (algebraMap R S) fg).comp ρfgR := by
  let fg : R := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  have haway_f :
      ∀ r : R,
        (Localization.awayMap (algebraMap R S) f) (algebraMap R (Localization.Away f) r) =
          algebraMap R (Localization.Away (algebraMap R S f)) r := by
    intro r
    -- Proof comment: the first away map is exactly the installed `R_f`-algebra map on `S_f`.
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
  have haway_fg :
      ∀ r : R,
        (Localization.awayMap (algebraMap R S) fg) (algebraMap R (Localization.Away fg) r) =
          algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
    intro r
    -- Proof comment: the final away map is likewise the scalar map of the `R_(fg)`-algebra
    -- structure on `S_(fg)`.
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) fg).commutes r
  have hρfgR :
      ∀ r : R,
        ρfgR (algebraMap R (Localization.Away f) r) =
          algebraMap R (Localization.Away fg) r := by
    intro r
    -- Proof comment: the source-side second shrink sends the class of `r / 1` to the same class
    -- in `R_(fg)`.
    simpa [ρfgR, fg] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away f) (P := Localization.Away fg)
        (x := f) (y := g) (a := r))
  have hρfgS :
      ∀ r : R,
        ρfgS (algebraMap R (Localization.Away (algebraMap R S f)) r) =
          algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
    intro r
    -- Proof comment: on the target side, the second shrink is again the canonical away-to-away
    -- map, now applied to the image of `r` inside `S_f`.
    rw [show algebraMap R (Localization.Away (algebraMap R S f)) r =
        algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S r) by
          simpa using
            (DFunLike.congr_fun
              (IsScalarTower.algebraMap_eq R S
                (Localization.Away (algebraMap R S f))) r).symm]
    simpa [ρfgS, fg] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away (algebraMap R S f))
        (P := Localization.Away (algebraMap R S fg))
        (x := algebraMap R S f) (y := algebraMap R S g)
        (a := algebraMap R S r))
  -- Proof comment: as in the first away-to-stalk square, localization uniqueness reduces the
  -- comparison to the image of the original ring `R`.
  suffices
      ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.awayMap (algebraMap R S) fg).comp ρfgR by
    simpa [fg, ρfgR, ρfgS]
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  calc
    (ρfgS.comp (Localization.awayMap (algebraMap R S) f))
        (algebraMap R (Localization.Away f) r)
        = ρfgS (algebraMap R (Localization.Away (algebraMap R S f)) r) := by
            rw [RingHom.comp_apply, haway_f r]
    _ = algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
          exact hρfgS r
    _ = (Localization.awayMap (algebraMap R S) fg)
          (algebraMap R (Localization.Away fg) r) := by
          symm
          exact haway_fg r
    _ = ((Localization.awayMap (algebraMap R S) fg).comp ρfgR)
          (algebraMap R (Localization.Away f) r) := by
          rw [RingHom.comp_apply, hρfgR r]

/-- Helper for Lemma 10.126.6: the shifted presentation on `R_f` transports pointwise to the final
away chart `R_(f * g)` by applying `MvPolynomial.map` to the coefficients and the canonical
away-to-away map to the target values of the shifted variables. -/
private theorem final_away_shifted_presentation_map
    {n : ℕ} {f g : R}
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∀ (πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f)),
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro πshift
  let fg : R := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
  have hcoeff :
      (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg))).comp ρfgR =
        ρfgS.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) := by
    -- Proof comment: the coefficient comparison is exactly the canonical final-away square once
    -- both away maps are rewritten as the installed algebra maps on the localized targets.
    rw [← awayMap_algebraMap_eq_algebraMap (R := R) (S := S) fg]
    rw [← awayMap_algebraMap_eq_algebraMap (R := R) (S := S) f]
    symm
    simpa [fg, ρfgR, ρfgS] using
      final_away_square_commutes (R := R) (S := S) f g
  have hπshift_aeval :
      MvPolynomial.aeval (fun i ↦ πshift (MvPolynomial.X i)) = πshift := by
    -- Proof comment: an algebra map out of a multivariable polynomial ring is determined by its
    -- values on the variables, so the displayed `aeval` is just `πshift` itself.
    apply MvPolynomial.algHom_ext
    intro i
    simp
  calc
    πshiftFinal (MvPolynomial.map ρfgR ψ)
        = MvPolynomial.eval₂Hom
            ((algebraMap (Localization.Away fg)
              (Localization.Away (algebraMap R S fg))).comp ρfgR)
            (fun i ↦ ρfgS (πshift (MvPolynomial.X i))) ψ := by
              -- Proof comment: rewrite the final-away presentation as an explicit `eval₂Hom` and
              -- transport the coefficient map through `MvPolynomial.map`.
              simp [πshiftFinal, MvPolynomial.aeval_eq_eval₂Hom]
    _ = MvPolynomial.eval₂Hom
          (ρfgS.comp
            (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))))
          (fun i ↦ ρfgS (πshift (MvPolynomial.X i))) ψ := by
            rw [hcoeff]
    _ = ρfgS ((MvPolynomial.aeval fun i ↦ πshift (MvPolynomial.X i)) ψ) := by
          -- Proof comment: after the coefficient maps match, the target side is exactly the image
          -- of evaluating the old shifted presentation and then applying the away-to-away map.
          symm
          simpa [MvPolynomial.aeval_eq_eval₂Hom] using
            (MvPolynomial.map_aeval
              (R := Localization.Away f)
              (σ := Fin n)
              (S₁ := Localization.Away (algebraMap R S f))
              (B := Localization.Away (algebraMap R S fg))
              (g := fun i ↦ πshift (MvPolynomial.X i))
              (φ := ρfgS)
              (p := ψ))
    _ = ρfgS (πshift ψ) := by
          rw [hπshift_aeval]

/-- Helper for Lemma 10.126.6: after the second shrink, the transported relation family
`relsFinal` spans exactly the image of the old shifted kernel ideal under coefficient base change.
-/
private theorem final_away_relations_span_eq_map_shifted_kernel
    {n m : ℕ} {f g : R}
    (relsShift : Fin m → MvPolynomial (Fin n) (Localization.Away f))
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (hK : Ideal.span (Set.range relsShift) = K) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    let relsFinal : Fin m → MvPolynomial (Fin n) (Localization.Away fg) :=
      fun j ↦ MvPolynomial.map ρfgR (relsShift j)
    Ideal.span (Set.range relsFinal) = Ideal.map (MvPolynomial.map ρfgR) K := by
  intro fg ρfgR relsFinal
  -- Proof comment: this is the source-proof transport step in pure ideal language:
  -- the new final-away relations are just the old relations with coefficients mapped along
  -- `R_f → R_(fg)`, so their span is the image ideal of the old shifted kernel.
  rw [← hK, Ideal.map_span]
  refine congrArg Ideal.span ?_
  ext ψ
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨relsShift j, Set.mem_range_self j, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    rcases hφ with ⟨j, rfl⟩
    exact Set.mem_range_self j

/-- Helper for Lemma 10.126.6: the forward transported-kernel inclusion on the final away chart
descends the final shifted presentation to the quotient by the mapped old kernel. -/
private noncomputable def final_away_quotient_comparison
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hkerle :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
          (Localization.Away (algebraMap R S fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap R S fg)
                (Localization.Away (algebraMap R S fg)))
      let ρfgS : Localization.Away (algebraMap R S f) →+*
          Localization.Away (algebraMap R S fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap R S fg))
          (algebraMap R S f) (algebraMap R S g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
        (Localization.awayMap (algebraMap R S) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap R S fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
      Localization.Away (algebraMap R S fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro fg ρfgR
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  intro ρfgS
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro Kfg πshiftFinal
  -- Proof comment: the forward kernel inclusion is exactly the datum needed to descend
  -- `πshiftFinal` across the quotient by the transported old kernel.
  exact Ideal.Quotient.liftₐ Kfg πshiftFinal hkerle

/-- Helper for Lemma 10.126.6: the quotient comparison map just defined sends each transported
polynomial class to the final-away image of the old shifted presentation. -/
private theorem final_away_quotient_comparison_apply_mk
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hkerle :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
          (Localization.Away (algebraMap R S fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap R S fg)
                (Localization.Away (algebraMap R S fg)))
      let ρfgS : Localization.Away (algebraMap R S f) →+*
          Localization.Away (algebraMap R S fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap R S fg))
          (algebraMap R S f) (algebraMap R S g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
        (Localization.awayMap (algebraMap R S) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap R S fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom)
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    let qComp :
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      final_away_quotient_comparison (R := R) (S := S) (πshift := πshift) (f := f) (g := g) hkerle
    qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) = ρfgS (πshift ψ) := by
  intro fg ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  intro ρfgS
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro Kfg πshiftFinal qComp
  -- Proof comment: after descending `πshiftFinal`, the quotient computation reduces immediately
  -- to the already established pointwise final-away transport formula.
  change πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ)
  simpa [πshiftFinal] using
    final_away_shifted_presentation_map
      (R := R)
      (S := S)
      (ψ := ψ)
      (πshift := πshift)
      (f := f)
      (g := g)

/-- Helper for Lemma 10.126.6: once the quotient comparison map is upgraded to an algebra
equivalence, surjectivity of the presentation and the exact kernel formula become formal
consequences of that equivalence. -/
private theorem surjective_and_ker_of_quotient_comparison_algEquiv
    {A : Type*} [CommRing A]
    {P : Type*} [CommRing P] [Algebra A P]
    {B : Type*} [CommRing B] [Algebra A B]
    (π : P →ₐ[A] B)
    (K : Ideal P)
    (e : (P ⧸ K) ≃ₐ[A] B)
    (he : ∀ x : P, e (Ideal.Quotient.mk K x) = π x) :
    Function.Surjective π ∧ RingHom.ker π.toRingHom = K := by
  constructor
  · intro b
    obtain ⟨q, rfl⟩ := e.surjective b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    -- Proof comment: every quotient class has a polynomial representative, and the comparison
    -- formula `he` turns that representative into a preimage for `π`.
    exact ⟨x, (he x).symm⟩
  · ext x
    constructor
    · intro hx
      -- Proof comment: if `π x = 0`, then the quotient class of `x` maps to zero under the
      -- equivalence `e`, hence the class itself is zero and `x` lies in `K`.
      have hq : e (Ideal.Quotient.mk K x) = e 0 := by
        simpa [he x, RingHom.mem_ker] using hx
      have hmk : Ideal.Quotient.mk K x = 0 := e.injective hq
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
    · intro hx
      -- Proof comment: an element of `K` has zero quotient class, so the comparison identity
      -- immediately forces its image under `π` to vanish.
      have hmk : Ideal.Quotient.mk K x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      have hq : e (Ideal.Quotient.mk K x) = 0 := by
        simpa using congrArg e hmk
      simpa [RingHom.mem_ker, he x] using hq

/-- Helper for Lemma 10.126.6: if the quotient comparison algebra equivalence is already expressed
over a spanning family of relations, the kernel formula can be rewritten directly in that
relation-span form. -/
private theorem surjective_and_kernel_span_of_quotient_comparison_algEquiv
    {A : Type*} [CommRing A]
    {P : Type*} [CommRing P] [Algebra A P]
    {B : Type*} [CommRing B] [Algebra A B]
    {ι : Type*}
    (π : P →ₐ[A] B)
    (rels : ι → P)
    (K : Ideal P)
    (hspan : Ideal.span (Set.range rels) = K)
    (e : (P ⧸ K) ≃ₐ[A] B)
    (he : ∀ x : P, e (Ideal.Quotient.mk K x) = π x) :
    Function.Surjective π ∧
      RingHom.ker π.toRingHom = Ideal.span (Set.range rels) := by
  obtain ⟨hπsurj, hker⟩ :=
    surjective_and_ker_of_quotient_comparison_algEquiv
      (π := π) (K := K) e he
  refine ⟨hπsurj, ?_⟩
  calc
    RingHom.ker π.toRingHom = K := hker
    _ = Ideal.span (Set.range rels) := hspan.symm

/-- Helper for Lemma 10.126.6: an `A`-algebra map out of a finite polynomial algebra is the
constant-coefficient map once every polynomial variable maps to zero. -/
private theorem mvPolynomial_image_eq_constantCoeff_of_variables_zero
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n : ℕ}
    (φ : MvPolynomial (Fin n) A →ₐ[A] B)
    (hX : ∀ i, φ (MvPolynomial.X i) = 0)
    (ψ : MvPolynomial (Fin n) A) :
    φ ψ = algebraMap A B (MvPolynomial.constantCoeff ψ) := by
  let g : Fin n → B := fun i ↦ φ (MvPolynomial.X i)
  have hφ : φ = MvPolynomial.aeval g := by
    -- Proof comment: `MvPolynomial.algHom_ext` identifies an algebra map by its values on the
    -- polynomial variables.
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp [g, MvPolynomial.aeval_X]
  rw [hφ]
  -- Proof comment: once the variable values vanish, the polynomial evaluation collapses to the
  -- constant coefficient.
  exact
    MvPolynomial.aeval_eq_constantCoeff_of_vars (p := ψ)
      (fun i _ ↦ by simpa [g] using hX i)

/-- Helper for Lemma 10.126.6: if a polynomial relation lies in the kernel of a presentation and
the target localization kills all variables, then its constant coefficient also maps to zero. -/
private theorem constantCoeff_map_zero_of_mem_ker_of_variables_zero
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {C : Type*} [CommRing C] [Algebra A C]
    {n : ℕ}
    (ρ : B →ₐ[A] C)
    (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hX : ∀ i, ρ (π (MvPolynomial.X i)) = 0)
    {φ : MvPolynomial (Fin n) A}
    (hφ : φ ∈ RingHom.ker π.toRingHom) :
    algebraMap A C (MvPolynomial.constantCoeff φ) = 0 := by
  have hπφ : π φ = 0 := by
    simpa [RingHom.mem_ker] using hφ
  -- Proof comment: after postcomposing with `ρ`, the presentation map is forced to be the
  -- constant-coefficient map by the vanishing of the variables.
  have hcoeff :
      ρ (π φ) = algebraMap A C (MvPolynomial.constantCoeff φ) := by
    simpa using
      mvPolynomial_image_eq_constantCoeff_of_variables_zero
        (φ := ρ.comp π) (hX := hX) φ
  rw [hπφ, map_zero] at hcoeff
  simpa [eq_comm] using hcoeff

/-- Helper for Lemma 10.126.6: the inverse of a bijective local ring map carries any element of
`S_𝔮` to a source element whose image is the original target element. -/
private theorem localRingHom_apply_symm_of_bijective
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    let localEquiv : Localization.AtPrime p ≃+* Localization.AtPrime q :=
      RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hq.over) hlocal
    ∀ y : Localization.AtPrime q,
      (Localization.localRingHom p q (algebraMap R S) hq.over) (localEquiv.symm y) = y := by
  intro localEquiv y
  -- Proof comment: `localEquiv` is the ring equivalence attached to the bijective local map, so
  -- applying the local map after `localEquiv.symm` is exactly `localEquiv.apply_symm_apply`.
  exact localEquiv.apply_symm_apply y

/-- Helper for Lemma 10.126.6: the chosen local preimage of each presentation generator in
`R_𝔭` maps back to that generator in `S_𝔮`. -/
private theorem generator_preimage_maps_to_variable
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) :
    let localEquiv : Localization.AtPrime p ≃+* Localization.AtPrime q :=
      RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hq.over) hlocal
    let generatorPreimage : Fin n → Localization.AtPrime p := fun i ↦
      localEquiv.symm (algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)))
    ∀ i,
      (Localization.localRingHom p q (algebraMap R S) hq.over) (generatorPreimage i) =
        algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)) := by
  intro localEquiv generatorPreimage i
  -- Proof comment: each `generatorPreimage i` was defined by applying the inverse local
  -- equivalence to the image of `π (X i)`, so the forward map returns that image immediately.
  exact
    localRingHom_apply_symm_of_bijective
      (R := R) (S := S) (p := p) (q := q) hq hlocal
      (algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)))

/-- Helper for Lemma 10.126.6: after the first denominator-clearing shrink, the chosen tuple
`a / f` in `R_f` maps to the original local preimages of the polynomial generators. -/
private theorem away_cleared_tuple_eq_generator_preimage
    {n : ℕ} {f : R} (hf : f ∉ p) (a : Fin n → R)
    (generatorPreimage : Fin n → Localization.AtPrime p)
    (ha : ∀ i,
      algebraMap R (Localization.AtPrime p) f * generatorPreimage i =
        algebraMap R (Localization.AtPrime p) (a i)) :
    let ρR : Localization.Away f →+* Localization.AtPrime p :=
      Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
        (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
    let u : Fin n → Localization.Away f :=
      let denom : Submonoid.powers f := ⟨f, ⟨1, by simp⟩⟩
      fun i ↦ IsLocalization.mk' (Localization.Away f) (a i) denom
    ∀ i, ρR (u i) = generatorPreimage i := by
  intro ρR u i
  let denom : Submonoid.powers f := ⟨f, ⟨1, by simp⟩⟩
  -- Proof comment: `u i` is the fraction `a i / f`, so `IsLocalization.lift_mk'_spec`
  -- translates the target equality to exactly the cleared-denominator identity `ha i`.
  apply (IsLocalization.lift_mk'_spec
    (M := Submonoid.powers f)
    (S := Localization.Away f)
    (g := algebraMap R (Localization.AtPrime p))
    (hg := fun y ↦ by
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨k, rfl⟩
      simpa using
        (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl)).pow k)
    (x := a i)
    (v := generatorPreimage i)
    (y := denom)).2
  simpa [ρR, u, denom, mul_comm] using (ha i).symm

/-- Helper for Lemma 10.126.6: subtracting a tuple `u` from the polynomial variables is the same
as postcomposing the original presentation with the substitution `Xᵢ ↦ Xᵢ - C(uᵢ)`. -/
private theorem shifted_localized_presentation_eq_sub
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n : ℕ} (v : Fin n → B) (u : Fin n → A) :
    let πeval : MvPolynomial (Fin n) A →ₐ[A] B :=
      MvPolynomial.aeval v
    let πshift : MvPolynomial (Fin n) A →ₐ[A] B :=
      MvPolynomial.aeval (fun i ↦ v i - algebraMap A B (u i))
    πshift =
      πeval.comp
        (MvPolynomial.aeval (R := A) fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
  dsimp
  -- Proof comment: both algebra maps are determined by their values on the polynomial variables.
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [sub_eq_add_neg]

/-- Helper for Lemma 10.126.6: after the first denominator-clearing shrink, every shifted
presentation variable maps to `0` in `S_𝔮`. -/
private theorem shifted_localized_variables_vanish_at_q
    (hq : q.LiesOver p) {n : ℕ} {f : R} (hf : f ∉ p)
    (π : MvPolynomial (Fin n) R →ₐ[R] S)
    (generatorPreimage : Fin n → Localization.AtPrime p)
    (hgeneratorPreimage : ∀ i,
      (Localization.localRingHom p q (algebraMap R S) hq.over) (generatorPreimage i) =
        algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)))
    (u : Fin n → Localization.Away f)
    (hu :
      let ρR : Localization.Away f →+* Localization.AtPrime p :=
        Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
          (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
      ∀ i, ρR (u i) = generatorPreimage i) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let ρR : Localization.Away f →+* Localization.AtPrime p :=
      Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
        (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
    let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
      Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
        (IsLocalization.map_units (Localization.AtPrime q)
          (⟨algebraMap R S f, by
            intro hfq
            exact hf (by
              rw [hq.over]
              simpa [Ideal.mem_comap] using hfq)⟩ : q.primeCompl))
    let πshift :
        MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
          Localization.Away (algebraMap R S f) :=
      MvPolynomial.aeval
        (fun i ↦
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i)) -
            algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
              (u i))
    ∀ i, ρS (πshift (MvPolynomial.X i)) = 0 := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  have hfq : algebraMap R S f ∉ q := by
    intro hfq
    exact hf (by
      rw [hq.over]
      simpa [Ideal.mem_comap] using hfq)
  let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
      (IsLocalization.map_units (Localization.AtPrime q)
        (⟨algebraMap R S f, hfq⟩ : q.primeCompl))
  let πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i)) -
          algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
            (u i))
  have hu' : ∀ i, ρR (u i) = generatorPreimage i := by
    simpa [ρR] using hu
  have hawaySquare :
      ρS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR :=
    away_to_atPrime_square_commutes (R := R) (S := S) (p := p) (q := q) hq hf
  change ∀ i : Fin n, ρS (πshift (MvPolynomial.X i)) = 0
  intro i
  simp only [πshift, MvPolynomial.aeval_X]
  rw [map_sub]
  have hleft :
      ρS
        (algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i))) =
        algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)) := by
    -- Proof comment: the stalk map out of `S_f` is the canonical localization lift on `S`.
    simp [ρS, Localization.awayLift]
  have hright :
      ρS
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (u i)) =
        algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)) := by
    -- Proof comment: the coefficient term `u i` maps across the away-to-stalk square to the chosen
    -- preimage of the generator, which was arranged to map back to `π(X i)` in `S_q`.
    have hcomm := congrArg
      (fun φ : Localization.Away f →+* Localization.AtPrime q ↦ φ (u i)) hawaySquare
    rw [awayMap_algebraMap_eq_algebraMap (R := R) (S := S) f] at hcomm
    simpa [RingHom.comp_apply, hu' i, hgeneratorPreimage i] using hcomm
  rw [hleft, hright, sub_self]

/-- Helper for Lemma 10.126.6: after matching the minus-shifted presentation with the existing
plus-shift API, one gets finitely many shifted relations spanning the kernel, and each shifted
relation has constant coefficient vanishing in `R_𝔭`. -/
private theorem exists_sign_aligned_shifted_kernel_family
    (hq : q.LiesOver p) {n : ℕ} {f : R} (hf : f ∉ p) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∀ (πeval :
        MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
          Localization.Away (algebraMap R S f))
      (hπeval : Function.Surjective πeval)
      (u : Fin n → Localization.Away f)
      (πshift :
        MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
          Localization.Away (algebraMap R S f))
      (hπshiftSub :
        πshift =
          πeval.comp
            (MvPolynomial.aeval (R := Localization.Away f)
              fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)))
      (ρR : Localization.Away f →+* Localization.AtPrime p)
      (ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q)
      (hawaySquare :
        ρS.comp (Localization.awayMap (algebraMap R S) f) =
          (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR)
      (hlocal :
        Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
      (hshiftX : ∀ i, ρS (πshift (MvPolynomial.X i)) = 0),
    ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) (Localization.Away f),
      Ideal.span (Set.range rels) = RingHom.ker πshift.toRingHom ∧
        ∀ j, ρR (MvPolynomial.constantCoeff (rels j)) = 0 := by
  intro πeval hπeval u πshift hπshiftSub ρR ρS hawaySquare hlocal hshiftX
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    away_localization_isScalarTower (R := R) (S := S) f
  letI : Algebra.FinitePresentation (Localization.Away f)
      (Localization.Away (algebraMap R S f)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
      (R := R)
      (A := Localization.Away f)
      (B := Localization.Away (algebraMap R S f))
  let uNeg : Fin n → Localization.Away f := fun i ↦ -u i
  obtain ⟨m, rels, hspanRaw⟩ :=
    exists_shifted_kernel_generators (π := πeval) hπeval uNeg
  have hshiftEq :
      πeval.comp
          (MvPolynomial.aeval (R := Localization.Away f)
            fun i ↦ MvPolynomial.X i + MvPolynomial.C (uNeg i)) =
        πshift := by
    calc
      πeval.comp
          (MvPolynomial.aeval (R := Localization.Away f)
            fun i ↦ MvPolynomial.X i + MvPolynomial.C (uNeg i))
        =
          πeval.comp
            (MvPolynomial.aeval (R := Localization.Away f)
              fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
            -- Proof comment: `uNeg i = -u i`, so the existing plus-shift kernel API matches the
            -- already constructed minus-shifted presentation exactly.
            refine congrArg (fun τ :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                MvPolynomial (Fin n) (Localization.Away f) ↦ πeval.comp τ) ?_
            refine MvPolynomial.algHom_ext fun i ↦ ?_
            simp [uNeg, sub_eq_add_neg]
      _ = πshift := hπshiftSub.symm
  have hspan :
      Ideal.span (Set.range rels) = RingHom.ker πshift.toRingHom := by
    -- Proof comment: the sign-aligned family generates the same shifted kernel because the two
    -- presentations were identified in the previous step.
    exact hspanRaw.trans <| by
      rw [hshiftEq]
  refine ⟨m, rels, hspan, ?_⟩
  intro j
  letI : Algebra (Localization.Away f) (Localization.AtPrime q) :=
    (ρS.comp (Localization.awayMap (algebraMap R S) f)).toAlgebra
  let ρSAlg :
      Localization.Away (algebraMap R S f) →ₐ[Localization.Away f]
        Localization.AtPrime q :=
    AlgHom.mk ρS fun z ↦ by
      -- Proof comment: for the direct `R_f`-algebra structure on `S_𝔮`, `ρS` is an algebra map
      -- by construction.
      change ρS ((Localization.awayMap (algebraMap R S) f) z) =
        (ρS.comp (Localization.awayMap (algebraMap R S) f)) z
      rfl
  have hrel : rels j ∈ RingHom.ker πshift.toRingHom := by
    -- Proof comment: the chosen family spans the shifted kernel, so each displayed relation lies
    -- in that kernel.
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self j)
  have hconst_q :
      algebraMap (Localization.Away f) (Localization.AtPrime q)
        (MvPolynomial.constantCoeff (rels j)) = 0 := by
    -- Proof comment: once the shifted variables vanish in `S_𝔮`, every shifted relation in the
    -- kernel evaluates there to its constant coefficient.
    have hπrel : πshift (rels j) = 0 := by
      simpa [RingHom.mem_ker] using hrel
    have hcoeff :
        ρS (πshift (rels j)) =
          algebraMap (Localization.Away f) (Localization.AtPrime q)
            (MvPolynomial.constantCoeff (rels j)) := by
      simpa [ρSAlg] using
        mvPolynomial_image_eq_constantCoeff_of_variables_zero
          (φ := ρSAlg.comp πshift) (hX := hshiftX) (ψ := rels j)
    rw [hπrel, map_zero] at hcoeff
    simpa [eq_comm] using hcoeff
  have hconst_q' :
      (ρS.comp (Localization.awayMap (algebraMap R S) f))
        (MvPolynomial.constantCoeff (rels j)) = 0 := by
    change algebraMap (Localization.Away f) (Localization.AtPrime q)
      (MvPolynomial.constantCoeff (rels j)) = 0
    exact hconst_q
  -- Proof comment: the local map `R_𝔭 → S_𝔮` is injective, so vanishing after applying it forces
  -- the constant coefficient to vanish already in `R_𝔭`.
  have hcomm := congrArg
    (fun φ : Localization.Away f →+* Localization.AtPrime q ↦
      φ (MvPolynomial.constantCoeff (rels j))) hawaySquare
  have hlocalZero :
      (Localization.localRingHom p q (algebraMap R S) hq.over)
        (ρR (MvPolynomial.constantCoeff (rels j))) = 0 := by
    calc
      (Localization.localRingHom p q (algebraMap R S) hq.over)
          (ρR (MvPolynomial.constantCoeff (rels j)))
        = (ρS.comp (Localization.awayMap (algebraMap R S) f))
            (MvPolynomial.constantCoeff (rels j)) := by
              simpa [RingHom.comp_apply] using hcomm.symm
      _ = 0 := hconst_q'
  apply hlocal.1
  simpa using hlocalZero

/-- Helper for Lemma 10.126.6: if an element of `R_f` is annihilated by `g`, then it vanishes
after the second away-localization `R_f → R_(fg)`. -/
private theorem awayToAwayRight_eq_zero_of_mul_eq_zero
    {f g : R} {z : Localization.Away f}
    (hz : algebraMap R (Localization.Away f) g * z = 0) :
    let A := Localization.Away (f * g)
    let ρ : Localization.Away f →+* A :=
      IsLocalization.Away.awayToAwayRight (P := A) f g
    ρ z = 0 := by
  intro A ρ
  have hmap :
      ρ (algebraMap R (Localization.Away f) g) * ρ z = 0 := by
    simpa [map_mul] using congrArg ρ hz
  have hρg :
      ρ (algebraMap R (Localization.Away f) g) =
        algebraMap R A g := by
    simpa [ρ] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away f)
        (P := A)
        (x := f)
        (y := g)
        (a := g))
  have hunit : IsUnit (ρ (algebraMap R (Localization.Away f) g)) := by
    rw [hρg]
    exact IsLocalization.Away.isUnit_of_dvd
      (R := R)
      (S := A)
      (x := f * g)
      (by
        refine ⟨f, ?_⟩
        ring)
  exact (IsUnit.mul_right_eq_zero hunit).mp hmap

/-- Helper for Lemma 10.126.6: if finitely many elements of `R_f` vanish in `R_𝔭`, then one more
denominator `g ∉ p` makes them literally vanish in `R_(fg)`. -/
private theorem exists_notMem_zero_family_after_second_shrink_atPrime
    {m : ℕ} {f : R} (hf : f ∉ p)
    (z : Fin m → Localization.Away f)
    (hz :
      let ρR : Localization.Away f →+* Localization.AtPrime p :=
        Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
          (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
      ∀ i, ρR (z i) = 0) :
    ∃ g : R, g ∉ p ∧
      let A := Localization.Away (f * g)
      let ρ : Localization.Away f →+* A :=
        IsLocalization.Away.awayToAwayRight (P := A) f g
      ∀ i, ρ (z i) = 0 := by
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  have hz' : ∀ i, ρR (z i) = 0 := by
    simpa [ρR] using hz
  choose e a ha using fun i : Fin m ↦ IsLocalization.Away.surj f (z i)
  have ha_zero : ∀ i, algebraMap R (Localization.AtPrime p) (a i) = 0 := by
    intro i
    have hmap := congrArg ρR (ha i)
    rw [map_mul, hz' i, zero_mul] at hmap
    simpa [ρR, map_pow, Localization.awayLift] using hmap.symm
  choose t ht using fun i : Fin m ↦
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (a i)).mp (ha_zero i)
  let g : R := ∏ i, (t i : R)
  have hg_mem : g ∈ p.primeCompl := by
    -- Proof comment: the product of finitely many elements outside `p` still lies in the prime
    -- complement.
    simpa [g] using p.primeCompl.prod_mem fun i _ ↦ (t i).2
  have hg : g ∉ p := hg_mem
  refine ⟨g, hg, ?_⟩
  intro A ρ i
  let u : p.primeCompl := (Finset.univ.erase i).prod t
  have hg_split : g = t i * u := by
    -- Proof comment: split the common annihilator product into the `i`-th factor and the
    -- complementary product.
    symm
    simpa [g, u] using
      (Finset.mul_prod_erase (s := Finset.univ) (a := i) (f := fun j : Fin m ↦ (t j : R))
        (by simp))
  have hkill_g :
      algebraMap R (Localization.Away f) g * z i = 0 := by
    have hkill_num : algebraMap R R g * a i = 0 := by
      calc
        algebraMap R R g * a i
            = (algebraMap R R (t i) * algebraMap R R (u : R)) * a i := by
                rw [hg_split, map_mul]
        _ = algebraMap R R (u : R) * (algebraMap R R (t i) * a i) := by ring
        _ = 0 := by simp [ht i]
    have hmap_kill :
        algebraMap R (Localization.Away f) g *
            algebraMap R (Localization.Away f) (a i) = 0 := by
      simpa [map_mul, mul_comm] using congrArg
        (algebraMap R (Localization.Away f)) hkill_num
    have hf_unit :
        IsUnit (algebraMap R (Localization.Away f) f) := by
      exact IsLocalization.Away.algebraMap_isUnit
        (R := R)
        (S := Localization.Away f)
        (x := f)
    have haux :
        (algebraMap R (Localization.Away f) g * z i) *
          algebraMap R (Localization.Away f) f ^ e i = 0 := by
      calc
        (algebraMap R (Localization.Away f) g * z i) *
            algebraMap R (Localization.Away f) f ^ e i
            =
          algebraMap R (Localization.Away f) g *
            (z i * algebraMap R (Localization.Away f) f ^ e i) := by
              ring
        _ =
          algebraMap R (Localization.Away f) g *
            algebraMap R (Localization.Away f) (a i) := by
              rw [ha i]
        _ = 0 := hmap_kill
    exact (IsUnit.mul_left_eq_zero (hf_unit.pow _)).mp haux
  exact awayToAwayRight_eq_zero_of_mul_eq_zero
    (R := R)
    (f := f)
    (g := g)
    (z := z i)
    hkill_g

/-- Helper for Lemma 10.126.6: the shifted relations whose constant coefficients only vanish in
`R_𝔭` can be transported to one final away chart where those constant coefficients are literally
zero. -/
private theorem exists_notMem_zero_shifted_constants_after_second_shrink
    {n m : ℕ} {f : R} (hf : f ∉ p)
    (rels : Fin m → MvPolynomial (Fin n) (Localization.Away f))
    (hconst :
      let ρR : Localization.Away f →+* Localization.AtPrime p :=
        Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
          (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
      ∀ j, ρR (MvPolynomial.constantCoeff (rels j)) = 0) :
    ∃ g : R, g ∉ p ∧
      let A := Localization.Away (f * g)
      let ρ : Localization.Away f →+* A :=
        IsLocalization.Away.awayToAwayRight (P := A) f g
      ∀ j, ρ (MvPolynomial.constantCoeff (rels j)) = 0 := by
  -- Proof comment: apply the common-denominator argument to the finite family of constant
  -- coefficients of the shifted relations.
  simpa using
    exists_notMem_zero_family_after_second_shrink_atPrime
      (R := R)
      (p := p)
      (hf := hf)
      (z := fun j ↦ MvPolynomial.constantCoeff (rels j))
      hconst

/-- Helper for Lemma 10.126.6: once the shifted relations have literal zero constant coefficient,
the zero-evaluation map descends to a retraction onto the coefficient ring, and its kernel is the
image of the variable ideal. -/
private theorem shifted_zero_section_retraction_of_zero_constant_relations
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {n m : ℕ}
    (πshift : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπshift : Function.Surjective πshift)
    (rels : Fin m → MvPolynomial (Fin n) A)
    (hspan : Ideal.span (Set.range rels) = RingHom.ker πshift.toRingHom)
    (hconst : ∀ j, MvPolynomial.constantCoeff (rels j) = 0) :
    ∃ σ : B →ₐ[A] A, Function.LeftInverse σ (algebraMap A B) ∧
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
  refine ⟨σ, ?_, ?_⟩
  · intro a
    -- Proof comment: the descended zero-evaluation map fixes coefficients, so it is a retraction
    -- of the canonical scalar map.
    have hCa : πshift (MvPolynomial.C a) = algebraMap A B a := by
      simp
    rw [← hCa]
    simpa [evalZero] using hσπ (MvPolynomial.C a)
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

/-- Helper for Lemma 10.126.6: in the quotient of a multivariable polynomial ring, the image of
the powers of a coefficient polynomial `C c` is exactly the powers of its quotient class. -/
private theorem quotient_mvPolynomial_algebraMapSubmonoid_powers_eq
    {A : Type*} [CommRing A] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) A)) (c : A) :
    Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) A)
      (S := MvPolynomial (Fin n) A ⧸ I)
      (Submonoid.powers (MvPolynomial.C c)) =
        Submonoid.powers
          (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A ⧸ I)
            (MvPolynomial.C c)) := by
  -- Proof comment: quotienting preserves the coefficient embedding `C`, so the image of the
  -- powers submonoid remains the powers of the quotient class of the same coefficient polynomial.
  simpa using
    (Algebra.algebraMapSubmonoid_powers
      (R := MvPolynomial (Fin n) A)
      (S := MvPolynomial (Fin n) A ⧸ I)
      (MvPolynomial.C c))

/-- Helper for Lemma 10.126.6: in the first-away source quotient, the image of the powers of
`C g` is exactly the powers of the quotient class of that coefficient polynomial. -/
private theorem final_away_source_quotient_powers_eq
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) (Localization.Away f))
      (S := Qf)
      (Submonoid.powers (MvPolynomial.C c)) =
        Submonoid.powers (Ideal.Quotient.mk K (MvPolynomial.C c)) := by
  intro Qf c
  -- Proof comment: after quotienting, the image of `C g` is definitionally the quotient class
  -- `Ideal.Quotient.mk K (C g)`, so this is exactly the generic quotient-powers lemma.
  change Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) (Localization.Away f))
      (S := MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
      (Submonoid.powers (MvPolynomial.C c)) =
    Submonoid.powers
      (algebraMap (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial.C c))
  simpa using
    quotient_mvPolynomial_algebraMapSubmonoid_powers_eq
      (A := Localization.Away f)
      (n := n)
      (I := K)
      c

/-- Helper for Lemma 10.126.6: the canonical quotient map from the first-away polynomial quotient
to the final-away polynomial quotient sends the class of `ψ` to the class of
`MvPolynomial.map ρfgR ψ`. -/
private theorem final_away_source_quotient_algebraMap_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    letI : Algebra
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) :=
      Ideal.Quotient.algebraQuotientMapQuotient
    algebraMap
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg)
        (Ideal.Quotient.mk K ψ) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
  intro fg ρfgR
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg
  letI : Algebra
      (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
      (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  -- Proof comment: this is exactly the quotient-map computation for the coefficient base-change
  -- homomorphism `MvPolynomial.map ρfgR`, so the quotient representative is unchanged by
  -- normalization.
  rfl

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
private theorem final_away_source_quotient_isLocalizationAway
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    IsLocalization.Away uQ Tfg := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  -- Proof comment: Proposition 10.9.14 is already available on the quotient of the localized
  -- polynomial ring. The only work here is to rewrite its denominator submonoid as the literal
  -- powers of the quotient class `uQ = [C g]`.
  simpa [Localization.Away, Qf, uQ, c,
    final_away_source_quotient_powers_eq (R := R) (n := n) (f := f) (g := g) K] using
    (inferInstance :
      IsLocalization
        (Algebra.algebraMapSubmonoid
          (R := MvPolynomial (Fin n) (Localization.Away f))
          (S := Qf)
          (Submonoid.powers (MvPolynomial.C c)))
        Tfg)

/-- Helper for Lemma 10.126.6: the quotient-localization equivalence from the first-away source
quotient to the final-away polynomial quotient sends a quotient generator to its transported
final-away class. -/
private noncomputable abbrev final_away_source_quotient_localization_algEquiv
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg :=
      ((algebraMap Qf Tfg).comp (algebraMap (Localization.Away f) Qf)).toAlgebra
    Localization.Away uQ ≃ₐ[Localization.Away f] Tfg := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg :=
    ((algebraMap Qf Tfg).comp (algebraMap (Localization.Away f) Qf)).toAlgebra
  letI : IsLocalization.Away uQ Tfg :=
    final_away_source_quotient_isLocalizationAway
      (R := R) (n := n) (f := f) (g := g) K
  -- Proof comment: after the source quotient is recognized as the away localization at `uQ`,
  -- the bridge to the final-away quotient is the canonical localization equivalence.
  simpa [Localization.Away] using
    ((Localization.algEquiv (Submonoid.powers uQ) Tfg).restrictScalars (Localization.Away f))

/-- Helper for Lemma 10.126.6: the source-side quotient-localization equivalence carries the class
of a polynomial `ψ` to the class of its coefficient-wise transport to the final away chart. -/
private theorem final_away_source_quotient_localization_algEquiv_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg :=
      ((algebraMap Qf Tfg).comp (algebraMap (Localization.Away f) Qf)).toAlgebra
    final_away_source_quotient_localization_algEquiv
        (R := R) (n := n) (f := f) (g := g) K
        (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg :=
    ((algebraMap Qf Tfg).comp (algebraMap (Localization.Away f) Qf)).toAlgebra
  letI : IsLocalization.Away uQ Tfg :=
    final_away_source_quotient_isLocalizationAway
      (R := R) (n := n) (f := f) (g := g) K
  -- Proof comment: rewrite the source quotient class as `ψ / 1`, evaluate the canonical
  -- localization equivalence on that generator, and finish with the explicit quotient-map formula.
  rw [← IsLocalization.mk'_one
    (M := Submonoid.powers uQ)
    (S := Localization.Away uQ)
    (x := Ideal.Quotient.mk K ψ)]
  rw [show final_away_source_quotient_localization_algEquiv
      (R := R) (n := n) (f := f) (g := g) K =
    ((Localization.algEquiv (Submonoid.powers uQ) Tfg).restrictScalars (Localization.Away f)) by
      rfl]
  rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
  simpa [Qf, uQ, c] using
    final_away_source_quotient_algebraMap_apply_mk
      (R := R) (n := n) (f := f) (g := g) K ψ

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
private theorem final_away_source_quotient_away_generator_image
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    eQuot
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf eQuot
  -- Proof comment: this is just the quotient comparison on one explicit presentation
  -- generator, namely the coefficient polynomial `C g`.
  change
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g)
  calc
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      πshift (MvPolynomial.C (algebraMap R (Localization.Away f) g)) := by
        exact Ideal.quotientKerAlgEquivOfSurjective_mk
          (f := πshift)
          hπshiftSurj
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    _ = algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g) := by
            simp

/-- Helper for Lemma 10.126.6: after transporting the shifted presentation to the final away
chart, the quotient comparison becomes an algebra equivalence, hence the final-away presentation is
surjective with kernel generated by the transported shifted relations. -/
private theorem final_away_shifted_presentation_surj_ker
    {n m : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (relsFinal : Fin m → MvPolynomial (Fin n) (Localization.Away (f * g)))
    (hrelsFinalSpan :
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom))
    (htransportedKernelLe :
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
          (Localization.Away (algebraMap R S fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap R S fg)
                (Localization.Away (algebraMap R S fg)))
      let ρfgS : Localization.Away (algebraMap R S f) →+*
          Localization.Away (algebraMap R S fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap R S fg))
          (algebraMap R S f) (algebraMap R S g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
        (Localization.awayMap (algebraMap R S) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap R S fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    Function.Surjective πshiftFinal ∧
      RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
  -- TODO: the remaining source-side blocker is to build an explicit
  -- `IsLocalization.Away uQ (MvPolynomial (Fin n) (Localization.Away (f * g)) ⧸ Kfg)` instance for
  -- `uQ = [C g]` in the first-away quotient, so that the localized quotient equivalence
  -- `Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj` can be transported to the final-away
  -- quotient and compared with `final_away_quotient_comparison` on quotient generators.
  --
  -- The new helper `final_away_source_quotient_away_generator_image` already fixes the image of
  -- the away element under the source quotient equivalence; what is still missing is the concrete
  -- quotient-localization instance turning that image computation into an actual conjugacy
  -- `Localization.Away uQ ≃ (MvPolynomial ... ⧸ Kfg)`.
  sorry

-- Proof sketch: write `S` by a finite presentation over `R` and use the local isomorphism
-- `R_p ≃ S_q` to produce a retraction after replacing `R` by `R_f` for some `f ∉ p`. The kernel of
-- that retraction becomes a finitely generated pure ideal near `p`, hence is generated by an
-- idempotent after shrinking once more. The standard idempotent splitting then identifies `S_f`
-- with a product `R_f × C`.
/-- Lemma 10.126.6: if `S` is a finitely presented `R`-algebra, `q` is a prime ideal of `S`
lying over a prime ideal `p` of `R`, and the induced local map `R_𝔭 → S_𝔮` is bijective, then
there exist `f ∉ p` and an `R_f`-algebra `C` such that `S_f ≅ R_f × C` as `R_f`-algebras. -/
theorem exists_away_product_decomposition_of_bijective_localRingHom
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    ∃ (f : R) (_ : f ∉ p),
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      ∃ (C : Type w) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
        Nonempty
          (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
            (Localization.Away f × C)) := by
  -- Route correction: abandon the quasi-finite subalgebra detour and follow the source proof
  -- directly through a finite presentation and common denominator clearing on the presentation
  -- generators.
  obtain ⟨n, π, hπsurj, hπkerfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let localEquiv : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hq.over) hlocal
  let generatorPreimage : Fin n → Localization.AtPrime p := fun i ↦
    localEquiv.symm (algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)))
  have hgeneratorPreimage :
      ∀ i,
        (Localization.localRingHom p q (algebraMap R S) hq.over) (generatorPreimage i) =
          algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)) :=
    generator_preimage_maps_to_variable
      (R := R) (S := S) (p := p) (q := q) hq hlocal π
  obtain ⟨f, hf, a, ha⟩ :=
    exists_notMem_and_common_denominator_atPrime
      (R := R) (p := p) generatorPreimage
  obtain ⟨m, rels, hrels⟩ :
      ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) R,
        Ideal.span (Set.range rels) = RingHom.ker π.toRingHom := by
    -- Proof comment: before shifting variables, fix one explicit finite family generating the
    -- kernel of the original presentation. The new shifted-kernel helpers above show that the same
    -- finite-generation step is available again after the localized translation.
    simpa using Submodule.fg_iff_exists_fin_generating_family.mp hπkerfg
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  have hfq : algebraMap R S f ∉ q := by
    intro hfq
    exact hf (by
      rw [hq.over]
      simpa [Ideal.mem_comap] using hfq)
  let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
      (IsLocalization.map_units (Localization.AtPrime q)
        ((⟨algebraMap R S f, hfq⟩ : q.primeCompl)))
  have hawaySquare :
      ρS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR :=
    away_to_atPrime_square_commutes (R := R) (S := S) (p := p) (q := q) hq hf
  let u : Fin n → Localization.Away f :=
    let denom : Submonoid.powers f := ⟨f, ⟨1, by simp⟩⟩
    fun i ↦ IsLocalization.mk' (Localization.Away f) (a i) denom
  have hu : ∀ i, ρR (u i) = generatorPreimage i :=
    -- Proof comment: the tuple `u = a / f` already recovers the chosen inverse-local preimages in
    -- `R_𝔭`, so the remaining work is purely to compare the localized polynomial presentation with
    -- this concrete tuple.
    away_cleared_tuple_eq_generator_preimage
      (R := R) (p := p) (hf := hf) a generatorPreimage ha
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    away_localization_isScalarTower (R := R) (f := f)
  have hπf :
      ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
          (AlgHom.restrictScalars R
            (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm.toAlgHom)) =
        (AlgHom.restrictScalars R
          (MvPolynomial.aeval
            (fun i ↦
              algebraMap S (Localization.Away (algebraMap R S f))
                (π (MvPolynomial.X i))) :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                Localization.Away (algebraMap R S f))) := by
    -- Proof comment: the first new localization bridge identifies the owner-side conjugated
    -- presentation with the explicit `R_f`-polynomial presentation on coefficients and variables.
    simpa using
      transported_away_presentation_eq_localized_aeval
        (R := R) (S := S) (π := π) (f := f)
  have hπfX :
      ∀ i,
        (AlgHom.restrictScalars R
          (MvPolynomial.aeval
            (fun j ↦
              algebraMap S (Localization.Away (algebraMap R S f))
                (π (MvPolynomial.X j))) :
            MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
              Localization.Away (algebraMap R S f))) (MvPolynomial.X i) =
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i)) := by
    intro i
    -- Proof comment: the explicit localized presentation sends each polynomial variable to the
    -- localized image of the corresponding presentation generator by construction.
    simp
  let πeval :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i)))
  let πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i)) -
          algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
            (u i))
  have hπshiftSub :
      πshift =
        πeval.comp
          (MvPolynomial.aeval (R := Localization.Away f)
            fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
    -- Proof comment: the shifted localized presentation is literally the unshifted presentation
    -- after substituting `X i - u i`.
    simpa [πeval, πshift] using
      shifted_localized_presentation_eq_sub
        (v := fun i ↦
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i)))
        (u := u)
  have hshiftX : ∀ i, ρS (πshift (MvPolynomial.X i)) = 0 := by
    -- Proof comment: after the first shrink, the translated generators vanish in the stalk `S_q`;
    -- this is the source proof's key turning point before descending the zero section.
    simpa [πshift, ρR, ρS] using
      shifted_localized_variables_vanish_at_q
        (R := R) (S := S) (p := p) (q := q) hq (hf := hf) π
        generatorPreimage hgeneratorPreimage u hu
  have hπtransportSurj :
      Function.Surjective
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)).comp
            (AlgHom.restrictScalars R
              (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm.toAlgHom)) := by
    intro y
    obtain ⟨z, hz⟩ :=
      IsLocalization.Away.mapₐ_surjective_of_surjective
        (Aₚ := Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Bₚ := Localization.Away (algebraMap R S f))
        (f := π)
        (a := MvPolynomial.C (σ := Fin n) f)
        hπsurj y
    refine ⟨(localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z, ?_⟩
    -- Proof comment: the conjugated presentation is surjective because the direct away map is
    -- surjective and the polynomial-localization equivalence supplies the needed preimage.
    change (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f))
        ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
          ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z)) = y
    have hz' :
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f))
          ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
            ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z)) =
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)) z := by
      exact congrArg
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)))
        ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm_apply_apply z)
    exact hz'.trans hz
  have hπevalSurj : Function.Surjective πeval := by
    -- Proof comment: the explicit localized presentation `πeval` is the conjugated away
    -- presentation from `hπf`, so surjectivity transfers across that identification.
    have hsurjR :
        Function.Surjective
          (AlgHom.restrictScalars R
            (MvPolynomial.aeval
              (fun i ↦
                algebraMap S (Localization.Away (algebraMap R S f))
                  (π (MvPolynomial.X i))) :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                Localization.Away (algebraMap R S f))) := by
      rw [← hπf]
      exact hπtransportSurj
    simpa [πeval] using hsurjR
  have hπshiftSurj : Function.Surjective πshift := by
    -- Proof comment: the shifted presentation differs from `πeval` only by the invertible
    -- translation `X i ↦ X i - u i`, so surjectivity persists after the first shrink.
    exact surjective_shifted_presentation
      (πeval := πeval)
      hπevalSurj
      u
      πshift
      hπshiftSub
  obtain ⟨mShift, relsShift, hrelsShift, hconstShift⟩ :=
    exists_sign_aligned_shifted_kernel_family
      (R := R) (S := S) (p := p) (q := q) hq (hf := hf)
      (πeval := πeval) hπevalSurj u (πshift := πshift) hπshiftSub
      ρR ρS hawaySquare hlocal hshiftX
  obtain ⟨g₂, hg₂, hconstZero⟩ :=
    exists_notMem_zero_shifted_constants_after_second_shrink
      (R := R)
      (p := p)
      (hf := hf)
      (rels := relsShift)
      hconstShift
  let fg : R := f * g₂
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g₂
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g₂)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g₂)
  have hfinalAwaySquare :
      ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.awayMap (algebraMap R S) fg).comp ρfgR := by
    -- Proof comment: the second shrink now has the same canonical commuting square as the first
    -- shrink to the stalks, so the remaining work can be phrased on the final away chart without
    -- further transport through ad hoc coercions.
    simpa [fg, ρfgR, ρfgS] using
      final_away_square_commutes (R := R) (S := S) f g₂
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
  let relsFinal : Fin mShift → MvPolynomial (Fin n) (Localization.Away fg) :=
    fun j ↦ MvPolynomial.map ρfgR (relsShift j)
  have hrelsFinalConstZero :
      ∀ j, MvPolynomial.constantCoeff (relsFinal j) = 0 := by
    intro j
    -- Proof comment: the second shrink was chosen exactly so that the transported constant
    -- coefficients of the shifted relations literally vanish in the final away chart `R_(fg)`.
    dsimp [relsFinal]
    simpa [fg, ρfgR] using hconstZero j
  have hrelsFinalSpan :
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) := by
    -- Proof comment: package the transported relation family as the coefficient-wise image of the
    -- already controlled shifted kernel ideal on `R_f`.
    simpa [fg, ρfgR, relsFinal] using
      final_away_relations_span_eq_map_shifted_kernel
        (R := R)
        (relsShift := relsShift)
        (K := RingHom.ker πshift.toRingHom)
        hrelsShift
  have hπshiftFinalMap :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away f),
        πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ) := by
    -- Proof comment: this is the pointwise transport bridge from the shifted presentation on
    -- `R_f` to the final away chart `R_(fg)`.
    intro ψ
    simpa [fg, ρfgR, ρfgS, πshiftFinal] using
      final_away_shifted_presentation_map
        (R := R)
        (S := S)
        (ψ := ψ)
        (πshift := πshift)
        (f := f)
        (g := g₂)
  have hrelsFinalSpanLe :
      Ideal.span (Set.range relsFinal) ≤ RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: every transported shifted relation still vanishes under the final-away
    -- presentation, so their span already lies in the new kernel.
    refine Ideal.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with ⟨j, rfl⟩
    change πshiftFinal (relsFinal j) = 0
    have hrelShift : πshift (relsShift j) = 0 := by
      have hrelShiftMem : relsShift j ∈ RingHom.ker πshift.toRingHom := by
        rw [← hrelsShift]
        exact Ideal.subset_span (Set.mem_range_self j)
      simpa [RingHom.mem_ker] using hrelShiftMem
    calc
      πshiftFinal (relsFinal j) = ρfgS (πshift (relsShift j)) := by
        simpa [relsFinal] using hπshiftFinalMap (relsShift j)
      _ = 0 := by simp [hrelShift]
  have htransportedKernelLe :
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: after identifying the transported relation span with the mapped old kernel,
    -- the already proved vanishing of the transported relations gives the forward kernel
    -- inclusion on the final away chart.
    rw [← hrelsFinalSpan]
    exact hrelsFinalSpanLe
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
  let qComp :
      (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    final_away_quotient_comparison
      (R := R)
      (S := S)
      (πshift := πshift)
      (f := f)
      (g := g₂)
      htransportedKernelLe
  have hqComp_apply :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away f),
        qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) = ρfgS (πshift ψ) := by
    intro ψ
    -- Proof comment: the descended quotient comparison agrees with the transported shifted
    -- presentation on every generator coming from the first away chart.
    simpa [Kfg, qComp, fg, ρfgR, ρfgS] using
      final_away_quotient_comparison_apply_mk
        (R := R)
        (S := S)
        (πshift := πshift)
        (f := f)
        (g := g₂)
        htransportedKernelLe
        ψ
  have hπshiftFinal :
      Function.Surjective πshiftFinal ∧
        RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
    -- Proof comment: this packages the entire final-away quotient-localization transport, so the
    -- main theorem can now continue with the zero-section retraction exactly as in the source
    -- argument.
    simpa [Kfg, πshiftFinal, fg, ρfgR, ρfgS] using
      final_away_shifted_presentation_surj_ker
        (R := R)
        (S := S)
        (πshift := πshift)
        (f := f)
        (g := g₂)
        hπshiftSurj
        relsFinal
        hrelsFinalSpan
        htransportedKernelLe
  obtain ⟨hπshiftFinalSurj, hπshiftFinalKer⟩ := hπshiftFinal
  obtain ⟨σfg, hσfg, hkerσfg⟩ :=
    shifted_zero_section_retraction_of_zero_constant_relations
      (πshift := πshiftFinal)
      hπshiftFinalSurj
      relsFinal
      hπshiftFinalKer.symm
      hrelsFinalConstZero
  -- Proof comment: `ha` is exactly the source's first shrinking step: after replacing `R` by
  -- `R_f`, every presentation generator has an inverse-local image with denominator `f`, and the
  -- shifted presentation kernel has now been reduced to a finite family whose constant
  -- coefficients already vanish in `R_𝔭`. The second shrink has now replaced that stalk-vanishing
  -- statement by literal coefficient equalities in the final away chart `R_(f * g₂)`, and the
  -- zero section has descended to a retraction `σfg : S_(fg) → R_(fg)` with explicit kernel
  -- formula `hkerσfg`.
  --
  -- TODO: the remaining blocker is now purely the semilocal descent from the source proof.
  -- One must localize the quotient by `RingHom.ker σfg.toRingHom` at `q`, identify that quotient
  -- with `S_q`, read purity of the localized kernel from the resulting flat quotient, and then
  -- descend the idempotent generator back to a further away chart before invoking
  -- `away_product_decomposition_of_idempotent_kernel_retraction`.
  sorry

end
