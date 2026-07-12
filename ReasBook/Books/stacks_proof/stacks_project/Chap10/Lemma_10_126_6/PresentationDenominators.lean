import StacksProject_2024.Chap10.Lemma_10_126_6.AwayTransport

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: an `A`-algebra map out of a finite polynomial algebra is the
constant-coefficient map once every polynomial variable maps to zero. -/
theorem mvPolynomial_image_eq_constantCoeff_of_variables_zero
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
theorem constantCoeff_map_zero_of_mem_ker_of_variables_zero
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
theorem localRingHom_apply_symm_of_bijective
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
theorem generator_preimage_maps_to_variable
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
theorem away_cleared_tuple_eq_generator_preimage
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
theorem shifted_localized_presentation_eq_sub
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
theorem shifted_localized_variables_vanish_at_q
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
theorem exists_sign_aligned_shifted_kernel_family
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
theorem awayToAwayRight_eq_zero_of_mul_eq_zero
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
theorem exists_notMem_zero_family_after_second_shrink_atPrime
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
theorem exists_notMem_zero_shifted_constants_after_second_shrink
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

end
