import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.PolynomialShift

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: localizing the coefficients away from `f` localizes the whole
polynomial ring away from `C f`. -/
theorem localized_mvPolynomial_isLocalization
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
noncomputable abbrev localized_mvPolynomial_algEquiv_over_base
    {n : ℕ} (f : R) :
    Localization.Away (MvPolynomial.C (σ := Fin n) f) ≃ₐ[MvPolynomial (Fin n) R]
      MvPolynomial (Fin n) (Localization.Away f) :=
  letI := localized_mvPolynomial_isLocalization (R := R) (n := n) f
  IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (Localization.Away (MvPolynomial.C (σ := Fin n) f))
    (MvPolynomial (Fin n) (Localization.Away f))

/-- Helper for Lemma 10.126.6: under the canonical polynomial-localization equivalence, a
coefficient coming from `R` is sent back to the same coefficient in the owner localization. -/
theorem localized_mvPolynomial_algEquiv_over_base_symm_C
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
theorem localized_mvPolynomial_algEquiv_over_base_symm_X
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
theorem localized_mvPolynomial_algEquiv_over_base_symm_eq_localization_map
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
theorem mvPolynomial_C_mem_powers
    {n : ℕ} {f : R} (y : Submonoid.powers f) :
    MvPolynomial.C (σ := Fin n) (y : R) ∈
      Submonoid.powers (MvPolynomial.C (σ := Fin n) f) := by
  rcases y with ⟨y, ⟨m, rfl⟩⟩
  -- Proof comment: coefficient embedding commutes with powers, so `C (f^m) = (C f)^m`.
  exact ⟨m, by simp⟩

/-- Helper for Lemma 10.126.6: under the canonical polynomial-localization equivalence, a
localized coefficient `x / y` is sent back to the owner-side localization class `C x / C y`. -/
theorem localized_mvPolynomial_algEquiv_over_base_symm_C_mk'
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
theorem awayMap_algebraMap_eq_algebraMap (f : R) :
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
theorem direct_away_map_on_owner_generators
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
theorem transported_away_presentation_coeff_eq_awayMap
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
theorem transported_away_presentation_coeff_mk'
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
theorem transported_away_presentation_comp_coeff
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
theorem away_localization_isScalarTower (f : R) :
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
theorem transported_away_presentation_eq_localized_aeval
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

end
