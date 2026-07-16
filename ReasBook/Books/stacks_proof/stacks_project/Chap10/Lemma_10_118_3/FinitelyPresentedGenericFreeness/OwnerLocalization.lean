import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.PolynomialModels

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: a localization of modules over an algebra remains a
localization after restricting scalars to the source ring and pulling back the denominator. -/
private lemma isLocalizedModule_restrictScalars_of_algebraMapSubmonoid
    {A : Type*} [CommSemiring A] [Algebra R A]
    {N₀ : Type*} [AddCommMonoid N₀] [Module A N₀] [Module R N₀] [IsScalarTower R A N₀]
    {N₁ : Type*} [AddCommMonoid N₁] [Module A N₁] [Module R N₁] [IsScalarTower R A N₁]
    {T : Submonoid R} (f : N₀ →ₗ[A] N₁)
    [IsLocalizedModule (Algebra.algebraMapSubmonoid A T) f] :
    IsLocalizedModule T (f.restrictScalars R) where
  map_units t := by
    -- Proof comment: units for the image denominator act by the same underlying endomorphism
    -- after scalar restriction.
    have hunit := IsLocalizedModule.map_units f
      (⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem (S := A) t⟩ :
        Algebra.algebraMapSubmonoid A T)
    rw [Module.End.isUnit_iff] at hunit ⊢
    convert hunit using 1
    ext y
    simp [Module.algebraMap_end_apply, algebraMap_smul A]
  surj y := by
    -- Proof comment: a localized denominator in the image submonoid is represented by an
    -- original denominator from `R`, so the same numerator works after restricting scalars.
    obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj (Algebra.algebraMapSubmonoid A T) f y
    rcases t with ⟨_, t, htT, rfl⟩
    exact ⟨⟨x, ⟨t, htT⟩⟩, by
      simpa [Submonoid.smul_def, algebraMap_smul A] using ht⟩
  exists_of_eq {x₁ x₂} h := by
    -- Proof comment: the equalizer denominator descends along the same image-submonoid
    -- representation.
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq
      (S := Algebra.algebraMapSubmonoid A T) (f := f) h
    rcases t with ⟨_, t, htT, rfl⟩
    exact ⟨⟨t, htT⟩, by
      simpa [Submonoid.smul_def, algebraMap_smul A] using ht⟩

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: the polynomial presentation coming from a scalar tower sends
the coefficient denominator `C f` to the owner denominator `f` in `S`. -/
lemma localizedCoeffAwayOwner_denominator_eq
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S)
        (MvPolynomial.C (σ := Fin n) f) =
      algebraMap R S f := by
  -- Proof comment: this is the existing scalar-tower computation, repackaged for the canonical
  -- algebra hom used by the owner-localization construction below.
  simpa using mvPolynomialPresentation_algebraMap_C (R := R) (S := S) (n := n) f

/-- Helper for Chap10 Lemma 10 118 3: the owner localization `S_f` receives the localized
polynomial algebra by evaluating variables at their localized presentation images. -/
noncomputable abbrev localizedCoeffAwayOwnerAlgHom
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
      Localization.Away (algebraMap R S f) :=
  MvPolynomial.aeval fun i : Fin n =>
    algebraMap S (Localization.Away (algebraMap R S f))
      (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i))

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: the owner evaluation hom sends localized coefficients to
the corresponding elements of `S_f`. -/
theorem localizedCoeffAwayOwnerAlgHom_C
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    (r : Localization.Away f) :
    localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f
        (MvPolynomial.C (σ := Fin n) r) =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r := by
  -- Proof comment: `localizedCoeffAwayOwnerAlgHom` is an `R_f`-algebra hom, so its coefficient
  -- computation is exactly its `commutes` field.
  simpa [MvPolynomial.algebraMap_eq] using
    (localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f).commutes r

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: the owner evaluation hom sends each polynomial variable to
the localized image of the original presentation variable. -/
theorem localizedCoeffAwayOwnerAlgHom_X
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    (i : Fin n) :
    localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f
        (MvPolynomial.X i) =
      algebraMap S (Localization.Away (algebraMap R S f))
        (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i)) := by
  -- Proof comment: variables are the chosen evaluation points in the `aeval` construction.
  simp [localizedCoeffAwayOwnerAlgHom]

/-- Helper for Chap10 Lemma 10 118 3: the owner localization of `S` at `f` carries the
coefficient-localized polynomial algebra structure induced by the original polynomial action. -/
noncomputable abbrev localizedCoeffAwayOwnerAlgebra
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
  (localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f).toRingHom.toAlgebra

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: the owner algebra structure is compatible with the
coefficient-localized base ring by construction. -/
theorem localizedCoeffAwayOwnerAlgebra_isScalarTower
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) := by
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  -- Proof comment: the algebra was built from an `R_f`-algebra hom, so the scalar-tower
  -- compatibility is precisely the coefficient-commutation of that hom.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  exact (localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f).commutes r |>.symm

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: the owner algebra structure on `S_f` extends the original
polynomial presentation action through `R_f[x]`. -/
theorem localizedCoeffAwayOwnerAlgebra_isScalarTower_over_source
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    let A := MvPolynomial (Fin n) (Localization.Away f)
    letI : Algebra A (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    IsScalarTower (MvPolynomial (Fin n) R) A
      (Localization.Away (algebraMap R S f)) := by
  dsimp
  let P := MvPolynomial (Fin n) R
  let A := MvPolynomial (Fin n) (Localization.Away f)
  let B := Localization.Away (algebraMap R S f)
  letI : Algebra A B := localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  have hring :
      (localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f).toRingHom.comp
          (algebraMap P A) =
        (algebraMap S B).comp (algebraMap P S) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      -- Proof comment: coefficients compare by the owner away map `R_f → S_f` and the
      -- original scalar-tower equation `R → R[x] → S`.
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_def,
        MvPolynomial.map_C]
      change localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f
          (MvPolynomial.C (algebraMap R (Localization.Away f) r)) =
        algebraMap S B (algebraMap P S (MvPolynomial.C (σ := Fin n) r))
      rw [localizedCoeffAwayOwnerAlgHom_C,
        mvPolynomialPresentation_algebraMap_C (R := R) (S := S) (n := n)]
      have hbase :
          algebraMap (Localization.Away f) B (algebraMap R (Localization.Away f) r) =
            algebraMap R B r := by
        change (Localization.awayMapₐ (Algebra.ofId R S) f)
            (algebraMap R (Localization.Away f) r) =
          algebraMap R B r
        exact (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
      rw [hbase]
      exact (IsScalarTower.algebraMap_apply R S B r).symm
    · intro i
      -- Proof comment: variables compare by the definition of the owner evaluation hom.
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_def,
        MvPolynomial.map_X]
      change localizedCoeffAwayOwnerAlgHom (R := R) (S := S) (n := n) f
          (MvPolynomial.X i) =
        algebraMap S B (algebraMap P S (MvPolynomial.X i))
      rw [localizedCoeffAwayOwnerAlgHom_X]
  refine IsScalarTower.of_algebraMap_smul ?_
  intro p x
  -- Proof comment: the ring-hom equality on `P` turns the tower condition into multiplication by
  -- the same element of the owner localization.
  have hmap := congrArg (fun F : P →+* B => F p) hring
  rw [Algebra.smul_def, Algebra.smul_def]
  exact congrArg (fun b : B => b * x) hmap

/-- Helper for Chap10 Lemma 10 118 3: once `S_f` is an algebra over the coefficient-localized
polynomial ring, the owner localization of `M` restricts scalars along that algebra map. -/
noncomputable abbrev localizedCoeffAwayOwnerModule
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))] :
    Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
  Module.compHom (LocalizedModule.Away (algebraMap R S f) M)
    (algebraMap (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)))

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the restricted owner module structure is compatible with
the localized owner algebra action by construction. -/
theorem localizedCoeffAwayOwnerModule_isScalarTower
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))] :
    letI : Module (MvPolynomial (Fin n) (Localization.Away f))
        (LocalizedModule.Away (algebraMap R S f) M) :=
      localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
    IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) := by
  letI : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
  -- Proof comment: `localizedCoeffAwayOwnerModule` is exactly `Module.compHom` along the
  -- localized algebra map, so the standard compHom tower instance applies.
  exact IsScalarTower.of_compHom
    (MvPolynomial (Fin n) (Localization.Away f))
    (Localization.Away (algebraMap R S f))
    (LocalizedModule.Away (algebraMap R S f) M)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the owner module structure on `M_f` extends the original
polynomial presentation action through `R_f[x]`. -/
theorem localizedCoeffAwayOwnerModule_isScalarTower_over_source
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M] :
    let A := MvPolynomial (Fin n) (Localization.Away f)
    let B := Localization.Away (algebraMap R S f)
    letI : Algebra A B := localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    letI : Module A (LocalizedModule.Away (algebraMap R S f) M) :=
      localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
    IsScalarTower (MvPolynomial (Fin n) R) A
      (LocalizedModule.Away (algebraMap R S f) M) := by
  dsimp
  let P := MvPolynomial (Fin n) R
  let A := MvPolynomial (Fin n) (Localization.Away f)
  let B := Localization.Away (algebraMap R S f)
  letI : Algebra A B := localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : IsScalarTower P A B :=
    localizedCoeffAwayOwnerAlgebra_isScalarTower_over_source
      (R := R) (S := S) (n := n) f
  letI : Module A (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
  refine ⟨?_⟩
  intro p a x
  -- Proof comment: unfold the restricted `A`-action to the owner algebra `B`.
  change algebraMap A B (algebraMap P A p * a) • x = p • (algebraMap A B a • x)
  rw [map_mul]
  rw [← IsScalarTower.algebraMap_apply P A B p]
  -- Proof comment: after the algebra map comparison, the existing tower `P → B → M_f` closes.
  calc
    ((algebraMap P B) p * (algebraMap A B) a) • x =
        (algebraMap P B) p • ((algebraMap A B) a • x) := by
      exact mul_smul (algebraMap P B p) (algebraMap A B a) x
    _ = p • ((algebraMap A B) a • x) := by
      exact IsScalarTower.algebraMap_smul B p ((algebraMap A B) a • x)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the owner localization of `S` is also the localization of
`S` as an `R[x]`-module after inverting the coefficient polynomial `C f`. -/
lemma localizedCoeffAwayOwnerSelf_isLocalizedModule
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    IsLocalizedModule (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      ((Algebra.linearMap S (Localization.Away (algebraMap R S f))).restrictScalars
        (MvPolynomial (Fin n) R)) := by
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  let B := Localization.Away (algebraMap R S f)
  -- Proof comment: the image of the coefficient denominator in `S` is exactly the owner
  -- denominator `f`, so the usual owner localization is a localization at the image submonoid.
  have hsub : Algebra.algebraMapSubmonoid S U = Submonoid.powers (algebraMap R S f) := by
    dsimp [U]
    rw [Algebra.algebraMapSubmonoid_powers]
    rw [mvPolynomialPresentation_algebraMap_C (R := R) (S := S) (n := n) f]
  have hloc : IsLocalizedModule (Algebra.algebraMapSubmonoid S U)
      (Algebra.linearMap S B) := by
    rw [hsub]
    infer_instance
  -- Proof comment: pull the owner-localization universal property back from `S` to the
  -- polynomial presentation ring.
  exact isLocalizedModule_restrictScalars_of_algebraMapSubmonoid
    (R := P) (A := S) (N₀ := S) (N₁ := B) (T := U) (Algebra.linearMap S B)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the direct coefficient-away localization of `S` maps
canonically to the owner localization `S_f` as an `R[x]`-linear equivalence. -/
noncomputable abbrev localizedCoeffAwayOwnerSelfLinearEquiv
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S ≃ₗ[MvPolynomial (Fin n) R]
      Localization.Away (algebraMap R S f) :=
  letI := localizedCoeffAwayOwnerSelf_isLocalizedModule (R := R) (S := S) (n := n) f
  IsLocalizedModule.linearEquiv
    (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (LocalizedModule.mkLinearMap (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) S)
    ((Algebra.linearMap S (Localization.Away (algebraMap R S f))).restrictScalars
      (MvPolynomial (Fin n) R))

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the owner comparison equivalence sends a numerator
`s / 1` to the corresponding localized element of `S_f`. -/
@[simp] theorem localizedCoeffAwayOwnerSelfLinearEquiv_apply_mk_one
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    (s : S) :
    localizedCoeffAwayOwnerSelfLinearEquiv (R := R) (S := S) (n := n) f
      (LocalizedModule.mk s 1) =
    algebraMap S (Localization.Away (algebraMap R S f)) s := by
  letI := localizedCoeffAwayOwnerSelf_isLocalizedModule (R := R) (S := S) (n := n) f
  -- Proof comment: the equivalence was built by uniqueness of localization, so it agrees with
  -- the owner localization map on all canonical numerators.
  simpa [localizedCoeffAwayOwnerSelfLinearEquiv]
    using (IsLocalizedModule.linearEquiv_apply
      (S := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (f := LocalizedModule.mkLinearMap (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) S)
      (g := (Algebra.linearMap S (Localization.Away (algebraMap R S f))).restrictScalars
        (MvPolynomial (Fin n) R)) s)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the direct coefficient-away localization of `S` maps
canonically to the owner localization `S_f` as an `R_f[x]`-linear equivalence. -/
noncomputable abbrev localizedCoeffAwayOwnerSelfCoeffLinearEquiv
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] :
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
      localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)]
      Localization.Away (algebraMap R S f) :=
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  let A := MvPolynomial (Fin n) (Localization.Away f)
  letI : Algebra A (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : IsLocalization U A := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  letI : IsScalarTower P A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S) :=
    away_polynomial_module_isScalarTower_over_source (R := R) (n := n) f
  letI : IsScalarTower P A (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra_isScalarTower_over_source
      (R := R) (S := S) (n := n) f
  (localizedCoeffAwayOwnerSelfLinearEquiv (R := R) (S := S) (n := n) f
    ).extendScalarsOfIsLocalization U A

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the owner localization of `M` is also the localization of
`M` as an `R[x]`-module after inverting the coefficient polynomial `C f`. -/
lemma localizedCoeffAwayOwnerModule_isLocalizedModule
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M] :
    IsLocalizedModule (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M).restrictScalars
        (MvPolynomial (Fin n) R)) := by
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  -- Proof comment: as for `S`, the image of `C f` in the owner algebra is the denominator
  -- defining the usual localized module `M_f`.
  have hsub : Algebra.algebraMapSubmonoid S U = Submonoid.powers (algebraMap R S f) := by
    dsimp [U]
    rw [Algebra.algebraMapSubmonoid_powers]
    rw [mvPolynomialPresentation_algebraMap_C (R := R) (S := S) (n := n) f]
  have hloc : IsLocalizedModule (Algebra.algebraMapSubmonoid S U)
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M) := by
    rw [hsub]
    infer_instance
  -- Proof comment: pull the localized-module universal property back along the polynomial
  -- presentation action.
  exact isLocalizedModule_restrictScalars_of_algebraMapSubmonoid
    (R := P) (A := S) (N₀ := M)
    (N₁ := LocalizedModule.Away (algebraMap R S f) M) (T := U)
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the direct coefficient-away localization of `M` maps
canonically to the owner localization `M_f` as an `R[x]`-linear equivalence. -/
noncomputable abbrev localizedCoeffAwayOwnerModuleLinearEquiv
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M] :
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M ≃ₗ[MvPolynomial (Fin n) R]
      LocalizedModule.Away (algebraMap R S f) M :=
  letI := localizedCoeffAwayOwnerModule_isLocalizedModule (R := R) (S := S) (M := M) (n := n) f
  IsLocalizedModule.linearEquiv
    (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (LocalizedModule.mkLinearMap (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) M)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M).restrictScalars
      (MvPolynomial (Fin n) R))

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the owner module comparison equivalence sends a numerator
`m / 1` to the corresponding localized element of `M_f`. -/
@[simp] theorem localizedCoeffAwayOwnerModuleLinearEquiv_apply_mk_one
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M]
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    (m : M) :
    localizedCoeffAwayOwnerModuleLinearEquiv (R := R) (S := S) (M := M) (n := n) f
      (LocalizedModule.mk m 1) =
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M m := by
  letI := localizedCoeffAwayOwnerModule_isLocalizedModule (R := R) (S := S) (M := M) (n := n) f
  -- Proof comment: uniqueness of localization again identifies the comparison on canonical
  -- numerators with the owner localized-module map.
  simpa [localizedCoeffAwayOwnerModuleLinearEquiv]
    using (IsLocalizedModule.linearEquiv_apply
      (S := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (f := LocalizedModule.mkLinearMap (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) M)
      (g := (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M).restrictScalars
        (MvPolynomial (Fin n) R)) m)

omit [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 118 3: the direct coefficient-away localization of `M` maps
canonically to the owner localization `M_f` as an `R_f[x]`-linear equivalence. -/
noncomputable abbrev localizedCoeffAwayOwnerModuleCoeffLinearEquiv
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M] :
    let A := MvPolynomial (Fin n) (Localization.Away f)
    let B := Localization.Away (algebraMap R S f)
    letI : Algebra A B := localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
    letI : Module A (LocalizedModule.Away (algebraMap R S f) M) :=
      localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)]
      LocalizedModule.Away (algebraMap R S f) M :=
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  let A := MvPolynomial (Fin n) (Localization.Away f)
  let B := Localization.Away (algebraMap R S f)
  letI : Algebra A B := localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : IsLocalization U A := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  letI : IsScalarTower P A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M) :=
    away_polynomial_module_isScalarTower_over_source (R := R) (n := n) f
  letI : Module A (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
  letI : IsScalarTower P A (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule_isScalarTower_over_source
      (R := R) (S := S) (M := M) (n := n) f
  (localizedCoeffAwayOwnerModuleLinearEquiv (R := R) (S := S) (M := M) (n := n) f
    ).extendScalarsOfIsLocalization U A

end
