import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.FinitelyPresentedModels

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: under a polynomial presentation scalar tower, acting by a
constant polynomial agrees with acting by the original coefficient. -/
lemma mvPolynomialPresentation_algebraMap_C
    {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    (r : R) :
    algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C (σ := Fin n) r) =
      algebraMap R S r := by
  -- Proof comment: this is the pointwise form of the scalar-tower algebra-map identity.
  have h := IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) S r
  simpa using h.symm

/-- Helper for Lemma 10.118.3: after inverting a nonzero `f`, every nonzero element of `R`
remains a non-zero-divisor in `R_f`. This is the regularity invariant behind the source inclusion
`N'_f ⊂ N'_K`. -/
lemma away_nonZeroDivisors_le
    {f : R} (hf : f ≠ 0) :
    Algebra.algebraMapSubmonoid (Localization.Away f) (nonZeroDivisors R) ≤
      nonZeroDivisors (Localization.Away f) := by
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  -- Proof comment: once `R_f` is known to be a domain, the canonical localization map preserves
  -- non-zero-divisors.
  simpa [Algebra.algebraMapSubmonoid] using
    (IsLocalization.map_nonZeroDivisors_le
      (M := Submonoid.powers f)
      (R := R)
      (S := Localization.Away f))

/-- Helper for Lemma 10.118.3: a free module over `R_f` injects into the further localization that
inverts all nonzero elements of `R`. -/
lemma injective_generic_fiber_map_of_free_away_source
    {f : R} (hf : f ≠ 0)
    {N : Type w} [AddCommGroup N] [Module (Localization.Away f) N]
    [Module.Free (Localization.Away f) N] :
    Function.Injective
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (Localization.Away f) (nonZeroDivisors R)) N) := by
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  -- Proof comment: apply the free-module localization injectivity criterion with the regularity
  -- submonoid from `away_nonZeroDivisors_le`.
  exact localizedModule_mkLinearMap_injective_of_free
    (A := Localization.Away f)
    (T := Algebra.algebraMapSubmonoid (Localization.Away f) (nonZeroDivisors R))
    (N := N)
    (away_nonZeroDivisors_le (R := R) hf)

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.118.3: localizing `R[x_1, ..., x_n]` away from `C f` is the same as
forming the polynomial ring over `R_f`. -/
theorem away_mvPolynomial_C_isLocalization
    {n : ℕ} (f : R) :
    IsLocalization (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (MvPolynomial (Fin n) (Localization.Away f)) := by
  -- Proof comment: localize coefficients away from `f` first, then identify the image submonoid
  -- with the powers of `C f` inside the polynomial ring.
  simpa [Submonoid.map_powers] using
    (MvPolynomial.isLocalization (σ := Fin n) (M := Submonoid.powers f)
      (S := Localization.Away f))

/-- Helper for Lemma 10.118.3: the owner-side away localization at `C f` is canonically the
polynomial ring over the base away localization `R_f`. -/
noncomputable abbrev away_mvPolynomial_C_algEquiv
    {n : ℕ} (f : R) :
    Localization.Away (MvPolynomial.C (σ := Fin n) f) ≃ₐ[MvPolynomial (Fin n) R]
      MvPolynomial (Fin n) (Localization.Away f) :=
  letI := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (Localization.Away (MvPolynomial.C (σ := Fin n) f))
    (MvPolynomial (Fin n) (Localization.Away f))

/-- Helper for Lemma 10.118.3: the inverse polynomial-away equivalence sends coefficients to the
matching coefficients in the owner localization. -/
theorem away_mvPolynomial_C_algEquiv_symm_C
    {n : ℕ} (f r : R) :
    (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
        (MvPolynomial.C (algebraMap R (Localization.Away f) r)) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.C (σ := Fin n) r) := by
  letI := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  -- Proof comment: both sides are the localization class of `C r / 1`.
  simpa [away_mvPolynomial_C_algEquiv, IsLocalization.mk'_one,
    MvPolynomial.isLocalization_C_mk'] using
    (IsLocalization.algEquiv_symm_mk'
      (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := MvPolynomial (Fin n) (Localization.Away f))
      (x := MvPolynomial.C (σ := Fin n) r)
      (y := (1 : Submonoid.powers (MvPolynomial.C (σ := Fin n) f))))

/-- Helper for Lemma 10.118.3: the inverse polynomial-away equivalence sends each variable to the
matching variable in the owner localization. -/
theorem away_mvPolynomial_C_algEquiv_symm_X
    {n : ℕ} (f : R) (i : Fin n) :
    (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
        (MvPolynomial.X i) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (MvPolynomial.X i) := by
  letI := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  -- Proof comment: the same localization formula with denominator `1` handles variables too.
  simpa [away_mvPolynomial_C_algEquiv, IsLocalization.mk'_one] using
    (IsLocalization.algEquiv_symm_mk'
      (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
      (S := Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (Q := MvPolynomial (Fin n) (Localization.Away f))
      (x := MvPolynomial.X i)
      (y := (1 : Submonoid.powers (MvPolynomial.C (σ := Fin n) f))))

/-- Helper for Lemma 10.118.3: the inverse polynomial-away equivalence is the canonical
localization map out of `R[x_1, ..., x_n]`. -/
theorem away_mvPolynomial_C_algEquiv_symm_eq_localization_map
    {n : ℕ} (f : R) :
    letI := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
    (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingHom =
      IsLocalization.map
        (M := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
        (S := MvPolynomial (Fin n) (Localization.Away f))
        (Q := Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (g := RingHom.id (MvPolynomial (Fin n) R))
        (by
          intro z hz
          simpa using hz) := by
  letI := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  -- Proof comment: compare the two ring maps on coefficients and variables, then apply the
  -- standard extensionality theorem for multivariate polynomials.
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    simpa using away_mvPolynomial_C_algEquiv_symm_C (R := R) (n := n) f r
  · intro i
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    simpa using away_mvPolynomial_C_algEquiv_symm_X (R := R) (n := n) f i

/-- Helper for Chap10 Lemma 10 118 3: after normalizing `R[x]_(C f)` as `R_f[x]`,
the inverse normalization followed by coefficient inclusion is the canonical away map
`R_f → R[x]_(C f)`. -/
theorem away_mvPolynomial_C_algEquiv_symm_comp_C
    {n : ℕ} (f : R) :
    ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingHom.comp
        (MvPolynomial.C : Localization.Away f →+* MvPolynomial (Fin n) (Localization.Away f))) =
      Localization.awayMap
        (MvPolynomial.C (σ := Fin n) : R →+* MvPolynomial (Fin n) R) f := by
  -- Proof comment: maps out of `R_f` are determined by their values on the original
  -- coefficients, where the pointwise coefficient computation was proved above.
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply]
  change (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
      (MvPolynomial.C (algebraMap R (Localization.Away f) r)) =
    (Localization.awayMap (MvPolynomial.C (σ := Fin n) : R →+* MvPolynomial (Fin n) R) f)
      (algebraMap R (Localization.Away f) r)
  rw [away_mvPolynomial_C_algEquiv_symm_C]
  simp [IsLocalization.Away.map]

/-- Helper for Chap10 Lemma 10 118 3: the algebra map induced by the polynomial away map is the
canonical coefficient away map. -/
theorem away_mvPolynomial_C_awayMapₐ_toAlgebra_algebraMap
    {n : ℕ} (f : R) :
    let P := MvPolynomial (Fin n) R
    let B := Localization.Away (MvPolynomial.C (σ := Fin n) f)
    let algAB := (Localization.awayMapₐ (Algebra.ofId R P) f).toAlgebra
    letI : Algebra (Localization.Away f) B := algAB
    algebraMap (Localization.Away f) B =
      Localization.awayMap (MvPolynomial.C (σ := Fin n) : R →+* MvPolynomial (Fin n) R) f := by
  -- Proof comment: both ring maps are produced by the same localization map out of `R_f`.
  dsimp
  rfl

/-- Helper for Lemma 10.118.3: transport the away-localized polynomial module structure along the
canonical ring equivalence `R[x]_(C f) ≃ R_f[x]`. -/
noncomputable instance away_polynomial_module_over_coeff_localization
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N] :
    Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
  Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)
    ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingHom)

/-- Helper for Lemma 10.118.3: restricting scalars from `R_f[x_1, \dots, x_n]` gives the
canonical `R_f`-module structure on the away-localized polynomial module. -/
noncomputable instance away_polynomial_module_over_base_localization
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N] :
    Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
  Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)
    (algebraMap (Localization.Away f) (MvPolynomial (Fin n) (Localization.Away f)))

/-- Helper for Lemma 10.118.3: the restricted `R_f`-action on the away-localized polynomial module
is scalar multiplication by the corresponding element of `R[x]_(C f)`. -/
lemma away_polynomial_source_coeff_smul_eq
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (r : Localization.Away f)
    (x : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :
    r • x =
      ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
        (MvPolynomial.C (σ := Fin n) r)) • x := by
  -- Proof comment: the restricted `R_f`-module structure is obtained by `compHom` along the
  -- coefficient embedding `R_f → R_f[x_1, \dots, x_n]`.
  rfl

/-- Helper for Chap10 Lemma 10 118 3: the restricted `R_f`-action is equivalently the
canonical away-map action through `R[x_1, \dots, x_n]_(C f)`. -/
lemma away_polynomial_source_smul_eq_awayMap
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (r : Localization.Away f)
    (x : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :
    r • x =
      (Localization.awayMap (MvPolynomial.C (σ := Fin n) : R →+* MvPolynomial (Fin n) R) f r) •
        x := by
  -- Proof comment: rewrite the source action through the normalized polynomial-away ring and
  -- then use the pointwise form of the coefficient away-map comparison.
  rw [away_polynomial_source_coeff_smul_eq (R := R) (n := n) (N := N) f r x]
  have hmap := DFunLike.congr_fun
    (away_mvPolynomial_C_algEquiv_symm_comp_C (R := R) (n := n) f) r
  rw [← hmap]
  rfl

/-- Helper for Lemma 10.118.3: the coefficient-localized polynomial action on the away-localized
source module is induced from the direct away-localization ring via
`away_mvPolynomial_C_algEquiv`. -/
lemma away_polynomial_coeff_smul_eq
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (p : MvPolynomial (Fin n) (Localization.Away f))
    (x : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :
    let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
        (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
      away_polynomial_module_over_coeff_localization (R := R) (n := n) f
    p • x =
      ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm p) • x := by
  -- Proof comment: the coefficient-localized action is exactly `Module.compHom` along the
  -- normalization ring equivalence to the direct away-localization ring.
  dsimp [away_polynomial_module_over_coeff_localization]
  rfl

/-- Helper for Lemma 10.118.3: the normalized coefficient-localized polynomial action extends the
restricted `R_f`-action on the away-localized polynomial module. -/
theorem away_polynomial_module_isScalarTower_over_coeff_localization
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N] :
    IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: both scalar actions are obtained by restriction from the same
  -- `R_f[x_1, \dots, x_n]`-module structure.
  let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  let _ : Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_base_localization (R := R) (n := n) f
  refine ⟨?_⟩
  intro r p x
  -- Proof comment: rewrite both coefficient-localized actions and the restricted `R_f`-action
  -- through the direct away-localization ring, then apply `mul_smul`.
  rw [show r • p = MvPolynomial.C (σ := Fin n) r * p by
    simpa [Algebra.smul_def]]
  rw [away_polynomial_coeff_smul_eq (R := R) (n := n) (N := N) f
    (MvPolynomial.C (σ := Fin n) r * p) x]
  rw [away_polynomial_source_coeff_smul_eq (R := R) (n := n) (N := N) f r (p • x)]
  rw [away_polynomial_coeff_smul_eq (R := R) (n := n) (N := N) f p x]
  rw [map_mul]
  exact mul_smul _ _ _

/-- Helper for Lemma 10.118.3: after transporting coefficients from `R[x_1, \dots, x_n]_f` to
the direct away-localization at `C f`, the localized polynomial presentation `π` becomes a concrete
ring map into the away-localization of `S` at `π(C f)`. -/
noncomputable abbrev localized_mvPolynomial_presentation_ringHom
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R) :
    MvPolynomial (Fin n) (Localization.Away f) →+*
      Localization.Away (π (MvPolynomial.C (σ := Fin n) f)) :=
  (Localization.awayMapₐ π (MvPolynomial.C (σ := Fin n) f)).toRingHom.comp
    (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingHom

/-- Helper for Lemma 10.118.3: the normalized localized polynomial presentation sends localized
coefficients to the matching localized coefficients in the target away-localization. -/
theorem localized_mvPolynomial_presentation_ringHom_C
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f r : R) :
    localized_mvPolynomial_presentation_ringHom (R := R) (S := S) (n := n) π f
        (MvPolynomial.C (algebraMap R (Localization.Away f) r)) =
      algebraMap S (Localization.Away (π (MvPolynomial.C (σ := Fin n) f))) (algebraMap R S r) := by
  -- Proof comment: first rewrite the coefficient through the polynomial-away equivalence, then
  -- evaluate the induced away map on the corresponding generator from `P = R[x_1, \dots, x_n]`.
  change (Localization.awayMapₐ π (MvPolynomial.C (σ := Fin n) f))
      ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
        (MvPolynomial.C (algebraMap R (Localization.Away f) r))) =
    algebraMap S (Localization.Away (π (MvPolynomial.C (σ := Fin n) f))) (algebraMap R S r)
  rw [away_mvPolynomial_C_algEquiv_symm_C (R := R) (n := n) f r]
  simp [Localization.awayMapₐ, IsLocalization.Away.map]

/-- Helper for Lemma 10.118.3: the normalized localized polynomial presentation sends each
variable to the localization of its image under the presentation map `π`. -/
theorem localized_mvPolynomial_presentation_ringHom_X
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : R) (i : Fin n) :
    localized_mvPolynomial_presentation_ringHom (R := R) (S := S) (n := n) π f
        (MvPolynomial.X i) =
      algebraMap S (Localization.Away (π (MvPolynomial.C (σ := Fin n) f))) (π (MvPolynomial.X i)) := by
  -- Proof comment: the same normalization reduces the variable case to the `awayMapₐ` computation
  -- on the direct localization generator.
  change (Localization.awayMapₐ π (MvPolynomial.C (σ := Fin n) f))
      ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm (MvPolynomial.X i)) =
    algebraMap S (Localization.Away (π (MvPolynomial.C (σ := Fin n) f))) (π (MvPolynomial.X i))
  rw [away_mvPolynomial_C_algEquiv_symm_X (R := R) (n := n) f i]
  simp [Localization.awayMapₐ, IsLocalization.Away.map]

/-- Helper for Lemma 10.118.3: localizing a ring viewed as a module over itself identifies that
localized module with the localized ring over the owner target ring. -/
noncomputable abbrev localized_self_module_linearEquiv_over_base
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[B]
      Localization.Away (algebraMap R B f) :=
  IsLocalizedModule.linearEquiv
    (.powers (algebraMap R B f))
    (LocalizedModule.mkLinearMap (.powers (algebraMap R B f)) B)
    (Algebra.linearMap B (Localization.Away (algebraMap R B f)))

/-- Helper for Lemma 10.118.3: the localized self-module comparison sends the canonical class
`b / 1` to the corresponding localized ring element. -/
@[simp] theorem localized_self_module_linearEquiv_over_base_apply_mk_one
    {B : Type*} [CommRing B] [Algebra R B] (f : R) (b : B) :
    localized_self_module_linearEquiv_over_base (R := R) (B := B) f (LocalizedModule.mk b 1) =
      algebraMap B (Localization.Away (algebraMap R B f)) b := by
  -- Proof comment: evaluate the universal-property comparison on the canonical numerator `b / 1`.
  simpa [localized_self_module_linearEquiv_over_base] using
    (IsLocalizedModule.linearEquiv_apply
      (.powers (algebraMap R B f))
      (LocalizedModule.mkLinearMap (.powers (algebraMap R B f)) B)
      (Algebra.linearMap B (Localization.Away (algebraMap R B f)))
      b)

/-- Helper for Lemma 10.118.3: the localized self-module comparison remains linear after
restricting scalars from the localized target ring to `R_f`. -/
noncomputable abbrev localized_self_module_linearEquiv
    {B : Type*} [CommRing B] [Algebra R B] (f : R) :
    LocalizedModule.Away (algebraMap R B f) B ≃ₗ[Localization.Away f]
      Localization.Away (algebraMap R B f) :=
  LinearEquiv.restrictScalars (Localization.Away f)
    (LinearEquiv.extendScalarsOfIsLocalization
      (.powers (algebraMap R B f))
      (Localization.Away (algebraMap R B f))
      (localized_self_module_linearEquiv_over_base (R := R) (B := B) f))

/-- Helper for Lemma 10.118.3: the restricted-scalars self-module comparison has the same
underlying function as the owner-side comparison. -/
@[simp] theorem localized_self_module_linearEquiv_apply
    {B : Type*} [CommRing B] [Algebra R B] (f : R)
    (x : LocalizedModule.Away (algebraMap R B f) B) :
    localized_self_module_linearEquiv (R := R) (B := B) f x =
      localized_self_module_linearEquiv_over_base (R := R) (B := B) f x := by
  -- Proof comment: restricting scalars changes only the linearity witness, not the function.
  rfl

/-- Helper for Lemma 10.118.3: the restricted-scalars self-module comparison still sends `b / 1`
to the corresponding localized ring element. -/
@[simp] theorem localized_self_module_linearEquiv_apply_mk_one
    {B : Type*} [CommRing B] [Algebra R B] (f : R) (b : B) :
    localized_self_module_linearEquiv (R := R) (B := B) f (LocalizedModule.mk b 1) =
      algebraMap B (Localization.Away (algebraMap R B f)) b := by
  -- Proof comment: this is the owner-side computation transported through scalar restriction.
  simpa [localized_self_module_linearEquiv] using
    localized_self_module_linearEquiv_over_base_apply_mk_one (R := R) (B := B) f b

/-- Helper for Lemma 10.118.3: after restricting scalars along `R → R_f`, the localized target
module sits in the expected scalar tower `R → R_f → N_f`. -/
theorem localized_away_moduleTarget_isScalarTower_over_base
    {B : Type*} [CommRing B] [Algebra R B]
    {N : Type*} [AddCommGroup N] [Module B N] (f : R) :
    let _ : Module R (LocalizedModule.Away (algebraMap R B f) N) :=
      Module.compHom (LocalizedModule.Away (algebraMap R B f) N)
        (algebraMap R (Localization.Away f))
    IsScalarTower R (Localization.Away f)
      (LocalizedModule.Away (algebraMap R B f) N) := by
  let _ : Module R (LocalizedModule.Away (algebraMap R B f) N) :=
    Module.compHom (LocalizedModule.Away (algebraMap R B f) N)
      (algebraMap R (Localization.Away f))
  -- Proof comment: both scalar actions factor through `R_f`, so the tower condition is just
  -- `mul_smul` after unfolding the restricted `R`-action.
  refine ⟨?_⟩
  intro r s x
  simpa [Module.compHom, Algebra.smul_def] using
    (mul_smul (algebraMap R (Localization.Away f) r) s x)

/-- Helper for Lemma 10.118.3: a surjective polynomial presentation makes `S` finite over the
polynomial ring when scalars are restricted along the presentation map. -/
lemma mvPolynomial_module_finite_of_surjective_presentation
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π) :
    let P := MvPolynomial (Fin n) R
    letI : Algebra P S := π.toRingHom.toAlgebra
    Module.Finite P S := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toRingHom.toAlgebra
  -- The polynomial generators of `S` are exactly the images of the free rank-one generator.
  exact Module.Finite.of_surjective (Algebra.linearMap P S) <| by
    simpa using hπ

/-- Helper for Lemma 10.118.3: after restricting scalars along a surjective polynomial
presentation, every finite `S`-module is finite over the polynomial ring as well. -/
lemma mvPolynomial_module_finite_of_surjective_presentation_on_module
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    {N : Type*} [AddCommGroup N] [Module S N] [Module.Finite S N] :
    let P := MvPolynomial (Fin n) R
    letI : Algebra P S := π.toRingHom.toAlgebra
    letI : Module P N := Module.compHom N π.toRingHom
    Module.Finite P N := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toRingHom.toAlgebra
  letI : Module P N := Module.compHom N π.toRingHom
  letI : IsScalarTower P S N := IsScalarTower.of_compHom P S N
  -- Finiteness descends along restriction of scalars through the finite polynomial presentation.
  let _ : Module.Finite P S :=
    mvPolynomial_module_finite_of_surjective_presentation (R := R) (S := S) π hπ
  exact Module.Finite.trans S N

/-- Helper for Lemma 10.118.3: if `f ≠ 0`, then every power of `C f` already belongs to the
generic-fiber denominator submonoid coming from the non-zero-divisors of `R`. -/
lemma powers_C_le_polynomial_generic_denominators
    {n : ℕ} {f : R} (hf : f ≠ 0) :
    Submonoid.powers (MvPolynomial.C (σ := Fin n) f) ≤
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R) := by
  intro z hz
  rw [Submonoid.mem_powers_iff] at hz
  rcases hz with ⟨m, rfl⟩
  -- Proof comment: `C` commutes with powers, and `f^m` is regular because `f` is regular in the
  -- domain `R`.
  have hm : f ^ m ∈ nonZeroDivisors R := by
    exact
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf) <| by
        rw [Submonoid.mem_powers_iff]
        exact ⟨m, rfl⟩
  simpa [Algebra.algebraMapSubmonoid]
    using Set.mem_image_of_mem (algebraMap R (MvPolynomial (Fin n) R)) hm

/-- Helper for Lemma 10.118.3: adjoining the powers of `C f` does not enlarge the generic-fiber
denominator submonoid of `R[x_1, \dots, x_n]`. -/
lemma polynomial_generic_denominators_sup_eq
    {n : ℕ} {f : R} (hf : f ≠ 0) :
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R) ⊔
        Submonoid.powers (MvPolynomial.C (σ := Fin n) f) =
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R) := by
  -- Proof comment: the powers of `C f` already lie in the generic-fiber denominator submonoid,
  -- so the supremum collapses to the larger submonoid.
  exact sup_eq_left.mpr <|
    powers_C_le_polynomial_generic_denominators (R := R) (n := n) hf

/-- Helper for Lemma 10.118.3: reindexing a localized module along an equality of denominator
submonoids fixes the canonical localization map. -/
noncomputable abbrev localizedModule_reindexLinearEquiv
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {S S' : Submonoid A} (h : S = S') :
    LocalizedModule S N ≃ₗ[A] LocalizedModule S' N :=
  h.rec (LinearEquiv.refl A (LocalizedModule S N))

/-- Helper for Lemma 10.118.3: the reindexing equivalence along an equality of denominator
submonoids sends each canonical numerator to itself. -/
lemma localizedModule_reindexLinearEquiv_apply_mk
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {S S' : Submonoid A} (h : S = S') (x : N) :
    localizedModule_reindexLinearEquiv (A := A) (N := N) h
      (LocalizedModule.mkLinearMap S N x) =
        LocalizedModule.mkLinearMap S' N x := by
  -- Proof comment: after substituting the denominator equality, the reindexing equivalence is
  -- definitionally the identity.
  subst h
  rfl

/-- Helper for Lemma 10.118.3: the canonical iterated-localization equivalence sends a double
numerator to the corresponding direct numerator. -/
lemma iterated_localization_linearEquiv_apply_mk_mk
    {A : Type*} [CommRing A]
    {S S' : Submonoid A}
    {N : Type*} [AddCommGroup N] [Module A N]
    (x : N) :
    IsLocalizedModule.linearEquiv (S ⊔ S')
      (iteratedLocalizedModuleMkLinearMap S S' N)
      (LocalizedModule.mkLinearMap (S ⊔ S') N)
      (LocalizedModule.mkLinearMap S (LocalizedModule S' N)
        (LocalizedModule.mkLinearMap S' N x)) =
      LocalizedModule.mkLinearMap (S ⊔ S') N x := by
  -- Proof comment: evaluate the universal-property comparison on the canonical double numerator.
  simpa [iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
    (IsLocalizedModule.linearEquiv_apply
      (S := S ⊔ S')
      (f := iteratedLocalizedModuleMkLinearMap S S' N)
      (g := LocalizedModule.mkLinearMap (S ⊔ S') N)
      x)

/-- Helper for Lemma 10.118.3: after collapsing the denominator supremum, the direct localization
at the generic-fiber submonoid sends the canonical double numerator to the expected direct
numerator. -/
lemma polynomial_iterated_generic_fiber_linearEquiv_apply_mk_mk
    {n : ℕ} {f : R} (hf : f ≠ 0)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (x : N) :
    let P := MvPolynomial (Fin n) R
    let T := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
    let U := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
    localizedModule_reindexLinearEquiv
        (A := P)
        (N := N)
        (polynomial_generic_denominators_sup_eq (R := R) (n := n) hf)
        (IsLocalizedModule.linearEquiv
          (T ⊔ U)
          (iteratedLocalizedModuleMkLinearMap T U N)
          (LocalizedModule.mkLinearMap (T ⊔ U) N)
          (LocalizedModule.mkLinearMap T (LocalizedModule U N)
            (LocalizedModule.mkLinearMap U N x))) =
      LocalizedModule.mkLinearMap T N x := by
  dsimp
  -- Route correction: normalize the denominator supremum before comparing any transported maps.
  have hiter :
      IsLocalizedModule.linearEquiv
          ((Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) ⊔
            Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
          (iteratedLocalizedModuleMkLinearMap
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))
            (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) N)
          (LocalizedModule.mkLinearMap
            ((Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) ⊔
              Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
            N)
          (LocalizedModule.mk (LocalizedModule.mk x 1) 1) =
        LocalizedModule.mk x 1 := by
    simpa [LocalizedModule.mkLinearMap_apply] using
      iterated_localization_linearEquiv_apply_mk_mk
        (A := MvPolynomial (Fin n) R)
        (S := Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))
        (S' := Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
        (N := N)
        (x := x)
  rw [hiter]
  exact localizedModule_reindexLinearEquiv_apply_mk
    (A := MvPolynomial (Fin n) R)
    (N := N)
    (S := (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) ⊔
      Submonoid.powers (MvPolynomial.C (σ := Fin n) f))
    (S' := Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))
    (polynomial_generic_denominators_sup_eq (R := R) (n := n) hf)
    x


end
