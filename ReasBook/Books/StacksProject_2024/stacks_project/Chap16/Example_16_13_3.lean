import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_11
import StacksProject_2024.stacks_project.Chap15.Definition_15_50_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_50_14
import StacksProject_2024.stacks_project.Chap16.Theorem_16_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsGRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R

/- Domain-style sampling:
 primary domain: henselization/completion comparison for a Noetherian local `G`-ring domain, and
  algebraic elements of the maximal-ideal completion over the base domain `R`;
- sampled owner declarations in this domain:
  `IsGRing`,
  `IsHenselizationOf`,
  `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`,
  `AlgHom.range`,
  `Subalgebra.algebraicClosure`;
- best owner abstraction: the source-facing theorem should talk about the image of the chosen
  henselization inside `Rhat` under its canonical `R`-algebra map to the completion and the
  canonical subalgebra `Subalgebra.algebraicClosure R Rhat`;
- primitive data: the local domain `R`, its `G`-ring owner, the chosen henselization `Rh`, and
  the completion comparison owner data identifying `Rhat` with `Rhhat`;
- derived API: the transported bridge `Rh →ₐ[R] Rhat` and the pointwise membership
  characterization
  obtained from the main theorem by `Subalgebra.mem_algebraicClosure`.

Source/core/bridge triage:
- `source-facing`: the subalgebra equality identifying the image with
  `Subalgebra.algebraicClosure R Rhat`;
- `core/canonical`: `IsGRing`, `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`, `AlgHom.range`, and `Subalgebra.algebraicClosure`;
- `bridge/view`: the thin transported map `henselizationToCompletion` and the pointwise
  algebraicity reformulation. -/

/-- Helper for Example 16.13.3: the maximal-ideal residue field of a local ring is canonically
the usual residue field. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Example 16.13.3: the maximal-ideal residue-field comparison commutes with local
ring maps. -/
private theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv A).toRingHom := by
  -- Proof comment: both composites send the class of `a : A` to the residue class of `f a`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv A
          (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap]
  rw [show maximalIdealResidueFieldEquiv A
      (algebraMap A (maximalIdeal A).ResidueField a) = residue A a by
        change
          maximalIdealResidueFieldEquiv A
              ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
            residue A a
        exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)]
  rw [show algebraMap B (maximalIdeal B).ResidueField (f a) =
      algebraMap (ResidueField B) (maximalIdeal B).ResidueField (residue B (f a)) by rfl]
  rw [show maximalIdealResidueFieldEquiv B
      (algebraMap (ResidueField B) (maximalIdeal B).ResidueField (residue B (f a))) =
      residue B (f a) by
        change
          maximalIdealResidueFieldEquiv B
              ((maximalIdealResidueFieldEquiv B).symm (residue B (f a))) =
            residue B (f a)
        exact (maximalIdealResidueFieldEquiv B).apply_symm_apply (residue B (f a))]
  exact IsLocalRing.ResidueField.map_residue f a

/-- Helper for Example 16.13.3: the completion residue field is canonically identified with the
residue field of the base local ring. -/
private noncomputable abbrev completionResidueFieldEquiv :
    ResidueField R ≃+* ResidueField Rhat :=
  RingEquiv.ofBijective
    (ResidueField.map (algebraMap R Rhat))
    (maximalIdealCompletion_residueField_bijective R)

/-- Helper for Example 16.13.3: the closed point of the chosen henselization and the closed point
of the completion contract to the same prime of `R`. -/
private theorem henselizationCompletion_under_eq :
    (maximalIdeal Rh).under R = (maximalIdeal Rhat).under R := by
  -- Proof comment: both contractions are the maximal ideal of the base local ring.
  calc
    (maximalIdeal Rh).under R = maximalIdeal R := by
      simpa [Ideal.under_def] using
        (IsLocalRing.maximalIdeal_comap (algebraMap R Rh))
    _ = (maximalIdeal Rhat).under R := by
      symm
      simpa [Ideal.under_def] using
        (IsLocalRing.maximalIdeal_comap (algebraMap R Rhat))

/-- Helper for Example 16.13.3: the residue-field map needed for the universal property of the
henselization targets the completion residue field. -/
private noncomputable abbrev henselizationCompletionResidueFieldMap :
    (maximalIdeal Rh).ResidueField →+* (maximalIdeal Rhat).ResidueField :=
  (maximalIdealResidueFieldEquiv Rhat).symm.toRingHom.comp <|
    completionResidueFieldEquiv.toRingHom.comp <|
      (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom.comp
        (maximalIdealResidueFieldEquiv Rh).toRingHom

/-- Helper for Example 16.13.3: the chosen residue-field map is compatible with the common closed
point of `R`. -/
private theorem henselizationCompletionResidueFieldMap_commutes :
    henselizationCompletionResidueFieldMap (R := R) (Rh := Rh).comp
        (Ideal.ResidueField.map
          ((maximalIdeal Rh).under R) (maximalIdeal Rh) (algebraMap R Rh) rfl) =
      Ideal.ResidueField.map
        ((maximalIdeal Rh).under R) (maximalIdeal Rhat) (algebraMap R Rhat)
        (henselizationCompletion_under_eq (R := R) (Rh := Rh)) := by
  -- Proof comment: compare both residue-field maps on classes of elements of `R`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp [henselizationCompletionResidueFieldMap, RingHom.comp_assoc]
  have hres :
      (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm
        (residue Rh ((algebraMap R Rh) a)) = residue R a := by
    -- Proof comment: the henselization residue-field equivalence is induced by `R → Rh`.
    apply (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).injective
    simpa using (IsLocalRing.ResidueField.map_residue (algebraMap R Rh) a)
  rw [show maximalIdealResidueFieldEquiv Rh
      ((algebraMap Rh (maximalIdeal Rh).ResidueField) ((algebraMap R Rh) a)) =
        residue Rh ((algebraMap R Rh) a) by
        change
          maximalIdealResidueFieldEquiv Rh
              ((maximalIdealResidueFieldEquiv Rh).symm (residue Rh ((algebraMap R Rh) a))) =
            residue Rh ((algebraMap R Rh) a)
        exact
          (maximalIdealResidueFieldEquiv Rh).apply_symm_apply
            (residue Rh ((algebraMap R Rh) a))]
  rw [hres]
  rw [IsLocalRing.ResidueField.map_residue]
  -- Proof comment: after rewriting both sides in the ordinary residue fields, the target is
  -- definitionally the same map back into the ideal residue field of the completion.
  change
    (maximalIdealResidueFieldEquiv Rhat).symm (residue Rhat ((algebraMap R Rhat) a)) =
      (maximalIdealResidueFieldEquiv Rhat).symm (residue Rhat ((algebraMap R Rhat) a))
  rfl

/-- Helper for Example 16.13.3: the maximal-ideal completion is complete for its closed-point
ideal. -/
private theorem completion_isAdicComplete_maximal :
    IsAdicComplete (maximalIdeal Rhat) Rhat := by
  have hcomplete :
      IsAdicComplete (Ideal.map (algebraMap R Rhat) (maximalIdeal R)) Rhat := by
    exact
      (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) Rhat).2
        (AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing (maximalIdeal R)))
  rw [← completion_map_maximalIdeal_eq_maximalIdeal (R := R)]
  exact hcomplete

/-- Helper for Example 16.13.3: the maximal-ideal completion of a Noetherian local ring is
henselian local. -/
private instance henselianLocalRing_completion : HenselianLocalRing Rhat := by
  let _ : IsAdicComplete (maximalIdeal Rhat) Rhat :=
    completion_isAdicComplete_maximal (R := R)
  let _ : HenselianRing Rhat (maximalIdeal Rhat) :=
    IsAdicComplete.henselianRing (R := Rhat) (I := maximalIdeal Rhat)
  refine HenselianLocalRing.mk ?_
  intro f hmonic a₀ ha hunit
  exact
    HenselianRing.is_henselian f hmonic a₀ ha
      (hunit.map (Ideal.Quotient.mk (maximalIdeal Rhat)))

/-- The canonical map from the chosen henselization `Rh` to the completion `Rhat`, obtained from
the henselization universal property with henselian target `Rhat`. -/
noncomputable abbrev henselizationToCompletion : Rh →ₐ[R] Rhat :=
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
        (R := R) (A := Rh) (S := Rhat)
        IsHenselizationOf.isFilteredColimitOfEtale
        (maximalIdeal Rh)
        (henselizationCompletion_under_eq (R := R) (Rh := Rh))
        (henselizationCompletionResidueFieldMap (R := R) (Rh := Rh))
        (henselizationCompletionResidueFieldMap_commutes (R := R) (Rh := Rh))

/-- Helper for Example 16.13.3: the canonical comparison map from `Rh` to `Rhat` still agrees
with the base completion map on the image of `R`. -/
private theorem henselizationToCompletion_comp_algebraMap :
    (henselizationToCompletion : Rh →ₐ[R] Rhat).toRingHom.comp (algebraMap R Rh) =
      algebraMap R Rhat := by
  -- Proof comment: every `R`-algebra homomorphism out of `Rh` restricts to the base completion
  -- map on `R`.
  exact RingHom.ext fun x ↦
    (henselizationToCompletion : Rh →ₐ[R] Rhat).commutes x

/-- Helper for Example 16.13.3: the residue field at the zero prime is a fraction-ring model of
`R`. -/
private theorem zeroPrimeResidueField_isFractionRing :
    IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
  intro x
  change algebraMap R ((⊥ : Ideal R).ResidueField) x =
    algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
  symm
  exact show
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
          (Ideal.Quotient.mk (⊥ : Ideal R) x) =
        algebraMap R ((⊥ : Ideal R).ResidueField) x by
    rfl

/-- Helper for Example 16.13.3: the natural map from the henselization into the zero fiber is
injective. -/
private theorem zeroPrimeFiber_includeRight_injective :
    Function.Injective
      (Algebra.TensorProduct.includeRight : Rh →ₐ[R] ((⊥ : Ideal R).Fiber Rh)) := by
  let _ : Module.Flat R Rh := henselizationMap_faithfullyFlat.flat
  -- Proof comment: the zero-prime residue field is a fraction-ring model of `R`, so tensoring
  -- along it preserves injectivity on the flat henselization side.
  exact
    Algebra.TensorProduct.includeRight_injective
      (R := R) (A := ((⊥ : Ideal R).ResidueField)) (B := Rh)
      (IsFractionRing.injective R ((⊥ : Ideal R).ResidueField))

/-- Helper for Example 16.13.3: an element of the completion that lies in every power of the
maximal ideal must vanish. -/
private theorem sub_eq_zero_of_mem_maximalIdeal_pow_all
    {a b : Rhat}
    (hpow : ∀ N : ℕ, a - b ∈ maximalIdeal Rhat ^ N) :
    a = b := by
  have hiInf_bot : (⨅ n : ℕ, maximalIdeal Rhat ^ n) = (⊥ : Ideal Rhat) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rhat)
      (maximalIdeal.isMaximal Rhat).ne_top
  have hsub_mem : a - b ∈ ⨅ n : ℕ, maximalIdeal Rhat ^ n := by
    -- Proof comment: membership in the infimum is exactly the same as membership in every power.
    simpa [Ideal.mem_iInf] using hpow
  have hsub_zero : a - b = 0 := by
    rw [hiInf_bot] at hsub_mem
    simpa using hsub_mem
  exact sub_eq_zero.mp hsub_zero

/-- Helper for Example 16.13.3: a finite product of algebraic algebras is algebraic. -/
private theorem isAlgebraic_pi_of_finite
    {K : Type u} [CommRing K] {ι : Type u} [Finite ι]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (hA : ∀ i, Algebra.IsAlgebraic K (A i)) :
    Algebra.IsAlgebraic K ((i : ι) → A i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  rw [Algebra.isAlgebraic_iff_isIntegral]
  intro x
  have hx : ∀ i, IsIntegral K (x i) := by
    intro i
    exact (Algebra.isAlgebraic_iff_isIntegral.mp (hA i)) (x i)
  choose p hpMonic hpRoot using hx
  let q : Polynomial K := ∏ i, p i
  refine ⟨q, ?_, ?_⟩
  · -- Proof comment: the product of monic annihilating polynomials is still monic.
    simpa [q] using Polynomial.monic_prod_of_monic fun i _ ↦ hpMonic i
  · -- Proof comment: evaluation in the product ring is coordinatewise, so the `i`-th factor
    -- of `q` annihilates the `i`-th coordinate of `x`.
    ext i
    have hfactor : Polynomial.aeval (x i) (p i) = 0 := hpRoot i
    simp [q, Polynomial.aeval_def, hpRoot, hfactor]

/-- Helper for Example 16.13.3: the zero fiber of the henselization is canonically the finite
product of the residue fields of the finitely many primes over `(0)`. -/
private noncomputable abbrev zeroPrimeFiberToPiResidueFieldEquiv :
    ((⊥ : Ideal R).Fiber Rh) ≃ₐ[((⊥ : Ideal R).ResidueField)]
      ((q : (show Finite ((show PrimeSpectrum R from ⟨⊥, Ideal.isPrime_bot⟩).asIdeal.primesOver Rh) from
          henselization_primesOver_finite (R := R) (Rh := Rh) ⟨⊥, Ideal.isPrime_bot⟩)).fintype) →
        q.1.ResidueField) := by
  classical
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  letI : Finite (p0.asIdeal.primesOver Rh) :=
    henselization_primesOver_finite (R := R) (Rh := Rh) p0
  letI : Fintype (p0.asIdeal.primesOver Rh) := Fintype.ofFinite (p0.asIdeal.primesOver Rh)
  -- Proof comment: Lemma `15.45.13` already identifies the zero fiber with the product of the
  -- residue fields lying over the chosen prime.
  exact
    AlgEquiv.ofBijective
      (p0.asIdeal.fiberToPiResidueField Rh)
      (fiberToPiResidueField_henselization_bijective (R := R) (Rh := Rh) p0)

/-- Helper for Example 16.13.3: the zero fiber of the henselization is algebraic over the zero
prime residue field. -/
private theorem zeroPrimeFiber_isAlgebraic_overZeroResidueField :
    Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField) (((⊥ : Ideal R).Fiber Rh)) := by
  classical
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  letI : Finite (p0.asIdeal.primesOver Rh) :=
    henselization_primesOver_finite (R := R) (Rh := Rh) p0
  letI : Fintype (p0.asIdeal.primesOver Rh) := Fintype.ofFinite (p0.asIdeal.primesOver Rh)
  let e := zeroPrimeFiberToPiResidueFieldEquiv (R := R) (Rh := Rh)
  letI :
      Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField)
        ((q : p0.asIdeal.primesOver Rh) → q.1.ResidueField) :=
    isAlgebraic_pi_of_finite (K := ((⊥ : Ideal R).ResidueField)) fun q ↦
      (henselization_residueField_isAlgebraic_and_separable
        (R := R) (Rh := Rh) p0 q).1
  -- Proof comment: transport algebraicity back across the canonical zero-fiber decomposition.
  exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective

-- Proof sketch: the `G`-ring hypothesis makes the completion map `R → Rhat` regular. Apply
-- Theorem `16.13.2` to one-variable polynomial relations over `R` to
-- approximate algebraic elements of `Rhat` by roots in étale neighborhoods of `R`; the universal
-- property of the chosen henselization funnels those approximations through `Rh`. The canonical
-- bijection from `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`
-- identifies the completion of `Rh` with `Rhat`, and the Stacks finiteness argument for roots
-- over the generic fiber forces the approximants to stabilize to an actual element of `Rh`. This
-- characterizes exactly the elements of `Rhat` algebraic over `R`.

/-- Example 16.13.3: let `R` be a Noetherian local domain that is a `G`-ring, let `Rh` be a chosen
henselization of `R`, and let `Rhat` be the maximal-ideal adic completion of `R`. Then the image
of the canonical map `henselizationToCompletion : Rh →ₐ[R] Rhat` is exactly the subalgebra of
`Rhat` consisting of elements algebraic over `R`, i.e. the canonical subalgebra
`Subalgebra.algebraicClosure R Rhat`. -/
-- Route correction: the intended zero-prime generic-fiber route still depends on
-- `Chap15.Lemma_15_45_13`, but that owner currently does not elaborate in this checkout because
-- its dependency closure through `Chap15.Lemma_15_45_12` and `Chap15.Lemma_15_45_3` fails before
-- this file is reached. The reverse inclusion remains the Artin-approximation step from
-- Theorem `16.13.2`, together with the finiteness/stabilization argument for roots in the
-- henselization.
theorem henselization_range_eq_algebraicClosure :
    (henselizationToCompletion : Rh →ₐ[R] Rhat).range =
      Subalgebra.algebraicClosure R Rhat := by
  -- Proof comment: the proof is the expected two-sided containment. The forward direction is the
  -- generic-fiber algebraicity argument for henselization elements, and the reverse direction is
  -- Artin approximation plus uniqueness in the henselian completion.
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    rw [Subalgebra.mem_algebraicClosure]
    -- TODO: the clean forward route is to import `Chap15.Lemma_15_45_13`, prove that the zero
    -- generic fiber `((⊥ : Ideal R).Fiber Rh)` is algebraic over `Frac(R)`, pull that back along
    -- the injective `includeRight : Rh → ((⊥).Fiber Rh)`, and then descend from `Frac(R)` to `R`
    -- via `IsFractionRing.comap_isAlgebraic_iff`. In this checkout that owner import is blocked
    -- structurally: rebuilding `Chap15.Lemma_15_45_13` fails upstream in
    -- `Chap15.Lemma_15_45_3` and `Chap15.Lemma_15_45_12` before this file can use the public
    -- theorems.
    sorry
  · intro f hf
    rw [Subalgebra.mem_algebraicClosure] at hf
    -- Proof comment: the `G`-ring hypothesis should supply the regularity bridge needed to apply
    -- Theorem `16.13.2` to an algebraic polynomial witness for `f`. The remaining work is to
    -- package the simple-root approximation in an étale neighborhood and descend it to `Rh` via
    -- the henselization universal property.
    -- TODO: choose a polynomial witness for `hf`, run Theorem `16.13.2` for all `N`, transport
    -- the resulting étale roots into `Rh`, and then use finiteness of the henselization root set
    -- together with separatedness of the completion to force eventual equality with `f`.
    sorry

/-- An element of `Rhat` lies in the image of the canonical henselization map exactly when it is
algebraic over `R`. -/
theorem mem_range_henselizationToCompletion_iff_isAlgebraic (f : Rhat) :
    f ∈ (henselizationToCompletion : Rh →ₐ[R] Rhat).range ↔ IsAlgebraic R f := by
  rw [henselization_range_eq_algebraicClosure]
  rw [Subalgebra.mem_algebraicClosure]

end
