import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_126_4
import stacks_proof.stacks_project.Chap10.Definition_10_110_7
import stacks_proof.stacks_project.Chap15.Definition_15_22_1
import stacks_proof.stacks_project.Chap15.Lemma_15_22_10
import stacks_proof.stacks_project.Chap15.Lemma_15_25_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {R : Type u} {A : Type v} [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing A] [Algebra R A] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
variable [Module.Flat R A] [Algebra.EssFiniteType R A]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) A
local notation "GenericFiber" => Ideal.Fiber (⊥ : Ideal R) A

/- Domain-style sampling:
- primary domain: Picard groups of fibers of local flat algebras over valuation rings, with the
  closed and generic fibers carried by the canonical owner `Ideal.Fiber`;
- sampled owner declarations:
  `Ideal.Fiber`,
  `CommRing.Pic`,
  `subsingleton_picardGroup_of_uniqueFactorizationMonoid`,
  `IsRegularRing`,
  `flat_iff_isTorsionFree_of_valuationRing`;
- best owner abstraction: the closed fiber should be written as
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) A` and the generic fiber as
  `GenericFiber = Ideal.Fiber (⊥ : Ideal R) A`; the tensor-product models
  `A ⊗[R] ResidueField R` and `A ⊗[R] FractionRing R` are bridge presentations of those owners;
- primitive vs. derived:
  the primitive data are the valuation-ring map `R → A`, locality of `A`, flatness, essential
  finite type, and regularity of the canonical closed fiber `ClosedFiber`;
  the Picard-triviality conclusion belongs on the owner `CommRing.Pic GenericFiber`, while any
  tensor-model reformulation is derived bridge/view API rather than the core owner statement.

Source/core/bridge triage:
- `source-facing`: the theorem below asserting Picard triviality of the generic fiber;
- `core/canonical`: the fiber-ring owner `Ideal.Fiber` together with `CommRing.Pic`;
- `bridge/view`: the textbook tensor-product presentations of the closed and generic fibers.
-/

-- Proof sketch: let `L` represent a class in `CommRing.Pic GenericFiber`, using the tensor-model
-- presentation `GenericFiber = A ⊗[R] FractionRing R`. Use the extension result for finite modules
-- over the generic fiber to choose a finite `A`-module whose base change to `GenericFiber`
-- is `L`. Over a valuation ring, torsion-free implies flat, so the cited finite-presentation and
-- perfectness lemmas give a finite free resolution of this model over `A`. After base change to
-- `GenericFiber`, Lemma `15.120.1` makes the class of `L` an integral multiple of the
-- free rank-one class in `K₀`, and Lemma `15.119.7` then forces `L` to be free of rank one.
-- Hence every element of the Picard group is trivial.
omit [ValuationRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
  [Algebra.EssFiniteType R A] in
/-- Helper for Lemma 15.122.3: if every Picard class on the generic fiber is equal to the unit
class, then the Picard group is trivial. -/
private theorem subsingleton_picardGroup_genericFiber_of_repr_trivial
    (htriv : ∀ x : CommRing.Pic GenericFiber, x = 1) :
    Subsingleton (CommRing.Pic GenericFiber) := by
  -- A multiplicative group is a subsingleton as soon as every element agrees with the unit.
  refine ⟨?_⟩
  intro x y
  rw [htriv x, htriv y]

omit [ValuationRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
  [Algebra.EssFiniteType R A] in
/-- Helper for Lemma 15.122.3: a Picard class on the generic fiber is trivial once its canonical
invertible representative is free of rank one. -/
private theorem picard_repr_eq_one_of_free
    (x : CommRing.Pic GenericFiber) [Module.Free GenericFiber x] :
    x = 1 := by
  -- Rewrite `x` as the class of its representative module and apply the Picard free-module
  -- criterion.
  rw [← CommRing.Pic.mk_eq_self (R := GenericFiber) (M := x)]
  exact CommRing.Pic.mk_eq_one (R := GenericFiber) (M := x)

omit [ValuationRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
  [Algebra.EssFiniteType R A] in
/-- Helper for Lemma 15.122.3: to trivialize the Picard group of the generic fiber, it is enough
to prove that every Picard representative over the generic fiber is free. -/
private theorem subsingleton_picardGroup_genericFiber_of_repr_free
    (hfree : ∀ x : CommRing.Pic GenericFiber, Module.Free GenericFiber x) :
    Subsingleton (CommRing.Pic GenericFiber) := by
  -- Convert the group-level statement to the source-facing freeness statement for each class.
  refine subsingleton_picardGroup_genericFiber_of_repr_trivial (R := R) (A := A) ?_
  intro x
  let _ : Module.Free GenericFiber x := hfree x
  exact picard_repr_eq_one_of_free (R := R) (A := A) x

/-- Helper for Lemma 15.122.3: the residue field at the zero prime of a domain is its fraction
field. -/
private theorem exists_zeroPrimeResidueField_algEquiv_fractionRing :
    Nonempty (FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField)) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    -- Compare `R` with `R / (0)` and reuse the canonical fraction-ring owner on the residue field.
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
  -- Once the bottom residue field is recognized as a fraction ring of `R`, the standard
  -- fraction-field equivalence finishes the identification.
  exact ⟨FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)⟩

/-- Helper for Lemma 15.122.3: choose the zero-prime residue-field/fraction-ring equivalence. -/
private noncomputable abbrev zeroPrimeResidueField_algEquiv_fractionRing :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
  Classical.choice (exists_zeroPrimeResidueField_algEquiv_fractionRing (R := R))

/-- Helper for Lemma 15.122.3: the canonical generic fiber is the localization of `A` away from
the image of the nonzero elements of `R`. -/
private theorem exists_genericFiber_ringEquiv_localization :
    Nonempty
      (GenericFiber ≃+* Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) := by
  let eFrac : ((⊥ : Ideal R).ResidueField) ≃ₐ[R] Localization (nonZeroDivisors R) :=
    (zeroPrimeResidueField_algEquiv_fractionRing (R := R)).symm.trans
      (FractionRing.algEquiv R (Localization (nonZeroDivisors R)))
  -- First rewrite the left tensor factor from the generic residue field to the fraction-field
  -- localization of `R`, then apply the standard tensor/localization comparison.
  exact
    ⟨(Algebra.TensorProduct.congr eFrac (AlgEquiv.refl : A ≃ₐ[R] A)).toRingEquiv.trans
      (Localization.tensorRightAlgEquiv (nonZeroDivisors R) A).toRingEquiv⟩

/-- Helper for Lemma 15.122.3: choose the canonical generic-fiber/localization equivalence. -/
private noncomputable abbrev genericFiber_ringEquiv_localization :
    GenericFiber ≃+* Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) :=
  Classical.choice (exists_genericFiber_ringEquiv_localization (R := R) (A := A))

/-- Helper for Lemma 15.122.3: after restricting scalars from the generic-fiber localization back
to `A`, the identity map is already a localization map. -/
private theorem localized_restrictScalars_id_isLocalizedModule_over_base
    (N : ModuleCat (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))) :
    let _ : Module A N := Module.compHom N (algebraMap A
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))
    let _ : IsScalarTower A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N :=
      RestrictScalars.isScalarTower A
        (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N
    IsLocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      (LinearMap.id : N →ₗ[A] N) := by
  let _ : Module A N := Module.compHom N (algebraMap A
    (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))
  let _ : IsScalarTower A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N :=
    RestrictScalars.isScalarTower A
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N
  -- Proof comment: the target already lives over the localization ring, so the identity map
  -- satisfies the universal localization property over `A`.
  simpa using
    (isLocalizedModule_id
      (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      N
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))

/-- Helper for Lemma 15.122.3: localizing the `A`-module obtained by restricting scalars from the
generic-fiber localization recovers the original localization module over the generic fiber. -/
private noncomputable def localized_restrictScalars_linearEquiv_over_base
    (N : ModuleCat (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))) :
    LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      (((ModuleCat.restrictScalars
          (algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))).obj
          N)) ≃ₗ[Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))] N :=
  let _ : Module A N := Module.compHom N (algebraMap A
    (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))
  let _ : IsScalarTower A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N :=
    RestrictScalars.isScalarTower A
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) N
  let g :
      (((ModuleCat.restrictScalars
          (algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))).obj
          N)) →ₗ[A] N :=
    LinearMap.id
  letI :
      IsLocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) g :=
    localized_restrictScalars_id_isLocalizedModule_over_base (R := R) (A := A) N
  -- Proof comment: first build the universal comparison over `A`, then extend scalars to the
  -- localization ring appearing in the source proof.
  LinearEquiv.extendScalarsOfIsLocalization
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
    (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
    (IsLocalizedModule.linearEquiv
      (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
        (((ModuleCat.restrictScalars
          (algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))))).obj
          N)))
      g)

/-- Helper for Lemma 15.122.3: transport a Picard representative on the generic fiber to the
canonical localization owner used by the source proof. -/
private noncomputable instance genericFiber_picard_localizationModule_module
    (x : CommRing.Pic GenericFiber) :
    Module (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) x :=
  Module.compHom x
    (genericFiber_ringEquiv_localization (R := R) (A := A)).symm.toRingHom

/-- Helper for Lemma 15.122.3: package the transported Picard representative as a module over the
canonical localization owner used by the source proof. -/
private noncomputable abbrev genericFiber_picard_localizationModule
    (x : CommRing.Pic GenericFiber) :
    ModuleCat (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) :=
  ModuleCat.of (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) x

/-- Helper for Lemma 15.122.3: the transported Picard representative on the generic fiber descends
to a finitely presented `A`-module after restricting scalars from the canonical localization. -/
private theorem genericFiber_picard_repr_has_finitePresentation_model
    (x : CommRing.Pic GenericFiber) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module A M)
      (_ : Module.FinitePresentation A M),
      Nonempty
        (LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M ≃ₗ[
          Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))]
          (genericFiber_picard_localizationModule (R := R) (A := A) x)) := by
  -- TODO: apply `exists_finitePresentation_module_with_localizedLinearEquiv` to the restricted
  -- scalars module `N`, after first supplying the missing localization-side finite-presentation
  -- instance through the canonical equivalence
  -- `localized_restrictScalars_linearEquiv_over_base`.
  sorry

/-- Helper for Lemma 15.122.3: a nonzero base element maps into the denominator submonoid used for
the generic-fiber localization. -/
private theorem algebraMap_mem_genericFiber_denominators
    {r : R} (hr : r ≠ 0) :
    algebraMap R A r ∈ Algebra.algebraMapSubmonoid A (nonZeroDivisors R) := by
  -- Proof comment: this denominator submonoid is exactly the image of the nonzero elements of
  -- `R` inside `A`.
  simpa [Algebra.algebraMapSubmonoid] using
    (show algebraMap R A r ∈ Submonoid.map (algebraMap R A) (nonZeroDivisors R) from
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩)

/-- Helper for Lemma 15.122.3: the `R`-torsion subset of an `A`-module is stable under the
ambient `A`-action, so the source proof can quotient by it inside the category of `A`-modules. -/
private def torsion_submodule_over_base
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Submodule A M :=
  { carrier := Submodule.torsion R M
    zero_mem' := (Submodule.torsion R M).zero_mem
    add_mem' := by
      intro x y hx hy
      exact (Submodule.torsion R M).add_mem hx hy
    smul_mem' := by
      intro a x hx
      rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R) (M := M) x).1 hx with
        ⟨r, hr0, hrx⟩
      refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R) (M := M) (a • x)).2 ?_
      refine ⟨r, hr0, ?_⟩
      have hsax : a • (r • x) = 0 := by
        -- Proof comment: applying the ambient `A`-scalar to a base-torsion relation preserves the
        -- same base annihilator.
        simpa using congrArg (fun y ↦ a • y) hrx
      calc
        r • (a • x) = a • (r • x) := by
          simpa [smul_assoc] using (smul_comm a r x).symm
        _ = 0 := hsax }

/-- Helper for Lemma 15.122.3: after restricting scalars from `A` to `R`, the promoted torsion
submodule is exactly the usual `R`-torsion submodule. -/
private theorem torsion_submodule_over_base_restrictScalars
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Submodule.restrictScalars R (torsion_submodule_over_base (R := R) (A := A) (M := M)) =
      Submodule.torsion R M := by
  -- Proof comment: the promoted `A`-submodule was defined with exactly the ordinary `R`-torsion
  -- carrier.
  ext x
  rfl

/-- Helper for Lemma 15.122.3: the quotient by the promoted `A`-torsion submodule becomes the
usual quotient by `Submodule.torsion R M` after forgetting from `A` to `R`. -/
private noncomputable abbrev torsion_submodule_over_base_quotient_equiv
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    ((M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) : Type _) ≃ₗ[R]
      (M ⧸ Submodule.torsion R M) :=
  (Submodule.Quotient.restrictScalarsEquiv R
      (torsion_submodule_over_base (R := R) (A := A) (M := M))).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars R
        (torsion_submodule_over_base (R := R) (A := A) (M := M)))
      (Submodule.torsion R M)
      (torsion_submodule_over_base_restrictScalars (R := R) (A := A) (M := M)))

/-- Helper for Lemma 15.122.3: the `A`-linear torsion quotient used in the source proof is
torsion free as an `R`-module because it is canonically identified with the usual quotient
`M / Submodule.torsion R M`. -/
private theorem torsion_submodule_over_base_quotient_isTorsionFree
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Module.IsTorsionFree R (M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) := by
  let e :
      ((M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) : Type _) ≃ₗ[R]
        (M ⧸ Submodule.torsion R M) :=
    torsion_submodule_over_base_quotient_equiv (R := R) (A := A) (M := M)
  let _ : Module.IsTorsionFree R (M ⧸ Submodule.torsion R M) := inferInstance
  -- Proof comment: the source quotient is torsion free because it is canonically the usual
  -- quotient by `Submodule.torsion R M`.
  rw [isTorsionFree_iff_forall_mem_torsion_eq_zero]
  intro x hx
  have hx' : e x ∈ Submodule.torsion R (M ⧸ Submodule.torsion R M) := by
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R)
        (M := M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) x).1 hx with
      ⟨r, hr0, hrx⟩
    exact (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R)
        (M := M ⧸ Submodule.torsion R M) (e x)).2 ⟨r, hr0, by simpa using congrArg e hrx⟩
  have hzero : e x = 0 :=
    (isTorsionFree_iff_forall_mem_torsion_eq_zero.mp inferInstance) (e x) hx'
  exact e.injective (by simpa using hzero)

/-- Helper for Lemma 15.122.3: localizing at the image of the nonzero elements of `R` produces an
`R`-torsion-free module because every nonzero base scalar becomes a unit after localization. -/
private theorem localizedModule_isTorsionFree_over_base
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Module.IsTorsionFree R
      (LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M) := by
  rw [isTorsionFree_iff_forall_mem_torsion_eq_zero]
  intro x hx
  rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R)
      (M := LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M) x).1 hx with
    ⟨r, hr0, hrx⟩
  let s : Algebra.algebraMapSubmonoid A (nonZeroDivisors R) :=
    ⟨algebraMap R A r, algebraMap_mem_genericFiber_denominators (R := R) (A := A) hr0⟩
  have hsunit :
      IsUnit (algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
        (algebraMap R A r)) :=
    IsLocalization.map_units
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) s
  rcases hsunit with ⟨u, hu⟩
  have hmul_one :
      ((↑u⁻¹ : Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) *
          algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
            (algebraMap R A r)) = 1 := by
    calc
      (↑u⁻¹ : Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) *
          algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
            (algebraMap R A r)
          = ↑u⁻¹ * ↑u := by rw [hu]
      _ = 1 := Units.inv_mul u
  have hrx' :
      (algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
        (algebraMap R A r)) • x = 0 := by
    simpa using hrx
  -- Proof comment: multiply the annihilating relation by the inverse unit to clear the scalar.
  calc
    x = (1 : Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) • x := by simp
    _ = (((↑u⁻¹ : Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) *
          algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
            (algebraMap R A r)) • x) := by
          rw [hmul_one]
    _ = (↑u⁻¹ : Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))) •
          ((algebraMap A (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
              (algebraMap R A r)) • x) := by
          rw [mul_smul]
    _ = 0 := by rw [hrx', smul_zero]

/-- Helper for Lemma 15.122.3: after inverting the nonzero elements of `R`, the promoted
`R`-torsion submodule of an `A`-module disappears. -/
private theorem localized_torsion_submodule_over_base_eq_bot
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Submodule.localized
        (p := Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
        (torsion_submodule_over_base (R := R) (A := A) (M := M)) =
      ⊥ := by
  let _ : Module.IsTorsionFree R
      (LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M) :=
    localizedModule_isTorsionFree_over_base (R := R) (A := A) (M := M)
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  change m ∈ Submodule.torsion R M at hm
  have hx' :
      IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M)
          m s ∈
        Submodule.torsion R
          (LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M) := by
    rcases (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R) (M := M) m).1 hm with
      ⟨r, hr0, hrm⟩
    refine (mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R)
        (M := LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M)
        (IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M)
          m s)).2 ?_
    refine ⟨r, hr0, ?_⟩
    -- Proof comment: the same base annihilator still kills the localized class.
    have hrmA : (algebraMap R A r) • m = 0 := by
      simpa using hrm
    have hloc :
        (algebraMap R A r) •
            IsLocalizedModule.mk'
              (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M)
              m s = 0 := by
      rw [← IsLocalizedModule.mk'_smul, hrmA, IsLocalizedModule.mk'_zero]
    simpa using hloc
  exact (isTorsionFree_iff_forall_mem_torsion_eq_zero.mp inferInstance) _ hx'

/-- Helper for Lemma 15.122.3: replacing a descended `A`-module by its quotient modulo the
promoted `R`-torsion submodule does not change its localization to the generic fiber. -/
private noncomputable def localized_torsion_quotient_linearEquiv_over_base
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
        (M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) ≃ₗ[
          Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))]
      LocalizedModule (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) M :=
  let Q : Submodule A M := torsion_submodule_over_base (R := R) (A := A) (M := M)
  -- Proof comment: localize the quotient and then identify the localized torsion submodule with
  -- `⊥`, exactly as in the source torsion-quotient replacement step.
  (localizedQuotientEquiv (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Q).symm ≪≫ₗ
    (Submodule.localized
      (p := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Q).quotEquivOfEqBot
      (localized_torsion_submodule_over_base_eq_bot (R := R) (A := A) (M := M))

/-- Helper for Lemma 15.122.3: the torsion-free quotient model `M₀` is finitely presented over
`A` by the valuation-ring finite-presentation criterion applied after quotienting out the
`R`-torsion. -/
private theorem torsionfree_model_has_finitePresentation_over_A
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.Finite A M] :
    Module.FinitePresentation A
      (M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)) := by
  let M₀ : Type _ := M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)
  let _ : Module.IsTorsionFree R M₀ :=
    torsion_submodule_over_base_quotient_isTorsionFree (R := R) (A := A) (M := M)
  let _ : Module.Flat R M₀ :=
    (flat_iff_isTorsionFree_of_valuationRing (A := R) (M := M₀)).2 inferInstance
  -- Proof comment: `M₀` stays finite over `A`, and over a valuation ring torsion-freeness is
  -- exactly the flatness input needed by Lemma `15.25.7 (2)`.
  simpa [M₀] using
    (module_finitePresentation_of_essFiniteType_finite_flat_over_valuationRing
      (A := R) (B := A) (M := M₀))

/-- Lemma 15.122.3: if `R` is a valuation ring and `R → A` is a local, flat, essentially finite
type map with `A` local and regular closed fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal R) A`, equivalently `A ⊗[R] ResidueField R`, then the
generic fiber `GenericFiber = Ideal.Fiber (⊥ : Ideal R) A`, canonically presented by
`A ⊗[R] FractionRing R`, has trivial Picard group. -/
@[stacks 0DLQ]
theorem subsingleton_picardGroup_genericFiber_of_regular_closedFiber
    [IsRegularRing ClosedFiber] :
    Subsingleton (CommRing.Pic GenericFiber) := by
  -- Route correction: the source endgame proves `x = 1` directly via the determinant map, so the
  -- top-level reduction should target triviality of each Picard class rather than freeness.
  refine subsingleton_picardGroup_genericFiber_of_repr_trivial (R := R) (A := A) ?_
  intro x
  obtain ⟨M, _instAddCommGroupM, _instModuleM, hMfp, ⟨eModel⟩⟩ :=
    genericFiber_picard_repr_has_finitePresentation_model (R := R) (A := A) x
  let _ : Module R M := Module.compHom M (algebraMap R A)
  let _ : IsScalarTower R A M := RestrictScalars.isScalarTower R A M
  let _ : Module.Finite A M := inferInstance
  let M₀ := M ⧸ torsion_submodule_over_base (R := R) (A := A) (M := M)
  let eModel0 :=
    localized_torsion_quotient_linearEquiv_over_base (R := R) (A := A) (M := M) ≪≫ₗ eModel
  have hM₀fp : Module.FinitePresentation A M₀ := by
    -- Proof comment: quotienting by the promoted base-torsion preserves the finite-presentation
    -- route needed for the source proof's torsion-free replacement step.
    simpa [M₀] using
      (torsionfree_model_has_finitePresentation_over_A (R := R) (A := A) (M := M))
  have hM₀torsionFree : Module.IsTorsionFree R M₀ := by
    -- Proof comment: the promoted `A`-linear torsion quotient is canonically the usual
    -- `R`-torsion quotient.
    simpa [M₀] using
      (torsion_submodule_over_base_quotient_isTorsionFree (R := R) (A := A) (M := M))
  have hM₀flat : Module.Flat R M₀ := by
    -- Proof comment: over a valuation ring, torsion-free is equivalent to flatness.
    exact (flat_iff_isTorsionFree_of_valuationRing (A := R) (M := M₀)).2 hM₀torsionFree
  -- TODO: use `hM₀fp`, `hM₀flat`, the closed-fiber regularity hypothesis, and the localization
  -- comparison `eModel0` to prove that `M₀[0]` is perfect over `A`, extract a finite free
  -- resolution, and run the source-faithful Euler-characteristic plus determinant endgame.
  sorry

end
