import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_7_8.RegularPrimeOwnerResidueAlgHom

open scoped Representation

noncomputable section

universe v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]
variable [IsIntegralClosure A ℤ K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: Serre's source route first evaluates the fixed fiber over `M`
on honest `p`-regular conjugacy-class representatives before descending to `Γ_K`-classes. This
is the fixed-fiber evaluator obtained by reassembling the owner-factor residue map with the
tensor-product universal property. -/
noncomputable def regular_fiber_prequotient_eval_family_algHom
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) →ₐ[M.1.asIdeal.ResidueField]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField) :=
  Algebra.TensorProduct.lift
    (Pi.constAlgHom (R := M.1.asIdeal.ResidueField)
      (A := PRegularConjClass G p) (B := M.1.asIdeal.ResidueField))
    (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) (p := p) M)
    (owner_pregular_residue_eval_commutes (A := A) (K := K) (G := G) (p := p) M)

/-- Helper for Exercise 12-12.7-8: on an `includeRight` generator of the fixed fiber, the
prequotient evaluator is exactly Serre's owner-factor residue evaluator. -/
@[simp] private theorem regular_fiber_prequotient_eval_family_algHom_includeRight_apply
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (c : PRegularConjClass G p) :
    (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) c =
      (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) (p := p) M f) c := by
  simp [regular_fiber_prequotient_eval_family_algHom]

/-- Helper for Exercise 12-12.7-8: the prequotient evaluator is constant on `Γ_K`-orbits of
`PRegularConjClass G p`, so it descends to Serre's quotient
`PRegularGaloisPowerClass ΓK p`. -/
theorem regular_fiber_prequotient_eval_family_invariant
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (t : ΓK) (c : PRegularConjClass G p) :
    (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M ξ) (t • c) =
      (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c := by
  refine TensorProduct.induction_on ξ ?_ ?_ ?_
  · simp [regular_fiber_prequotient_eval_family_algHom]
  · intro a f
    simp only [regular_fiber_prequotient_eval_family_algHom,
      Algebra.TensorProduct.lift_tmul
        (f := Pi.constAlgHom (R := M.1.asIdeal.ResidueField)
          (A := PRegularConjClass G p) (B := M.1.asIdeal.ResidueField))
        (g := owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) (p := p) M)
        (hfg := owner_pregular_residue_eval_commutes (A := A) (K := K) (G := G) (p := p) M)]
    change
      a * (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) (p := p) M f) (t • c) =
        a * (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) (p := p) M f) c
    rw [owner_pregular_residue_eval_invariant (A := A) (K := K) (G := G) (p := p) M f t c]
  · intro ξ η hξ hη
    simpa [hξ, hη] using congrArg₂ (· + ·) hξ hη

/-- Helper for Exercise 12-12.7-8: descending the prequotient evaluator sends the zero element of
the fixed fiber to the zero function on `PRegularGaloisPowerClass ΓK p`. -/
private theorem regular_fiber_eval_family_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
          (0 : M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
        (regular_fiber_prequotient_eval_family_invariant (A := A) (K := K) (G := G) M
          (0 : M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) =
      0 := by
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  change
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      (0 : M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
      (PRegularConjClass.ofSubtype p x) = 0
  simpa using
    congrArg
      (fun g : PRegularConjClass G p → M.1.asIdeal.ResidueField ↦
        g (PRegularConjClass.ofSubtype p x))
      ((regular_fiber_prequotient_eval_family_algHom
        (A := A) (K := K) (G := G) M).map_zero)

/-- Helper for Exercise 12-12.7-8: descending the prequotient evaluator sends the unit of the
fixed fiber to the constant-one function on `PRegularGaloisPowerClass ΓK p`. -/
private theorem regular_fiber_eval_family_one
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
          (1 : M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
        (regular_fiber_prequotient_eval_family_invariant (A := A) (K := K) (G := G) M
          (1 : M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) =
      1 := by
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  change
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      (1 : M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
      (PRegularConjClass.ofSubtype p x) = 1
  simpa using
    congrArg
      (fun g : PRegularConjClass G p → M.1.asIdeal.ResidueField ↦
        g (PRegularConjClass.ofSubtype p x))
      ((regular_fiber_prequotient_eval_family_algHom
        (A := A) (K := K) (G := G) M).map_one)

/-- Helper for Exercise 12-12.7-8: quotient descent preserves addition for the source-faithful
prequotient evaluator family. -/
private theorem regular_fiber_eval_family_add
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ η : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
          (ξ + η))
        (regular_fiber_prequotient_eval_family_invariant
          (A := A) (K := K) (G := G) M (ξ + η)) =
      pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
          ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ)
          (regular_fiber_prequotient_eval_family_invariant
            (A := A) (K := K) (G := G) M ξ) +
        pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
          ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) η)
          (regular_fiber_prequotient_eval_family_invariant
            (A := A) (K := K) (G := G) M η) := by
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  change
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      (ξ + η)) (PRegularConjClass.ofSubtype p x) =
      ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ)
          (PRegularConjClass.ofSubtype p x) +
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) η)
          (PRegularConjClass.ofSubtype p x)
  simpa using
    congrArg
      (fun g : PRegularConjClass G p → M.1.asIdeal.ResidueField ↦
        g (PRegularConjClass.ofSubtype p x))
      ((regular_fiber_prequotient_eval_family_algHom
        (A := A) (K := K) (G := G) M).map_add ξ η)

/-- Helper for Exercise 12-12.7-8: quotient descent preserves multiplication for the
source-faithful prequotient evaluator family. -/
private theorem regular_fiber_eval_family_mul
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ η : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
          (ξ * η))
        (regular_fiber_prequotient_eval_family_invariant
          (A := A) (K := K) (G := G) M (ξ * η)) =
      pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
          ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ)
          (regular_fiber_prequotient_eval_family_invariant
            (A := A) (K := K) (G := G) M ξ) *
        pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
          ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) η)
          (regular_fiber_prequotient_eval_family_invariant
            (A := A) (K := K) (G := G) M η) := by
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  change
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      (ξ * η)) (PRegularConjClass.ofSubtype p x) =
      ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ)
          (PRegularConjClass.ofSubtype p x) *
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) η)
          (PRegularConjClass.ofSubtype p x)
  simpa using
    congrArg
      (fun g : PRegularConjClass G p → M.1.asIdeal.ResidueField ↦
        g (PRegularConjClass.ofSubtype p x))
      ((regular_fiber_prequotient_eval_family_algHom
        (A := A) (K := K) (G := G) M).map_mul ξ η)

/-- Helper for Exercise 12-12.7-8: quotient descent preserves scalar constants from
`M.1.asIdeal.ResidueField` for the prequotient evaluator family. -/
private theorem regular_fiber_eval_family_commutes
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (a : M.1.asIdeal.ResidueField) :
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
          (algebraMap M.1.asIdeal.ResidueField
            (M.1.asIdeal.Fiber
              (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) a))
        (regular_fiber_prequotient_eval_family_invariant
          (A := A) (K := K) (G := G) M
          (algebraMap M.1.asIdeal.ResidueField
            (M.1.asIdeal.Fiber
              (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) a)) =
      algebraMap M.1.asIdeal.ResidueField
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) a := by
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  change
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      (algebraMap M.1.asIdeal.ResidueField
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) a))
      (PRegularConjClass.ofSubtype p x) = a
  simpa using
    congrArg
      (fun g : PRegularConjClass G p → M.1.asIdeal.ResidueField ↦
        g (PRegularConjClass.ofSubtype p x))
      ((regular_fiber_prequotient_eval_family_algHom
        (A := A) (K := K) (G := G) M).commutes a)

/-- Helper for Exercise 12-12.7-8: Serre's canonical evaluator on the fixed fiber over `M`. -/
noncomputable def regular_fiber_eval_family_algHom
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) →ₐ[M.1.asIdeal.ResidueField]
      (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  { toFun := fun ξ ↦
      pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
        ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ)
        (regular_fiber_prequotient_eval_family_invariant (A := A) (K := K) (G := G) M ξ)
    map_zero' := regular_fiber_eval_family_zero (A := A) (K := K) (G := G) M
    map_one' := regular_fiber_eval_family_one (A := A) (K := K) (G := G) M
    map_add' := regular_fiber_eval_family_add (A := A) (K := K) (G := G) M
    map_mul' := regular_fiber_eval_family_mul (A := A) (K := K) (G := G) M
    commutes' := regular_fiber_eval_family_commutes (A := A) (K := K) (G := G) M }

/-- Helper for Exercise 12-12.7-8: evaluating the descended regular-fiber family on the
`Γ_K`-class of a chosen `p`-regular representative simply recovers the source-level prequotient
value on that representative. -/
@[simp] theorem regular_fiber_eval_family_algHom_mk
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (x : {x : G // IsPRegular p x}) :
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (pRegularGaloisPowerClassMk ΓK p x) =
      (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (PRegularConjClass.ofSubtype p x) := by
  rfl

/-- Helper for Exercise 12-12.7-8: vanishing of the descended evaluator on the `Γ_K`-class of a
chosen representative is exactly vanishing of the prequotient evaluator on that representative. -/
@[simp] theorem regular_fiber_eval_family_algHom_mk_eq_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (x : {x : G // IsPRegular p x}) :
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (pRegularGaloisPowerClassMk ΓK p x) = 0 ↔
      (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (PRegularConjClass.ofSubtype p x) = 0 := by
  rw [regular_fiber_eval_family_algHom_mk]

/-- Helper for Exercise 12-12.7-8: on an honest `p`-regular representative, evaluating the
prequotient family on an `includeRight` generator is zero exactly when the character value is
congruent modulo the fixed maximal ideal `M`. -/
theorem regular_fiber_prequotient_eval_includeRight_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : {x : G // IsPRegular p x})
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    ((regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)
        (PRegularConjClass.ofSubtype p x) = 0) ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  rw [regular_fiber_prequotient_eval_family_algHom_includeRight_apply
    (A := A) (K := K) (G := G) (p := p) M f (PRegularConjClass.ofSubtype p x)]
  exact
    owner_pregular_residue_eval_ofSubtype_zero_iff
      (A := A) (K := K) (G := G) (p := p) M x f

/-- Helper for Exercise 12-12.7-8: the canonical evaluator detects vanishing on the
`includeRight` generator exactly by Serre's intrinsic modulo-`M` condition on the chosen
`p`-regular `Γ_K`-class. -/
theorem regular_fiber_eval_family_includeRight_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) c = 0) ↔
      ∀ x : {x : G // IsPRegular p x},
        pRegularGaloisPowerClassMk ΓK p x = c →
          ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  let gpre : PRegularConjClass G p → M.1.asIdeal.ResidueField :=
    (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M)
      ((Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)
  let hgpre : ∀ t : ΓK, ∀ c' : PRegularConjClass G p, gpre (t • c') = gpre c' :=
    regular_fiber_prequotient_eval_family_invariant
      (A := A) (K := K) (G := G) M
      ((Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)
  have hdesc :=
    pRegularGaloisPowerClassLift_eq_zero_iff_forall_representatives_eq_zero
      (K := K) (G := G) (p := p) gpre hgpre c
  constructor
  · intro h x hx
    have hzero : pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) gpre hgpre c = 0 := by
      simpa [regular_fiber_eval_family_algHom, gpre, hgpre] using h
    exact
      (regular_fiber_prequotient_eval_includeRight_zero_iff
        (A := A) (K := K) (G := G) M x f).mp ((hdesc.mp hzero) x hx)
  · intro h
    have hzero : pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) gpre hgpre c = 0 :=
      hdesc.mpr fun x hx ↦
        (regular_fiber_prequotient_eval_includeRight_zero_iff
          (A := A) (K := K) (G := G) M x f).mpr (h x hx)
    simpa [regular_fiber_eval_family_algHom, gpre, hgpre] using hzero

end RegularPrime

end

end Representation
