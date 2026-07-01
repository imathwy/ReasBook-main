import Serre.Chap12.Exercise_12_12_7_8.RegularPrimeTensorOwner

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278RegularPrimeResidueEvaluationGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278RegularPrimeResidueEvaluationGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: after base-changing from `A` to the residue field of `M`, the
fixed fiber owner is linearly identified with Serre's tensor owner
`M.1.asIdeal.ResidueField ⊗ R_K(G)`. This is the transport half of the regular-fiber source
route, before evaluation on `p`-regular representatives. -/
noncomputable def regular_fiber_to_tensorCharacterRingLinearEquiv
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    TensorProduct A M.1.asIdeal.ResidueField
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) ≃ₗ[M.1.asIdeal.ResidueField]
      TensorProduct ℤ M.1.asIdeal.ResidueField (R[K](G)) := by
  let e₁ :
      TensorProduct A M.1.asIdeal.ResidueField
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) ≃ₗ[M.1.asIdeal.ResidueField]
        TensorProduct A M.1.asIdeal.ResidueField (TensorProduct ℤ A (R[K](G))) :=
    LinearEquiv.baseChange A M.1.asIdeal.ResidueField
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
      (TensorProduct ℤ A (R[K](G)))
      (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G))
  exact e₁.trans <|
    (fiber_linearEquiv_tensorCharacterRingOverField_baseChange
      (A := A) (K := K) (G := G) (F := M.1.asIdeal.ResidueField))

/-- Helper for Exercise 12-12.7-8: on a genuine pure tensor in the abstract owner
`A ⊗ R_K(G)`, the base-change associativity equivalence simply multiplies the scalar coefficients.
This is the coefficient-normalization step used before later residue-field evaluations. -/
theorem fiber_linearEquiv_tensorCharacterRingOverField_baseChange_tmul_tmul
    (F : Type*) [Field F] [Algebra A F]
    (a : F) (b : A) (χ : R[K](G)) :
    (fiber_linearEquiv_tensorCharacterRingOverField_baseChange
      (A := A) (K := K) (G := G) (F := F))
      ((a : F) ⊗ₜ[A] (b ⊗ₜ[ℤ] χ)) =
        (a * algebraMap A F b) ⊗ₜ[ℤ] χ := by
  rw [fiber_linearEquiv_tensorCharacterRingOverField_baseChange,
    fiber_algEquiv_tensorCharacterRingOverField_baseChange]
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 12-12.7-8: transporting an `includeRight` generator of the fixed fiber
through `regular_fiber_to_tensorCharacterRingLinearEquiv` reduces the base-change step to the
pure tensor `(1 : k(M)) ⊗ owner(f)` before the final associativity normalization. This is the
transport-stable normal form needed before Serre's representative-level residue evaluation is
introduced. -/
theorem regular_fiber_to_tensorCharacterRingLinearEquiv_includeRight_formula
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    regular_fiber_to_tensorCharacterRingLinearEquiv (A := A) (K := K) (G := G) (p := p) M
      ((Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) =
        (fiber_linearEquiv_tensorCharacterRingOverField_baseChange
          (A := A) (K := K) (G := G) (F := M.1.asIdeal.ResidueField))
          (((1 : M.1.asIdeal.ResidueField) ⊗ₜ[A]
            ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f))) := by
  simp [regular_fiber_to_tensorCharacterRingLinearEquiv,
    fiber_linearEquiv_tensorCharacterRingOverField_baseChange,
    fiber_algEquiv_tensorCharacterRingOverField_baseChange]
  rfl

/-- Helper for Exercise 12-12.7-8: realizing the tensor owner representative attached to an
owner element `f` gives back the original `K`-valued class function. This is the source-side
normalization used before any residue-field descent is introduced. -/
@[simp] theorem tensorCharacterRingRealization_ownerLinearEquiv_apply
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    tensorCharacterRingRealization (A := A) (K := K) (G := G)
        ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f) =
      (f : G → K) := by
  have howner :
      tensorCharacterRingToOwnerLinearMap (A := A) (K := K) (G := G)
          ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f) = f := by
    simpa [ownerLinearEquiv_tensorCharacterRing] using
      (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)).symm_apply_apply f
  exact congrArg
    (fun z : characterRingOverFieldAlgebraScalarExtension A K G ↦ (z : G → K))
    howner

/-- Helper for Exercise 12-12.7-8: on an honest `p`-regular representative, the tensor owner
representative chosen by `ownerLinearEquiv_tensorCharacterRing` evaluates exactly as the original
owner function. This is the representative-level source bridge needed before passing to residue
classes. -/
@[simp] theorem tensorCharacterRingPRegularLift_local_ownerLinearEquiv_ofSubtype
    (x : {x : G // IsPRegular p x})
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    tensorCharacterRingPRegularLift_local (A := A) (K := K) (G := G) p
        ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f)
        (PRegularConjClass.ofSubtype p x) =
      (f : G → K) x.1 := by
  rw [tensorCharacterRingPRegularLift_local_ofSubtype,
    tensorCharacterRingRealization_ownerLinearEquiv_apply]

/-- Helper for Exercise 12-12.7-8: every `p`-regular conjugacy class has a chosen
`p`-regular representative. This keeps later source-faithful orbit arguments on honest
representatives instead of opening the quotient structure of `PRegularConjClass G p`. -/
theorem pRegularConjClass_ofSubtype_surjective
    (c : PRegularConjClass G p) :
    ∃ x : {x : G // IsPRegular p x}, PRegularConjClass.ofSubtype p x = c := by
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep (c : ConjClasses G)
  have hx_mem : x ∈ (c : ConjClasses G).carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  have hx_reg : IsPRegular p x := c.2 x hx_mem
  refine ⟨⟨x, hx_reg⟩, ?_⟩
  apply Subtype.ext
  simpa [PRegularConjClass.coe_ofSubtype, hx]

/-- Helper for Exercise 12-12.7-8: raising a `p`-regular element to the natural-number value of a
power-action unit preserves `p`-regularity. This is the source-level input for the local
`Γ_K`-action wrapper on `PRegularConjClass`. -/
theorem isPRegular_pow_unit_val
    (t : (ZMod (Monoid.exponent G))ˣ) {x : G} (hx : IsPRegular p x) :
    IsPRegular p (x ^ (t : ZMod (Monoid.exponent G)).val) := by
  have hcop :
      Nat.Coprime (orderOf x) ((t : ZMod (Monoid.exponent G)).val) :=
    (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent x) (ZMod.val_coe_unit_coprime t)).symm
  simpa [IsPRegular, hcop.orderOf_pow] using hx

/-- Helper for Exercise 12-12.7-8: the `Γ_K`-action on a `p`-regular representative class is the
class of the corresponding powered representative. This local wrapper replaces the inaccessible
private rewrite from `PowerClassActions.lean` and is the exact source-level rewrite needed for the
regular-fiber invariance proof. -/
theorem pRegularConjClass_smul_ofSubtype_local
    (t : ΓK) (s : {x : G // IsPRegular p x}) :
    t • PRegularConjClass.ofSubtype p s =
      PRegularConjClass.ofSubtype p
        ⟨s.1 ^ ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val,
          isPRegular_pow_unit_val (G := G) (p := p) (t := (t : (ZMod (Monoid.exponent G))ˣ)) s.2⟩ := by
  apply Subtype.ext
  change ((t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk s.1) =
    ConjClasses.mk (s.1 ^ ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val)
  simpa using ConjClasses.smul_mk (G := G) (t : (ZMod (Monoid.exponent G))ˣ) s.1

/-- Helper for Exercise 12-12.7-8: taking the `Γ_K`-power of a chosen `p`-regular representative
does not change its image in Serre's quotient `PRegularGaloisPowerClass ΓK p`. This is the
quotient-level normalization that later residue arguments should use instead of reopening the
orbit relation by hand. -/
theorem pRegularGaloisPowerClassMk_of_pow_eq
    (t : ΓK) (x : {x : G // IsPRegular p x}) :
    pRegularGaloisPowerClassMk ΓK p
        ⟨x.1 ^ ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val,
          isPRegular_pow_unit_val (G := G) (p := p)
            (t := (t : (ZMod (Monoid.exponent G))ˣ)) x.2⟩ =
      pRegularGaloisPowerClassMk ΓK p x := by
  change Quotient.mk'' (t • PRegularConjClass.ofSubtype p x) =
    Quotient.mk'' (PRegularConjClass.ofSubtype p x)
  rw [pRegularConjClass_smul_ofSubtype_local]
  apply Quotient.sound
  change PRegularConjClass.ofSubtype p
      ⟨x.1 ^ ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val,
        isPRegular_pow_unit_val (G := G) (p := p)
          (t := (t : (ZMod (Monoid.exponent G))ˣ)) x.2⟩ ∈
    MulAction.orbit ΓK (PRegularConjClass.ofSubtype p x)
  exact ⟨t, rfl⟩

/-- Helper for Exercise 12-12.7-8: an algebra map out of the fixed fiber over `M` is determined
by its values on the owner-factor generators `includeRight f`. This isolates the tensor-product
packaging step from the source-level residue computations on those generators. -/
theorem regular_fiber_algHom_ext_of_eq_on_includeRight
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {B : Type*} [CommSemiring B] [Algebra A B] [Algebra M.1.asIdeal.ResidueField B]
    [IsScalarTower A M.1.asIdeal.ResidueField B]
    {φ ψ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) →ₐ[M.1.asIdeal.ResidueField] B}
    (h :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        φ ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) =
        ψ ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) :
    φ = ψ := by
  apply Algebra.TensorProduct.ext_ring
  ext f
  exact h f

/-- Helper for Exercise 12-12.7-8: every owner element in `A ⊗ R_K(G)` is already constant on
Serre's arithmetic `Γ_K`-classes. This is the source-level invariance input before any reduction
modulo the fixed maximal ideal is introduced. -/
theorem owner_isConstantOnGaloisPowerClasses
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    IsConstantOnGaloisPowerClasses ΓK ((f :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K) := by
  exact
    isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension
      (A := A) (K := K) (G := G) f.2

/-- Helper for Exercise 12-12.7-8: before reducing modulo `M`, an owner element already gives a
`K`-valued function on `p`-regular conjugacy classes by the ordinary class-function lift. This is
the source-level evaluator that the missing residue-field bridge should factor through. -/
def owner_pregular_eval
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    PRegularConjClass G p → K :=
  (owner_isConstantOnGaloisPowerClasses (A := A) (K := K) (G := G) (p := p) f).isClassFunction
    .pRegularLift p

/-- Helper for Exercise 12-12.7-8: on an honest `p`-regular representative, the pre-residue owner
evaluator recovers the original owner value. This keeps the future residue reduction pinned to
Serre's chosen representatives. -/
@[simp] theorem owner_pregular_eval_ofSubtype
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (x : {x : G // IsPRegular p x}) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f
        (PRegularConjClass.ofSubtype p x) =
      (f : G → K) x.1 := by
  simpa [owner_pregular_eval] using
    IsClassFunction.pRegularLift_ofSubtype
      (hf := (owner_isConstantOnGaloisPowerClasses
        (A := A) (K := K) (G := G) (p := p) f).isClassFunction)
      x

/-- Helper for Exercise 12-12.7-8: the source-level owner evaluator on `p`-regular conjugacy
classes is already constant on `Γ_K`-orbits. This isolates the arithmetic quotient step from the
still-missing reduction to the residue field of `M`. -/
theorem owner_pregular_eval_invariant
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (t : ΓK) (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f (t • c) =
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  rw [pRegularConjClass_smul_ofSubtype_local,
    owner_pregular_eval_ofSubtype (A := A) (K := K) (G := G) (p := p) f,
    owner_pregular_eval_ofSubtype (A := A) (K := K) (G := G) (p := p) f]
  let hconst :
      IsConstantOnGaloisPowerClasses ΓK ((f :
        characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K) :=
    owner_isConstantOnGaloisPowerClasses (A := A) (K := K) (G := G) (p := p) f
  have hpow :=
    (isConstantOnGaloisPowerClasses_iff_forall_pow_eq
      (ΓK := ΓK)
      (f := ((f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K))
      hconst.isClassFunction).1 hconst x.1 t
  exact hpow.symm

/-- Helper for Exercise 12-12.7-8: the owner-level `K`-valued evaluation on `p`-regular
representatives already depends only on the corresponding `Γ_K`-class. This is the exact
source-faithful quotient bridge needed before reducing values modulo the fixed maximal ideal. -/
theorem owner_pregular_eval_eq_of_galoisPowerClass_eq
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    {x y : {x : G // IsPRegular p x}}
    (hxy : pRegularGaloisPowerClassMk ΓK p x = pRegularGaloisPowerClassMk ΓK p y) :
    (f : G → K) x.1 = (f : G → K) y.1 := by
  let g : PRegularGaloisPowerClass ΓK p → K :=
    pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
      (owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f)
      (owner_pregular_eval_invariant (A := A) (K := K) (G := G) (p := p) f)
  have hxg : g (pRegularGaloisPowerClassMk ΓK p x) = (f : G → K) x.1 := by
    simpa [g] using
      (pRegularGaloisPowerClassLift_mk (K := K) (G := G) (p := p)
        (owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f)
        (owner_pregular_eval_invariant (A := A) (K := K) (G := G) (p := p) f) x)
  have hyg : g (pRegularGaloisPowerClassMk ΓK p y) = (f : G → K) y.1 := by
    simpa [g] using
      (pRegularGaloisPowerClassLift_mk (K := K) (G := G) (p := p)
        (owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f)
        (owner_pregular_eval_invariant (A := A) (K := K) (G := G) (p := p) f) y)
  calc
    (f : G → K) x.1 = g (pRegularGaloisPowerClassMk ΓK p x) := hxg.symm
    _ = g (pRegularGaloisPowerClassMk ΓK p y) := by rw [hxy]
    _ = (f : G → K) y.1 := hyg

section IntegralClosureArithmeticBridge

variable [IsIntegralClosure A ℤ K]

/-- Helper for Exercise 12-12.7-8: every value of a virtual `K`-character is integral over
`ℤ`. This is the source-level arithmetic input needed before one can ask whether a `p`-regular
value already comes from the coefficient ring `A`. -/
theorem characterRingOverField_value_isIntegral
    (χ : R[K](G)) (x : G) :
    IsIntegral ℤ ((χ : G → K) x) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional K ρ := hρfd
    simpa using Representation.char_isIntegral ρ.ρ x
  · intro n
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro f g _ _ hf hg
    exact hf.mul hg

/-- Helper for Exercise 12-12.7-8: under the missing integral-closure hypothesis, a
`p`-regular value of a virtual `K`-character already lies in the image of `A → K`. This is
Serre's arithmetic source statement before any tensor-owner or fiber packaging. -/
theorem characterRingOverField_value_mem_range_of_isPRegular_of_isIntegralClosure
    (χ : R[K](G)) (x : {x : G // IsPRegular p x}) :
    ((χ : G → K) x.1) ∈ Set.range (algebraMap A K) := by
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := K)).mp
      (characterRingOverField_value_isIntegral (G := G) (A := A) (K := K) χ x.1)

/-- Helper for Exercise 12-12.7-8: under the missing integral-closure hypothesis, every
realized tensor-owner value on a `p`-regular representative already comes from `A`. This is the
tensor-level bridge needed to reduce the owner evaluator to `residueFieldOfLiftedValue`. -/
theorem tensorCharacterRingRealization_value_mem_range_on_pRegular_representatives
    (x : {x : G // IsPRegular p x})
    (ξ : TensorProduct ℤ A (R[K](G))) :
    tensorCharacterRingRealization (A := A) (K := K) (G := G) ξ x.1 ∈
      Set.range (algebraMap A K) := by
  induction ξ using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | tmul a χ =>
      rcases
          characterRingOverField_value_mem_range_of_isPRegular_of_isIntegralClosure
            (G := G) (A := A) (K := K) (p := p) χ x with
        ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      simp [tensorCharacterRingRealization_apply_tmul, Algebra.smul_def, hb, mul_assoc]
  | add ξ η hξ hη =>
      rcases hξ with ⟨a, ha⟩
      rcases hη with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp [map_add, ha, hb]

/-- Helper for Exercise 12-12.7-8: under the missing integral-closure hypothesis, every owner
value on a `p`-regular representative already lies in the image of `A → K`. This is the exact
owner-level arithmetic bridge the residue evaluator needs once the theorem is stated with the
correct arithmetic assumptions. -/
theorem owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (x : {x : G // IsPRegular p x}) :
    ((f : G → K) x.1) ∈ Set.range (algebraMap A K) := by
  simpa [tensorCharacterRingRealization_ownerLinearEquiv_apply]
    using
      tensorCharacterRingRealization_value_mem_range_on_pRegular_representatives
        (G := G) (A := A) (K := K) (p := p) x
        ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f)

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, the source-level owner
evaluation on a `p`-regular conjugacy class already lies in the image of `A → K`. This packages
the representative-level arithmetic bridge at exactly the class-function layer used by Serre's
fixed-fiber construction. -/
theorem owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
      Set.range (algebraMap A K) := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simpa [owner_pregular_eval_ofSubtype] using
    owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) f x

end IntegralClosureArithmeticBridge

/-- Helper for Exercise 12-12.7-8: an exact `A`-valued lift of the owner evaluation on
`p`-regular conjugacy classes exists exactly when every class value already lies in the image of
`A → K`. This isolates the remaining arithmetic frontier for the regular-fiber residue
construction from the later tensor-product packaging. -/
theorem exists_owner_pregular_class_lift_iff
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    (∃ φ : PRegularConjClass G p → A,
        ∀ c : PRegularConjClass G p,
          algebraMap A K (φ c) =
            owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c) ↔
      ∀ c : PRegularConjClass G p,
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
          Set.range (algebraMap A K) := by
  constructor
  · rintro ⟨φ, hφ⟩ c
    -- An explicit class lift immediately witnesses that the owner value comes from `A`.
    exact ⟨φ c, hφ c⟩
  · intro hRange
    classical
    -- Conversely, choose one `A`-preimage independently for each `p`-regular class.
    refine ⟨fun c ↦ Classical.choose (hRange c), ?_⟩
    intro c
    exact Classical.choose_spec (hRange c)

omit [IsDomain A] in
/-- Helper for Exercise 12-12.7-8: if a `K`-value is known to come from `A`, choose one
`A`-preimage and reduce it modulo the fixed prime ideal. This isolates the coefficient-side bridge
from owner values in `K` to residue-field values in `M.1.asIdeal.ResidueField`. -/
noncomputable def residueFieldOfLiftedValue
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (z : K) (hz : z ∈ Set.range (algebraMap A K)) :
    M.1.asIdeal.ResidueField :=
  algebraMap A M.1.asIdeal.ResidueField (Classical.choose hz)

omit [IsDomain A] in
/-- Helper for Exercise 12-12.7-8: the chosen residue class is zero exactly when the underlying
`K`-value is represented by an element of the fixed maximal ideal `M`. This is the precise
zero-test needed once the owner evaluator is reduced to `A`-lifted values. -/
@[simp] theorem residueFieldOfLiftedValue_eq_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (z : K) (hz : z ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hz = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = z := by
  constructor
  · intro hz0
    refine ⟨⟨Classical.choose hz, ?_⟩, ?_⟩
    · exact (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal)).mp hz0
    · exact Classical.choose_spec hz
  · rintro ⟨a, ha⟩
    have hEq : (Classical.choose hz : A) = a.1 := by
      apply (IsFractionRing.injective A K)
      calc
        algebraMap A K (Classical.choose hz) = z := Classical.choose_spec hz
        _ = algebraMap A K a.1 := ha.symm
    simpa [residueFieldOfLiftedValue, hEq] using a.2

omit [IsDomain A] in
/-- Helper for Exercise 12-12.7-8: if two proofs show that the same `K`-value comes from `A`,
they define the same residue class modulo `M`. This removes proof-choice noise from the eventual
owner-level residue evaluator. -/
theorem residueFieldOfLiftedValue_eq_of_eq
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {z : K} (hz hw : z ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hz =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hw := by
  apply congrArg (algebraMap A M.1.asIdeal.ResidueField)
  apply (IsFractionRing.injective A K)
  calc
    algebraMap A K (Classical.choose hz) = z := Classical.choose_spec hz
    _ = algebraMap A K (Classical.choose hw) := (Classical.choose_spec hw).symm

omit [IsDomain A] in
/-- Helper for Exercise 12-12.7-8: equal `K`-values with `A`-lifts give equal residue classes.
This is the congruence form used when `Γ_K`-orbit equalities are later transported to the residue
evaluator. -/
theorem residueFieldOfLiftedValue_congr
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {z w : K} (hz : z ∈ Set.range (algebraMap A K))
    (hw : w ∈ Set.range (algebraMap A K)) (hzw : z = w) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hz =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w hw := by
  subst hzw
  exact residueFieldOfLiftedValue_eq_of_eq (A := A) (K := K) (p := p) M hz hw

/-- Helper for Exercise 12-12.7-8: once the arithmetic descent theorem supplies a pointwise
`A`-lift for `owner_pregular_eval`, the residue-field evaluator on `p`-regular conjugacy classes
is defined by reducing those chosen lifts modulo `M`. This packages the coefficient-side bridge in
the exact form later used by the regular-fiber tensor argument. -/
noncomputable def owner_pregular_residue_eval_of_range
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (hRange :
      ∀ c : PRegularConjClass G p,
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
          Set.range (algebraMap A K)) :
    PRegularConjClass G p → M.1.asIdeal.ResidueField :=
  fun c ↦
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M
      (owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c)
      (hRange c)

/-- Helper for Exercise 12-12.7-8: once the owner evaluation is known to take `A`-values on
`p`-regular classes, the residue evaluator is already constant on `Γ_K`-orbits. This isolates the
orbit argument from the still-missing arithmetic descent theorem that supplies `hRange`. -/
theorem owner_pregular_residue_eval_of_range_invariant
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (hRange :
      ∀ c : PRegularConjClass G p,
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
          Set.range (algebraMap A K))
    (t : ΓK) (c : PRegularConjClass G p) :
    owner_pregular_residue_eval_of_range
        (A := A) (K := K) (G := G) (p := p) M f hRange (t • c) =
      owner_pregular_residue_eval_of_range
        (A := A) (K := K) (G := G) (p := p) M f hRange c := by
  -- The residue evaluator only depends on the underlying owner value in `K`, so the existing
  -- `Γ_K`-orbit invariance of `owner_pregular_eval` descends directly.
  apply residueFieldOfLiftedValue_congr (A := A) (K := K) (p := p) M
  · exact hRange (t • c)
  · exact hRange c
  · simpa using owner_pregular_eval_invariant (A := A) (K := K) (G := G) (p := p) f t c

/-- Helper for Exercise 12-12.7-8: once the missing arithmetic descent theorem supplies
representative-level `A`-lifts of the owner values, vanishing of the residue evaluator is exactly
Serre's congruence criterion modulo the fixed maximal ideal `M`. -/
@[simp] theorem owner_pregular_residue_eval_of_range_ofSubtype_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (hRange :
      ∀ c : PRegularConjClass G p,
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
          Set.range (algebraMap A K))
    (x : {x : G // IsPRegular p x}) :
    owner_pregular_residue_eval_of_range
        (A := A) (K := K) (G := G) (p := p) M f hRange
        (PRegularConjClass.ofSubtype p x) = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  -- Normalize the class-level residue evaluator to the representative value and apply the
  -- standard zero criterion for `residueFieldOfLiftedValue`.
  rw [owner_pregular_residue_eval_of_range, owner_pregular_eval_ofSubtype]
  simpa using
    (residueFieldOfLiftedValue_eq_zero_iff (A := A) (K := K) (p := p) M
      ((f : G → K) x.1)
      (hRange (PRegularConjClass.ofSubtype p x)))

/-- Helper for Exercise 12-12.7-8: once two `p`-regular representatives define the same
`Γ_K`-class, any chosen `A`-lifts of their common owner value reduce to the same residue class.
This removes the quotient/interface bookkeeping from the later residue-evaluator invariance step.
-/
theorem residueFieldOfLiftedValue_eq_of_galoisPowerClass_eq
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    {x y : {x : G // IsPRegular p x}}
    (hx : (f : G → K) x.1 ∈ Set.range (algebraMap A K))
    (hy : (f : G → K) y.1 ∈ Set.range (algebraMap A K))
    (hxy : pRegularGaloisPowerClassMk ΓK p x = pRegularGaloisPowerClassMk ΓK p y) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M ((f : G → K) x.1) hx =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M ((f : G → K) y.1) hy := by
  exact
    residueFieldOfLiftedValue_congr (A := A) (K := K) (p := p) M hx hy
      (owner_pregular_eval_eq_of_galoisPowerClass_eq
        (A := A) (K := K) (G := G) (p := p) f hxy)

/-- Helper for Exercise 12-12.7-8: once an owner element `f` is presented by an `A`-valued lift
`φ`, reducing `φ` modulo `M` depends only on the `p`-regular `Γ_K`-class. This is the exact
source-level congruence statement needed after the missing lift-existence bridge is supplied. -/
theorem lifted_owner_residue_eq_of_galoisPowerClass_eq
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    {x y : {x : G // IsPRegular p x}}
    (hxy : pRegularGaloisPowerClassMk ΓK p x = pRegularGaloisPowerClassMk ΓK p y) :
    algebraMap A M.1.asIdeal.ResidueField (φ x.1) =
      algebraMap A M.1.asIdeal.ResidueField (φ y.1) := by
  apply congrArg (algebraMap A M.1.asIdeal.ResidueField)
  apply (IsFractionRing.injective A K)
  calc
    algebraMap A K (φ x.1) = (f : G → K) x.1 := by
      simpa [Function.comp] using congrFun hφ x.1
    _ = (f : G → K) y.1 :=
      owner_pregular_eval_eq_of_galoisPowerClass_eq
        (A := A) (K := K) (G := G) (p := p) f hxy
    _ = algebraMap A K (φ y.1) := by
      simpa [Function.comp] using (congrFun hφ y.1).symm

/-- Helper for Exercise 12-12.7-8: once an owner element `f` is presented by an `A`-valued lift
`φ`, the residue class of `φ(x)` vanishes exactly when the original owner value lies in the fixed
maximal ideal `M`. This is the representative-level zero test needed after the missing lift data
is chosen. -/
@[simp] theorem lifted_owner_residue_eq_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    (x : {x : G // IsPRegular p x}) :
    algebraMap A M.1.asIdeal.ResidueField (φ x.1) = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  constructor
  · intro hzero
    refine ⟨⟨φ x.1, ?_⟩, ?_⟩
    · exact (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal)).mp hzero
    · simpa [Function.comp] using congrFun hφ x.1
  · rintro ⟨a, ha⟩
    have hEq : φ x.1 = a.1 := by
      apply (IsFractionRing.injective A K)
      calc
        algebraMap A K (φ x.1) = (f : G → K) x.1 := by
          simpa [Function.comp] using congrFun hφ x.1
        _ = algebraMap A K a.1 := ha.symm
    simpa [hEq] using a.2

section IntegralClosureResidueEvaluator

variable [IsIntegralClosure A ℤ K]

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, Serre's source-level
residue evaluator on `p`-regular conjugacy classes is obtained by reducing the already
`A`-valued owner evaluation modulo the fixed maximal ideal `M`. This is the arithmetic core of
the stalled ambient owner evaluator. -/
noncomputable def owner_pregular_residue_eval_of_isIntegralClosure
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    PRegularConjClass G p → M.1.asIdeal.ResidueField :=
  fun c ↦
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M
      (owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c)
      (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) f c)

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, evaluating the class
level residue map on an honest `p`-regular representative is exactly reducing the corresponding
owner value modulo `M`. This is the representative formula the ambient `sorry` block still needs.
-/
@[simp] theorem owner_pregular_residue_eval_of_isIntegralClosure_ofSubtype
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (x : {x : G // IsPRegular p x}) :
    owner_pregular_residue_eval_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) M f
        (PRegularConjClass.ofSubtype p x) =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M ((f : G → K) x.1)
        (owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
          (A := A) (K := K) (G := G) (p := p) f x) := by
  let hxClass :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f
          (PRegularConjClass.ofSubtype p x) ∈
        Set.range (algebraMap A K) :=
    owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) f (PRegularConjClass.ofSubtype p x)
  let hxRep :
      ((f : G → K) x.1) ∈ Set.range (algebraMap A K) :=
    owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) f x
  have hvalue :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f
          (PRegularConjClass.ofSubtype p x) =
        (f : G → K) x.1 := by
    simpa using owner_pregular_eval_ofSubtype (A := A) (K := K) (G := G) (p := p) f x
  simpa [owner_pregular_residue_eval_of_isIntegralClosure, hxClass, hxRep] using
    residueFieldOfLiftedValue_congr (A := A) (K := K) (p := p) M hxClass hxRep hvalue

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, the source-level
residue evaluator is constant on `Γ_K`-orbits of `PRegularConjClass G p`. This is Serre's
orbit-invariance step before passing to `PRegularGaloisPowerClass ΓK p`. -/
theorem owner_pregular_residue_eval_of_isIntegralClosure_invariant
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (t : ΓK) (c : PRegularConjClass G p) :
    owner_pregular_residue_eval_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) M f (t • c) =
      owner_pregular_residue_eval_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) M f c := by
  let ht :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f (t • c) ∈
        Set.range (algebraMap A K) :=
    owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) f (t • c)
  let hc :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
        Set.range (algebraMap A K) :=
    owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) f c
  have hvalue :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f (t • c) =
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c := by
    simpa using owner_pregular_eval_invariant (A := A) (K := K) (G := G) (p := p) f t c
  simpa [owner_pregular_residue_eval_of_isIntegralClosure, ht, hc] using
    residueFieldOfLiftedValue_congr (A := A) (K := K) (p := p) M ht hc hvalue

/-- Helper for Exercise 12-12.7-8: under the integral-closure hypothesis, the class-level residue
evaluator vanishes at a chosen representative exactly when the corresponding owner value comes
from the fixed maximal ideal `M`. This is the precise zero criterion needed by the ambient
regular-fiber evaluator. -/
@[simp] theorem owner_pregular_residue_eval_of_isIntegralClosure_ofSubtype_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : {x : G // IsPRegular p x})
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    owner_pregular_residue_eval_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) M f
        (PRegularConjClass.ofSubtype p x) = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  rw [owner_pregular_residue_eval_of_isIntegralClosure_ofSubtype
    (A := A) (K := K) (G := G) (p := p) M f x]
  simpa using
    (residueFieldOfLiftedValue_eq_zero_iff (A := A) (K := K) (p := p) M
      ((f : G → K) x.1)
      (owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) f x))

end IntegralClosureResidueEvaluator

end RegularPrime

end

end Representation
