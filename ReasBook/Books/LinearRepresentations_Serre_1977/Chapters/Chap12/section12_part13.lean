import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_12_12_4_3 (from Chap12) -/
noncomputable section

open CategoryTheory
open scoped Representation

universe u v w x

namespace Representation

section GaloisPowerClasses

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGaloisPowerClasses : Fintype G := Fintype.ofFinite G
local instance instNeZeroExponentGaloisPowerClasses :
    NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite

/- Source/core/bridge triage:
- `source-facing`: `GaloisPowerClass ΓK` and `PRegularGaloisPowerClass ΓK p`, LinearRepresentations_Serre_1977's genuine
  `Γ_K`-classes and `p`-regular `Γ_K`-classes.
- `core/canonical`: `ConjClasses G`, `PRegularConjClass G p`, the orbit quotients
  `MulAction.orbitRel.Quotient ΓK _` coming from the descended `Γ_K`-power action, and the
  bundled owner `galoisPowerClassFunctionSubmodule R ΓK` of functions constant on those quotients.
- `bridge/view`: the factor-through predicate `IsConstantOnGaloisPowerClasses ΓK f`.
-/

private theorem galoisPowerExponentUnit_mul_modEq
    (t u : (ZMod (Monoid.exponent G))ˣ) :
    galoisPowerExponentUnit (t * u) ≡
      galoisPowerExponentUnit t * galoisPowerExponentUnit u [MOD Monoid.exponent G] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [galoisPowerExponentUnit, Nat.cast_mul]

namespace ConjClasses

instance : MulAction (ZMod (Monoid.exponent G))ˣ (ConjClasses G) where
  smul t c := ConjClasses.pow (galoisPowerExponentUnit t) c
  one_smul c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    have hmod :
        galoisPowerExponentUnit (1 : (ZMod (Monoid.exponent G))ˣ) ≡
          1 [MOD Monoid.exponent G] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [galoisPowerExponentUnit]
    calc
      g ^ galoisPowerExponentUnit (1 : (ZMod (Monoid.exponent G))ˣ) = g ^ 1 := by
        exact pow_eq_pow_of_modEq hmod (Monoid.pow_exponent_eq_one g)
      _ = g := pow_one g
  mul_smul t u c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    calc
      g ^ galoisPowerExponentUnit (t * u)
          = g ^ (galoisPowerExponentUnit u * galoisPowerExponentUnit t) := by
        rw [Nat.mul_comm]
        exact pow_eq_pow_of_modEq (galoisPowerExponentUnit_mul_modEq t u)
          (Monoid.pow_exponent_eq_one g)
      _ = (g ^ galoisPowerExponentUnit u) ^ galoisPowerExponentUnit t := by
        rw [pow_mul]

@[simp] theorem smul_mk (t : (ZMod (Monoid.exponent G))ˣ) (g : G) :
    t • ConjClasses.mk g = ConjClasses.mk (g ^ galoisPowerExponentUnit t) :=
  by
    change ConjClasses.pow (galoisPowerExponentUnit t) (ConjClasses.mk g) =
      ConjClasses.mk (g ^ galoisPowerExponentUnit t)
    exact ConjClasses.pow_mk (galoisPowerExponentUnit t) g

@[simp] theorem smul_mk_subgroup
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (t : ΓK) (g : G) :
    t • ConjClasses.mk g = ConjClasses.mk (g ^ t) := by
  change ((t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk g) =
    ConjClasses.mk (g ^ t)
  rw [pow_subgroup_eq_pow_nat]
  exact ConjClasses.smul_mk (t : (ZMod (Monoid.exponent G))ˣ) g

end ConjClasses

/-- LinearRepresentations_Serre_1977's `Γ_K`-classes, realized canonically as the orbit quotient of `ConjClasses G` under the
descended `Γ_K`-power action. -/
abbrev GaloisPowerClass (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :=
  MulAction.orbitRel.Quotient ΓK (ConjClasses G)

/-- The canonical map from group elements to LinearRepresentations_Serre_1977's `Γ_K`-classes. -/
def galoisPowerClassMk (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    G → GaloisPowerClass ΓK :=
  Quotient.mk'' ∘ ConjClasses.mk

/-- The canonical map `G → GaloisPowerClass ΓK` is surjective. -/
theorem galoisPowerClassMk_surjective
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    Function.Surjective (galoisPowerClassMk ΓK : G → GaloisPowerClass ΓK) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  exact ⟨g, rfl⟩

namespace PRegularConjClass

variable {p : ℕ}

omit [Finite G] in
private theorem isPRegular_pow_galoisPowerExponentUnit
    (t : (ZMod (Monoid.exponent G))ˣ) {x : G} (hx : IsPRegular p x) :
    IsPRegular p (x ^ galoisPowerExponentUnit t) := by
  have hcop :
      Nat.Coprime (orderOf x) (galoisPowerExponentUnit t) :=
    (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent x)
      (ZMod.val_coe_unit_coprime t)).symm
  simpa [IsPRegular, hcop.orderOf_pow] using hx

omit [Finite G] in
private theorem pow_mem
    (t : (ZMod (Monoid.exponent G))ˣ) (c : PRegularConjClass G p) :
    ∀ y ∈ (ConjClasses.pow (galoisPowerExponentUnit t) (c : ConjClasses G)).carrier,
      IsPRegular p y := by
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep (c : ConjClasses G)
  have hxreg : IsPRegular p x := c.2 x <| by
    simp [ConjClasses.mem_carrier_iff_mk_eq, hx]
  intro y hy
  have hy' : ConjClasses.mk y = ConjClasses.pow (galoisPowerExponentUnit t) (c : ConjClasses G) :=
    ConjClasses.mem_carrier_iff_mk_eq.mp hy
  rw [← hx, ConjClasses.pow_mk] at hy'
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hy').symm with ⟨a, rfl⟩
  simpa using isPRegular_conj p _ a
    (isPRegular_pow_galoisPowerExponentUnit t hxreg)

instance : MulAction (ZMod (Monoid.exponent G))ˣ (PRegularConjClass G p) where
  smul t c :=
    ⟨ConjClasses.pow (galoisPowerExponentUnit t) (c : ConjClasses G), pow_mem t c⟩
  one_smul c := by
    apply Subtype.ext
    change ((1 : (ZMod (Monoid.exponent G))ˣ) • (c : ConjClasses G)) = c
    simp
  mul_smul t u c := Subtype.ext <|
    mul_smul t u (c : ConjClasses G)

@[simp] theorem smul_ofSubtype
    (t : (ZMod (Monoid.exponent G))ˣ) (s : {x : G // IsPRegular p x}) :
    t • PRegularConjClass.ofSubtype p s =
      PRegularConjClass.ofSubtype p
        ⟨s.1 ^ galoisPowerExponentUnit t,
          isPRegular_pow_galoisPowerExponentUnit t s.2⟩ := by
  apply Subtype.ext
  change (t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk s.1 =
    ConjClasses.mk (s.1 ^ galoisPowerExponentUnit t)
  exact ConjClasses.smul_mk t s.1

@[simp] theorem smul_ofSubtype_subgroup
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (t : ΓK) (s : {x : G // IsPRegular p x}) :
    t • PRegularConjClass.ofSubtype p s =
      PRegularConjClass.ofSubtype p
        ⟨s.1 ^ t, isPRegular_pow_galoisPowerExponentUnit (t : _) s.2⟩ := by
  apply Subtype.ext
  change ((t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk s.1) =
    ConjClasses.mk (s.1 ^ t)
  exact ConjClasses.smul_mk_subgroup ΓK t s.1

end PRegularConjClass

/-- The `p`-regular LinearRepresentations_Serre_1977 `Γ_K`-classes, realized canonically as the orbit quotient of
`PRegularConjClass G p` under the descended `Γ_K`-power action. -/
abbrev PRegularGaloisPowerClass (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ) :=
  MulAction.orbitRel.Quotient ΓK (PRegularConjClass G p)

/-- The canonical map from `p`-regular elements to their `p`-regular `Γ_K`-class. -/
def pRegularGaloisPowerClassMk (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ) :
    {x : G // IsPRegular p x} → PRegularGaloisPowerClass ΓK p :=
  Quotient.mk'' ∘ PRegularConjClass.ofSubtype p

section GaloisPowerClassFunctions

variable {R : Type v}

/-- An `R`-valued function on `G` is constant on LinearRepresentations_Serre_1977's `Γ_K`-classes if it factors through the
canonical map `G → GaloisPowerClass ΓK`. -/
@[mk_iff]
class IsConstantOnGaloisPowerClasses
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough (galoisPowerClassMk ΓK)

/-- A `Γ_K`-class-constant function has equal values on equal `Γ_K`-classes. -/
theorem IsConstantOnGaloisPowerClasses.eq_of_mk_eq
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) {s t : G}
    (hst : galoisPowerClassMk ΓK s = galoisPowerClassMk ΓK t) :
    f s = f t :=
  hf.factorsThrough hst

/-- A `Γ_K`-class-constant function is, in particular, constant on conjugacy classes. -/
theorem IsConstantOnGaloisPowerClasses.isClassFunction
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) :
    _root_.IsClassFunction f := by
  refine ⟨?_⟩
  intro s t hst
  exact hf.eq_of_mk_eq <| by
    simpa [galoisPowerClassMk] using congrArg Quotient.mk'' hst

/-- A `Γ_K`-class-constant function descends canonically to `GaloisPowerClass ΓK`. -/
def IsConstantOnGaloisPowerClasses.lift
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) :
    GaloisPowerClass ΓK → R :=
  Quotient.lift
    (_root_.IsClassFunction.lift hf.isClassFunction)
    fun c d hcd ↦ by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective d
    simpa [galoisPowerClassMk] using hf.factorsThrough (Quotient.sound hcd)

@[simp] theorem IsConstantOnGaloisPowerClasses.lift_mk
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) (g : G) :
    hf.lift (galoisPowerClassMk ΓK g) = f g :=
  rfl

@[simp] theorem IsConstantOnGaloisPowerClasses.lift_comp_mk
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) :
    hf.lift ∘ galoisPowerClassMk ΓK = f := by
  ext g
  rfl

/-- A function on `GaloisPowerClass ΓK` pulls back to a `Γ_K`-class-constant function on `G`. -/
instance {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    (f : GaloisPowerClass ΓK → R) :
    IsConstantOnGaloisPowerClasses ΓK (f ∘ galoisPowerClassMk ΓK) := by
  refine ⟨?_⟩
  intro _ _ h
  exact congrArg f h

/-- A `Γ_K`-class-constant function is exactly a class function that factors through the quotient
map `G → GaloisPowerClass ΓK`; the class-function field is derived rather than primitive. -/
theorem isConstantOnGaloisPowerClasses_iff_isClassFunction_and_factorsThrough
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R} :
    IsConstantOnGaloisPowerClasses ΓK f ↔
      _root_.IsClassFunction f ∧ f.FactorsThrough (galoisPowerClassMk ΓK) := by
  constructor
  · intro hf
    exact ⟨hf.isClassFunction, hf.factorsThrough⟩
  · rintro ⟨_, hfactor⟩
    exact ⟨hfactor⟩

/-- A function on `G` is constant on LinearRepresentations_Serre_1977's `Γ_K`-classes exactly when it is pulled back from
`GaloisPowerClass ΓK`. -/
theorem isConstantOnGaloisPowerClasses_iff_exists
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R} :
    IsConstantOnGaloisPowerClasses ΓK f ↔
      ∃ φ : GaloisPowerClass ΓK → R, f = φ ∘ galoisPowerClassMk ΓK := by
  constructor
  · intro hf
    exact ⟨hf.lift, hf.lift_comp_mk.symm⟩
  · rintro ⟨φ, rfl⟩
    infer_instance

/-- For a class function, constancy on LinearRepresentations_Serre_1977's `Γ_K`-classes is equivalent to invariance under the
corresponding `Γ_K`-power maps. -/
theorem isConstantOnGaloisPowerClasses_iff_forall_pow_eq
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : _root_.IsClassFunction f) :
    IsConstantOnGaloisPowerClasses ΓK f ↔
      ∀ s (t : ΓK), f s = f (s ^ t) := by
  constructor
  · intro hconst s t
    have hst :
        galoisPowerClassMk ΓK (s ^ t) = galoisPowerClassMk ΓK s := by
      apply Quotient.sound
      change ConjClasses.mk (s ^ t) ∈ MulAction.orbit ΓK (ConjClasses.mk s)
      exact ⟨t, ConjClasses.smul_mk_subgroup ΓK t s⟩
    exact (hconst.eq_of_mk_eq hst).symm
  · intro hpow
    refine ⟨?_⟩
    intro s t hst
    have horbit : MulAction.orbitRel ΓK (ConjClasses G) (ConjClasses.mk s) (ConjClasses.mk t) :=
      Quotient.exact hst
    rw [MulAction.orbitRel_apply] at horbit
    rcases horbit with ⟨a, ha⟩
    have hmk : ConjClasses.mk (t ^ a) = ConjClasses.mk s := by
      simpa [galoisPowerClassMk] using ha
    calc
      f s = f (t ^ a) := by simpa using (hf.eq_of_mk_eq hmk).symm
      _ = f t := (hpow t a).symm

instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) [Zero R] :
    IsConstantOnGaloisPowerClasses ΓK (fun _ : G ↦ (0 : R)) := by
  refine ⟨?_⟩
  intro _ _ _
  rfl

instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) [Add R]
    {f g : G → R} [IsConstantOnGaloisPowerClasses ΓK f]
    [IsConstantOnGaloisPowerClasses ΓK g] :
    IsConstantOnGaloisPowerClasses ΓK (f + g) := by
  refine ⟨?_⟩
  intro s t hst
  change f s + g s = f t + g t
  simpa using congrArg₂ (· + ·)
    ((inferInstance : IsConstantOnGaloisPowerClasses ΓK f).factorsThrough hst)
    ((inferInstance : IsConstantOnGaloisPowerClasses ΓK g).factorsThrough hst)

instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) {S : Type w} [SMul S R] (a : S)
    {f : G → R} [IsConstantOnGaloisPowerClasses ΓK f] :
    IsConstantOnGaloisPowerClasses ΓK (a • f) := by
  refine ⟨?_⟩
  intro s t hst
  change a • f s = a • f t
  simpa using congrArg (a • ·)
    ((inferInstance : IsConstantOnGaloisPowerClasses ΓK f).factorsThrough hst)

end GaloisPowerClassFunctions

section GaloisPowerClassFunctionSubmodule

variable {R : Type v} [Semiring R]

/-- The `R`-submodule of `R`-valued functions on `G` that are constant on LinearRepresentations_Serre_1977's `Γ_K`-classes.
This is the Chapter `12` owner matching the Chapter `2` owner `classFunctionSubmodule`. -/
def galoisPowerClassFunctionSubmodule
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) : Submodule R (G → R) where
  carrier := {f | IsConstantOnGaloisPowerClasses ΓK f}
  zero_mem' := by
    simpa using (inferInstance : IsConstantOnGaloisPowerClasses ΓK (fun _ : G ↦ (0 : R)))
  add_mem' := by
    intro f g hf hg
    letI : IsConstantOnGaloisPowerClasses ΓK f := hf
    letI : IsConstantOnGaloisPowerClasses ΓK g := hg
    simpa using (inferInstance : IsConstantOnGaloisPowerClasses ΓK (f + g))
  smul_mem' := by
    intro a f hf
    letI : IsConstantOnGaloisPowerClasses ΓK f := hf
    simpa using (inferInstance : IsConstantOnGaloisPowerClasses ΓK (a • f))

/-- Membership in the bundled owner `galoisPowerClassFunctionSubmodule R ΓK` is exactly LinearRepresentations_Serre_1977's
`Γ_K`-class-constancy condition. -/
@[simp] theorem mem_galoisPowerClassFunctionSubmodule_iff
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (f : G → R) :
    f ∈ galoisPowerClassFunctionSubmodule ΓK ↔
      IsConstantOnGaloisPowerClasses ΓK f := by
  rfl

namespace galoisPowerClassFunctionSubmodule

/-- Elements of `galoisPowerClassFunctionSubmodule R ΓK` are canonically viewed as `R`-valued
functions on `G`. -/
instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    CoeFun (↥(galoisPowerClassFunctionSubmodule ΓK : Submodule R (G → R))) (fun _ ↦ G → R) where
  coe f := f.1

/-- The bundled owner of `Γ_K`-class-constant functions is canonically linearly equivalent to the
full function space on the quotient `GaloisPowerClass ΓK`. -/
def equivFun (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    (galoisPowerClassFunctionSubmodule ΓK : Submodule R (G → R)) ≃ₗ[R]
      GaloisPowerClass ΓK → R :=
  { toFun := fun φ ↦
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      hφ.lift
    invFun := fun φ ↦
      ⟨φ ∘ galoisPowerClassMk ΓK,
        (mem_galoisPowerClassFunctionSubmodule_iff ΓK (φ ∘ galoisPowerClassMk ΓK)).2
          inferInstance⟩
    left_inv := fun φ ↦ by
      ext g
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      exact hφ.lift_mk g
    right_inv := fun φ ↦ by
      ext c
      obtain ⟨g, rfl⟩ := Quotient.exists_rep c
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective g
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ ∘ galoisPowerClassMk ΓK) :=
        inferInstance
      change hφ.lift (galoisPowerClassMk ΓK x) = φ (galoisPowerClassMk ΓK x)
      exact hφ.lift_mk x
    map_add' := by
      intro φ ψ
      ext c
      obtain ⟨g, rfl⟩ := Quotient.exists_rep c
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective g
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      let hψ : IsConstantOnGaloisPowerClasses ΓK (ψ : G → R) := ψ.2
      let hφψ : IsConstantOnGaloisPowerClasses ΓK ((φ + ψ : galoisPowerClassFunctionSubmodule ΓK)
          : G → R) := (φ + ψ).2
      change hφψ.lift (galoisPowerClassMk ΓK x) =
        hφ.lift (galoisPowerClassMk ΓK x) + hψ.lift (galoisPowerClassMk ΓK x)
      rw [hφψ.lift_mk, hφ.lift_mk, hψ.lift_mk]
      rfl
    map_smul' := by
      intro a φ
      ext c
      obtain ⟨g, rfl⟩ := Quotient.exists_rep c
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective g
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      let haφ : IsConstantOnGaloisPowerClasses ΓK ((a • φ : galoisPowerClassFunctionSubmodule ΓK)
          : G → R) := (a • φ).2
      change haφ.lift (galoisPowerClassMk ΓK x) =
        a • hφ.lift (galoisPowerClassMk ΓK x)
      rw [haφ.lift_mk, hφ.lift_mk]
      rfl }

end galoisPowerClassFunctionSubmodule

end GaloisPowerClassFunctionSubmodule

end GaloisPowerClasses

section RankOfRepresentationRing

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type u} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable {ι : Type x}

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-
Corollary `12-12.4-2`, rewritten through the canonical quotient owner
`GaloisPowerClass (Γ[K](G))`: a `K`-valued function in `A ⊗ R_K(G)` is automatically a class
function, since this scalar extension is spanned by ordinary characters.
-/
omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
theorem isClassFunction_of_mem_characterRingOverFieldScalarExtension
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    _root_.IsClassFunction f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact Representation.isClassFunction_of_mem_characterRingOverField ψ hψ
  | zero =>
      simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      simpa using (inferInstance : _root_.IsClassFunction (f + g))
  | smul a f _ hf =>
      letI : _root_.IsClassFunction f := hf
      simpa using (inferInstance : _root_.IsClassFunction (a • f))

/-- Corollary `12-12.4-2`, rewritten through the canonical quotient owner
`GaloisPowerClass (Γ[K](G))`: a `K`-valued function belongs to `K ⊗ R_K(G)` exactly when
it is constant on LinearRepresentations_Serre_1977's `Γ_K`-classes. -/
theorem classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
    (f : G → K) :
    f ∈ K⊗R[K](G) ↔ IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  constructor
  · intro hf
    let hfClass : _root_.IsClassFunction f :=
      isClassFunction_of_mem_characterRingOverFieldScalarExtension K hf
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hfClass⟩
    exact
      (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hfClass).2 <|
        (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
          G K φ).1 hf
  · intro hf
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hf.isClassFunction⟩
    exact
      (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        G K φ).2 <|
        (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hf.isClassFunction).1 hf

/-- Helper for Corollary 12-12.4-3: this is the canonical owner submodule of `Γ[K](G)`-constant
`K`-valued functions, written with the explicit pointwise `K`-module structure on `G → K`. -/
abbrev galoisPowerClassFunctionSubmoduleOverField :
    @Submodule K (G → K) _ _ (Pi.module G (fun _ : G ↦ K) K) :=
  galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G))

/-- LinearRepresentations_Serre_1977's scalar extension `K ⊗ R_K(G)` is exactly the owner submodule of `K`-valued
functions on `G` that are constant on `Γ[K](G)`-power classes. This is Corollary 12.4.2 in
LinearRepresentations_Serre_1977's notation; the earlier rationalized owner `ℚ ⊗ R_K(G)` is too small for this statement. -/
theorem characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule :
    (K⊗R[K](G) : Submodule K (G → K)) =
      galoisPowerClassFunctionSubmoduleOverField (G := G) (L := L) K := by
  ext f
  rw [mem_galoisPowerClassFunctionSubmodule_iff]
  exact
    classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
      K f

/-- Corollary 12-12.4-3 bridge: LinearRepresentations_Serre_1977's scalar extension `K ⊗ R_K(G)` is canonically the full
function space on the quotient `GaloisPowerClass (Γ[K](G))`. -/
def characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions
    :
    K⊗R[K](G) ≃ₗ[K] GaloisPowerClass (Γ[K](G)) → K :=
  (LinearEquiv.ofEq _ _
      (characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule K)).trans
    (galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)))

/-- Helper for Corollary 12-12.4-3: pulling back the quotient-function equivalence along
`galoisPowerClassMk` recovers the original function in `K ⊗ R_K(G)`. -/
@[simp] theorem
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions_comp_galoisPowerClassMk
    (f : K ⊗R[K](G)) :
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K f ∘
        galoisPowerClassMk (Γ[K](G)) =
      f := by
  ext g
  let φ :
      galoisPowerClassFunctionSubmoduleOverField K :=
    (LinearEquiv.ofEq _ _
      (characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule K)) f
  let φK : galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G)) := φ
  let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G)) ((φK : G → K)) := φK.2
  -- Unfold the transport across the restricted owner equality and then evaluate the quotient lift.
  have hdef :
      (characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K) f =
        galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ := by
    rfl
  have hφ_eq : (φK : G → K) = (f : G → K) := by
    dsimp [φ, φK]
  have hpull :
      ((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ) ∘
        galoisPowerClassMk (Γ[K](G))) = (φK : G → K) := by
    exact congrArg
      (fun ψ : galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G)) ↦ (ψ : G → K))
      ((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G))).left_inv φ)
  rw [hdef]
  have hleft :
      ↑(((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ) ∘
          galoisPowerClassMk (Γ[K](G))) g) = ↑(φK g) := by
    simpa [Function.comp] using congrArg ((↑) : K → L) (congrFun hpull g)
  have hright : ↑(φK g) = ↑((f : G → K) g) := by
    simpa using congrArg ((↑) : K → L) (congrFun hφ_eq g)
  simpa using hleft.trans hright

/-- A `K`-valued character in `R_K(G)` is constant on LinearRepresentations_Serre_1977's `Γ_K`-classes. -/
theorem isConstantOnGaloisPowerClasses_of_mem_characterRingOverField
    {f : G → K} (hf : f ∈ R[K](G)) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  exact
      (classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
      K f).1
      (mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField (A := K) hf)

/-- Membership in LinearRepresentations_Serre_1977's scalar extension `A ⊗ R_K(G)` implies constancy on the genuine
arithmetic `Γ_K`-classes. This is the owner-level Chapter `12` upgrade of the `R_K(G)` statement
above, and the canonical source for later reductions modulo prime ideals. -/
theorem isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact isConstantOnGaloisPowerClasses_of_mem_characterRingOverField K (by simpa using hψ)
  | zero =>
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) f := hf
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) g := hg
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (f + g))
  | smul a f _ hf =>
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) f := hf
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (a • f))

-- Proof sketch: Corollary `12-12.4-2` identifies the image of `K ⊗ R_K(G)` with the
-- bundled owner `galoisPowerClassFunctionSubmodule K (Γ[K](G))`, hence with the full function
-- space `GaloisPowerClass (Γ[K](G)) → K` via
-- `characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions`. Transport each
-- irreducible character through that quotient equivalence, then package the resulting family as
-- the basis promised by LinearRepresentations_Serre_1977's corollary.
/-- The quotient function on `GaloisPowerClass (Γ[K](G))` corresponding to the irreducible
character of `π i`. -/
def irreducibleCharacterOnGaloisPowerClasses
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    GaloisPowerClass (Γ[K](G)) → K :=
  letI : Simple (π i) := hπ_complete.isSimple i
  characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K
    ⟨(π i).character,
      mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
        (A := K) (FDRep.character_mem_characterRingOverField K (π i))⟩

@[simp] theorem irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i ∘
        galoisPowerClassMk (Γ[K](G)) =
      (π i).character := by
  letI := hπ_complete.isSimple i
  -- Route correction: the quotient character is obtained through a scalar-restricted transport, so
  -- the pullback identity is proved by unfolding that transport rather than by definitional `rfl`.
  simpa [irreducibleCharacterOnGaloisPowerClasses] using
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions_comp_galoisPowerClassMk
      K
      ⟨(π i).character,
        mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
          (A := K) (FDRep.character_mem_characterRingOverField K (π i))⟩

/- Helper for Corollary 12-12.4-3: every element of `R[K](G)` already lies in the ambient
`K`-span of the ordinary irreducible characters of a complete pairwise nonisomorphic family. -/
omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
lemma mem_span_irreducible_characters_of_mem_characterRingOverField
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {χ : G → K} (hχ : χ ∈ R[K](G)) :
    χ ∈ Submodule.span K (Set.range fun i ↦ (π i).character) := by
  classical
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr ⟨χ, hχ⟩
  -- Rewrite the basis expansion in `R[K](G)` inside the ambient function space `G → K`.
  have hχ_eq :
      Finset.sum c.support (fun i ↦ c i • (π i).character) = χ := by
    have hrepr :
        (Finsupp.linearCombination ℤ (fun i ↦ b i)) c = ⟨χ, hχ⟩ := by
      rw [show c = b.repr ⟨χ, hχ⟩ by rfl]
      exact b.linearCombination_repr ⟨χ, hχ⟩
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, b,
      irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg ((↑) : R[K](G) → G → K) hrepr
  -- A finite linear combination of the generators lies in their span.
  rw [← hχ_eq]
  exact
    Submodule.sum_mem (Submodule.span K (Set.range fun i ↦ (π i).character)) fun i _ ↦
      by
        simpa [zsmul_eq_mul] using
          (Submodule.smul_mem (Submodule.span K (Set.range fun j ↦ (π j).character))
            (c i : K)
            (Submodule.subset_span ⟨i, rfl⟩))

/-- Helper for Corollary 12-12.4-3: every function in the ambient span of the ordinary
irreducible characters is the pullback of a quotient function in the corresponding quotient span.
-/
lemma exists_mem_span_irreducibleCharacterOnGaloisPowerClasses_of_mem_span
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {f : G → K}
    (hf : f ∈ Submodule.span K (Set.range fun i ↦ (π i).character)) :
    ∃ φ ∈ Submodule.span K
        (Set.range (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete)),
      φ ∘ galoisPowerClassMk (Γ[K](G)) = f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      rcases hψ with ⟨i, rfl⟩
      -- Each ordinary irreducible character is the pullback of its quotient avatar.
      refine ⟨irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i,
        Submodule.subset_span ⟨i, rfl⟩, ?_⟩
      exact irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk K π hπ_complete i
  | zero =>
      -- The zero function descends trivially.
      exact ⟨0, Submodule.zero_mem _, by ext g; rfl⟩
  | add f g _ _ hf hg =>
      rcases hf with ⟨φf, hφf, rfl⟩
      rcases hg with ⟨φg, hφg, rfl⟩
      -- Descent is stable under addition.
      refine ⟨φf + φg, Submodule.add_mem _ hφf hφg, ?_⟩
      ext g
      rfl
  | smul a f _ hf =>
      rcases hf with ⟨φ, hφ, rfl⟩
      -- Descent is stable under scalar multiplication.
      refine ⟨a • φ, Submodule.smul_mem _ a hφ, ?_⟩
      ext g
      rfl

section PairingHelpers

variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L]
variable {ι : Type x}
variable (K : IntermediateField ℚ L)

/-- Helper for Corollary 12-12.4-3: the normalized pairing is additive on finite `K`-linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_smul_left
    [Invertible (Nat.card G : K)]
    (s : Finset ι) (g : ι → K) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, g j • χ j, ψ⟫ = ∑ j ∈ s, g j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [groupFunctionPairingOverField]
  | insert a s ha ih =>
      -- Expand the inserted term, then use additivity and homogeneity of the pairing.
      simp [Finset.sum_insert, ha, ih, groupFunctionPairing_add_left,
        groupFunctionPairing_smul_left]

/-- Helper for Corollary 12-12.4-3: the self-pairing of the character of a simple
finite-dimensional representation is nonzero, because the identity intertwiner survives in its
endomorphism space. -/
private theorem groupFunctionPairingOverField_character_self_ne_zero
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    rw [← Fintype.card_eq_nat_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  letI : FiniteDimensional K (Representation.IntertwiningMap V.ρ V.ρ) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have hnontriv : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
    refine ⟨0, e (𝟙 V), ?_⟩
    intro h
    apply CategoryTheory.id_nonzero V
    exact e.injective h.symm
  letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := hnontriv
  have hpair :
      ⟪V.character, V.character⟫ =
        Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) :=
    Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K V.ρ V.ρ
  rw [hpair]
  exact_mod_cast Module.finrank_pos.ne'

end PairingHelpers

/-- Helper for Corollary 12-12.4-3: the quotient irreducible characters remain linearly
independent after passing to functions on `GaloisPowerClass (Γ[K](G))`. -/
lemma linearIndependent_irreducibleCharacterOnGaloisPowerClasses
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    LinearIndependent K (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) := by
  classical
  let pullback :
      (GaloisPowerClass (Γ[K](G)) → K) →ₗ[K] G → K :=
    { toFun := fun φ ↦ φ ∘ galoisPowerClassMk (Γ[K](G))
      map_add' := by intro φ ψ; rfl
      map_smul' := by intro a φ; rfl }
  have hchars : LinearIndependent K (fun i ↦ (π i).character) := by
    letI : Fintype G := Fintype.ofFinite G
    have hcard_ne : (Nat.card G : K) ≠ 0 := by
      rw [← Fintype.card_eq_nat_card]
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
    have horth :
        Pairwise fun i j ↦
          ⟪(π i).character, (π j).character⟫ = (0 : K) :=
      Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
        K π hπ_complete.isSimple hπ_pairwise
    rw [linearIndependent_iff']
    intro s g hg i hi
    -- Pair the relation with the `i`-th character to isolate its coefficient.
    have hpair0 :=
      congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hg
    have hpair :
        ⟪∑ j ∈ s, g j • (π j).character, (π i).character⟫ = (0 : K) := by
      simpa [Representation.groupFunctionPairingOverField] using hpair0
    rw [Representation.groupFunctionPairing_sum_smul_left
        K s g (fun j ↦ (π j).character) ((π i).character)]
      at hpair
    -- Route correction: the diagonal term is handled via the simple-object endomorphism-space
    -- computation, avoiding the previous timeout-prone explicit self-intertwining witness.
    rw [Finset.sum_eq_single i] at hpair
    · exact (mul_eq_zero.mp hpair).resolve_right <|
        Representation.groupFunctionPairingOverField_character_self_ne_zero K (π i)
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hnot_mem
      exact (hnot_mem hi).elim
  -- Pulling back along the surjective quotient map identifies the quotient characters with the
  -- ordinary irreducible characters.
  have hpullback :
      LinearIndependent K
        (pullback ∘ irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) := by
    have hfamily :
        (pullback ∘ irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) =
          fun i ↦ (π i).character := by
      funext i
      ext g
      -- Evaluate the pullback on each quotient character and rewrite with the explicit descent law.
      simpa [pullback] using
        congrFun
          (irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk K π hπ_complete i) g
    rw [hfamily]
    exact hchars
  exact LinearIndependent.of_comp pullback hpullback

/-- Helper for Corollary 12-12.4-3: the transported irreducible characters span all functions on
`GaloisPowerClass (Γ[K](G))`. -/
lemma span_irreducibleCharacterOnGaloisPowerClasses_eq_top
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span K
        (Set.range (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro φ hφ
    let f : G → K := φ ∘ galoisPowerClassMk (Γ[K](G))
    have hf_scalar : f ∈ K⊗R[K](G) := by
      -- Pulling back a quotient function produces a `Γ[K](G)`-constant function, so Corollary
      -- `12-12.4-2` places it in `K ⊗ R[K](G)`.
      exact
        (classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
          K f).2 inferInstance
    have hscalar_to_span :
        ∀ h : G → K, h ∈ K⊗R[K](G) →
          h ∈ Submodule.span K (Set.range fun i ↦ (π i).character) := by
      intro h hh
      -- First span in the ambient function space `G → K`; the generator case is the previous
      -- `R[K](G)` spanning lemma, and the scalar extension is now the source-correct `K`-span.
      induction hh using Submodule.span_induction with
      | mem χ hχ =>
          exact
            mem_span_irreducible_characters_of_mem_characterRingOverField
              K π hπ_pairwise hπ_complete (by simpa using hχ)
      | zero =>
          exact Submodule.zero_mem _
      | add f g _ _ hf hg =>
          exact Submodule.add_mem _ hf hg
      | smul a h _ hh =>
          exact Submodule.smul_mem _ a hh
    have hf_span :
        f ∈ Submodule.span K (Set.range fun i ↦ (π i).character) :=
      hscalar_to_span f hf_scalar
    rcases
        exists_mem_span_irreducibleCharacterOnGaloisPowerClasses_of_mem_span
          K π hπ_complete hf_span with
      ⟨ψ, hψ, hψ_eq⟩
    have hpullback_eq : ψ ∘ galoisPowerClassMk (Γ[K](G)) = φ ∘ galoisPowerClassMk (Γ[K](G)) := by
      simpa [f] using hψ_eq
    have hψφ : ψ = φ := by
      ext q
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (Γ[K](G)) q
      simpa using congrFun hpullback_eq g
    simpa [hψφ] using hψ

/-- Corollary 12-12.4-3: the characters of the distinct irreducible `K`-representations of `G`
form a basis of the `K`-valued functions that are constant on LinearRepresentations_Serre_1977's `Γ_K`-classes of `G`. In
the canonical quotient-owner presentation used in this file, this is realized as a basis of the
function space on `GaloisPowerClass (Γ[K](G))`. -/
def irreducible_characters_basis_of_galoisPowerClassFunctions
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι K (GaloisPowerClass (Γ[K](G)) → K) :=
  Module.Basis.mk
    (linearIndependent_irreducibleCharacterOnGaloisPowerClasses
      K π hπ_pairwise hπ_complete)
    ((span_irreducibleCharacterOnGaloisPowerClasses_eq_top
      K π hπ_pairwise hπ_complete).ge)

@[simp] theorem irreducible_characters_basis_of_galoisPowerClassFunctions_apply
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete i =
      irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i := by
  exact Module.Basis.mk_apply _ _ _

@[simp] theorem irreducible_characters_basis_of_galoisPowerClassFunctions_comp_galoisPowerClassMk
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete i ∘
        galoisPowerClassMk (Γ[K](G)) =
      (π i).character := by
  rw [irreducible_characters_basis_of_galoisPowerClassFunctions_apply]
  exact
    irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk
      K π hπ_complete i

/-- The index set of a complete pairwise nonisomorphic irreducible family has the same
cardinality as the quotient `GaloisPowerClass (Γ[K](G))`. -/
theorem nat_card_irreducible_family_eq_nat_card_galoisPowerClass
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card ι = Nat.card (GaloisPowerClass (Γ[K](G))) := by
  letI : Finite (GaloisPowerClass (Γ[K](G))) :=
    Finite.of_surjective
      (galoisPowerClassMk (Γ[K](G)))
      (galoisPowerClassMk_surjective (Γ[K](G)))
  letI : Fintype (GaloisPowerClass (Γ[K](G))) := Fintype.ofFinite _
  let b : Module.Basis ι K (GaloisPowerClass (Γ[K](G)) → K) :=
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  calc
    Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ = Module.finrank K (GaloisPowerClass (Γ[K](G)) → K) :=
      (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (GaloisPowerClass (Γ[K](G))) := Module.finrank_fintype_fun_eq_card K
    _ = Nat.card (GaloisPowerClass (Γ[K](G))) := Nat.card_eq_fintype_card.symm

end RankOfRepresentationRing

end Representation

/-! ### Remark_12_12_4_4 (from Chap12) -/
open scoped Representation

universe u v w

namespace Representation

private theorem span_eq_overlineCharacterRing_of_isFiniteRelIndex
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G]
    (A : Type w) [Field A] [CharZero A] [Algebra A K] :
    Submodule.span A (R[K](G) : Set (G → K)) =
      Submodule.span A (R̄[K](G) : Set (G → K)) := by
  let RK : Submodule ℤ (G → K) := (R[K](G)).toSubmodule
  let RbarK : Submodule ℤ (G → K) := (R̄[K](G)).toSubmodule
  have hle : RK ≤ RbarK := by
    simpa [RK, RbarK] using
      (characterRingOverField_le_overlineCharacterRing K G :
        (R[K](G)).toSubmodule ≤ (R̄[K](G)).toSubmodule)
  have hfin : RK.toAddSubgroup.IsFiniteRelIndex RbarK.toAddSubgroup := by
    simpa [RK, RbarK] using
      (characterRingOverField_isFiniteRelIndex_overlineCharacterRing K :
        (R[K](G)).toSubmodule.toAddSubgroup.IsFiniteRelIndex
          (R̄[K](G)).toSubmodule.toAddSubgroup)
  letI := hfin
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    intro χ hχ
    have hχRK : χ ∈ RK := by
      simpa [RK] using hχ
    exact Submodule.subset_span <| by
      simpa [RbarK] using hle hχRK
  · refine Submodule.span_le.2 fun χ hχ ↦ ?_
    let n := RK.toAddSubgroup.relIndex RbarK.toAddSubgroup
    have hχRbarK : χ ∈ RbarK.toAddSubgroup := by
      simpa [RbarK] using hχ
    have hnsmul_mem : n • χ ∈ (R[K](G) : Set (G → K)) := by
      simpa [RK, n] using RK.toAddSubgroup.nsmul_relIndex_mem hχRbarK
    have hn_ne_zero : (n : A) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr <| by
        simpa [n] using (AddSubgroup.relIndex_ne_zero :
          RK.toAddSubgroup.relIndex RbarK.toAddSubgroup ≠ 0)
    have hχ :
        χ = ((n : A)⁻¹) • (n • χ) := by
      rw [← Nat.cast_smul_eq_nsmul A, ← mul_smul, inv_mul_cancel₀ hn_ne_zero, one_smul]
    rw [hχ]
    exact (Submodule.span A (R[K](G) : Set (G → K))).smul_mem _ <|
      Submodule.subset_span hnsmul_mem

/-- The `ℚ`-scalar-extension form of Remark 12-12.4-4: the chapter owner `ℚ ⊗ R_K(G)` is exactly
the `ℚ`-span of `\overline{R}_K(G)` inside `G → K`. This is the owner-level equality underlying
the replacement of `R_K(G)` by `\overline{R}_K(G)` in Corollary `12-12.4-2`. -/
theorem characterRingOverField_rationalScalarExtension_eq_overlineCharacterRing_span
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G] :
    (ℚ⊗R[K](G) : Submodule ℚ (G → K)) =
      Submodule.span ℚ (R̄[K](G) : Set (G → K)) := by
  simpa [characterRingOverFieldScalarExtension] using
    span_eq_overlineCharacterRing_of_isFiniteRelIndex K G ℚ

/-- Remark 12-12.4-4: after extending scalars from `ℤ` to `K`, the canonical `K`-span generated
by `R_K(G)` agrees with the `K`-span of `\overline{R}_K(G)` inside `G → K`. -/
theorem characterRingOverField_scalarExtension_eq_overlineCharacterRing_span
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G] :
    K ⊗R[K](G) = Submodule.span K (R̄[K](G) : Set (G → K)) := by
  simpa [characterRingOverFieldAlgebraScalarExtension] using
    span_eq_overlineCharacterRing_of_isFiniteRelIndex K G K

end Representation
