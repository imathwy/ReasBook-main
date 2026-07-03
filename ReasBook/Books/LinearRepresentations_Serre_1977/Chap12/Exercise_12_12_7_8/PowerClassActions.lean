import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.GroupTheory.ConjClassesPower
import Serre.Chap11.Proposition_11_11_4_1

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat

section LocalGaloisPowerClasses

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278PowerClassActionsGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278PowerClassActionsGroup
local instance : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite

/-- Helper for Exercise 12-12.7-8: the natural-number representative of an exponent unit. -/
private abbrev galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) : ℕ :=
  (t : ZMod (Monoid.exponent G)).val

/-- Helper for Exercise 12-12.7-8: Serre's `Γ_K`-power action uses the chosen exponent-unit
representative. -/
private instance gammaSubgroupPow
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} : Pow G ΓK where
  pow s t := s ^ galoisPowerExponentUnit (G := G) (t : (ZMod (Monoid.exponent G))ˣ)

/-- Helper for Exercise 12-12.7-8: the subgroup power action unfolds to the natural-number
exponent. -/
private theorem pow_subgroup_eq_pow_nat
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} (s : G) (t : ΓK) :
    (s ^ t : G) = s ^ galoisPowerExponentUnit (G := G) (t : (ZMod (Monoid.exponent G))ˣ) := rfl

/-- Helper for Exercise 12-12.7-8: exponent-unit representatives multiply modulo the group
exponent. -/
private theorem galoisPowerExponentUnit_mul_modEq
    (t u : (ZMod (Monoid.exponent G))ˣ) :
    galoisPowerExponentUnit (G := G) (t * u) ≡
      galoisPowerExponentUnit (G := G) t * galoisPowerExponentUnit (G := G) u
        [MOD Monoid.exponent G] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [galoisPowerExponentUnit, Nat.cast_mul]

/-- Helper for Exercise 12-12.7-8: the theorem-local owner of Serre's subgroup
`Γ_K ⊆ (ℤ / exp(G)ℤ)ˣ` attached to `K ⊆ L`. It is deliberately named away from the chapter-level
API to avoid import collisions with earlier owner modules while the local helper tree is active.
-/
abbrev exerciseGammaSubgroup (K : IntermediateField ℚ L) :
    Subgroup (ZMod (Monoid.exponent G))ˣ :=
  (galEquivZMod (Monoid.exponent G) L).mapSubgroup K.fixingSubgroup

namespace ConjClasses

/-- Helper for Exercise 12-12.7-8: conjugacy classes carry the exponent-unit power action. -/
private instance : MulAction (ZMod (Monoid.exponent G))ˣ (ConjClasses G) where
  smul t c := ConjClasses.pow (galoisPowerExponentUnit (G := G) t) c
  one_smul c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    have hmod :
        galoisPowerExponentUnit (G := G) (1 : (ZMod (Monoid.exponent G))ˣ) ≡
          1 [MOD Monoid.exponent G] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [galoisPowerExponentUnit]
    calc
      g ^ galoisPowerExponentUnit (G := G) (1 : (ZMod (Monoid.exponent G))ˣ) = g ^ 1 := by
        exact pow_eq_pow_of_modEq hmod (Monoid.pow_exponent_eq_one g)
      _ = g := pow_one g
  mul_smul t u c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    calc
      g ^ galoisPowerExponentUnit (G := G) (t * u)
          = g ^
              (galoisPowerExponentUnit (G := G) u *
                galoisPowerExponentUnit (G := G) t) := by
            rw [Nat.mul_comm]
            exact pow_eq_pow_of_modEq
              (galoisPowerExponentUnit_mul_modEq (G := G) t u)
              (Monoid.pow_exponent_eq_one g)
      _ = (g ^ galoisPowerExponentUnit (G := G) u) ^
            galoisPowerExponentUnit (G := G) t := by
            rw [pow_mul]

/-- Helper for Exercise 12-12.7-8: the unit action on `ConjClasses G` sends `g` to the class of
its power. -/
@[simp] private theorem smul_mk (t : (ZMod (Monoid.exponent G))ˣ) (g : G) :
    t • ConjClasses.mk g =
      ConjClasses.mk (g ^ galoisPowerExponentUnit (G := G) t) := by
  change ConjClasses.pow (galoisPowerExponentUnit (G := G) t) (ConjClasses.mk g) =
    ConjClasses.mk (g ^ galoisPowerExponentUnit (G := G) t)
  exact ConjClasses.pow_mk (galoisPowerExponentUnit (G := G) t) g

/-- Helper for Exercise 12-12.7-8: the subgroup action uses the same power map on
representatives. -/
@[simp] private theorem smul_mk_subgroup
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (t : ΓK) (g : G) :
    t • ConjClasses.mk g = ConjClasses.mk (g ^ t) := by
  change ((t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk g) =
    ConjClasses.mk (g ^ t)
  rw [pow_subgroup_eq_pow_nat (G := G)]
  exact ConjClasses.smul_mk (G := G) (t : (ZMod (Monoid.exponent G))ˣ) g

end ConjClasses

/-- Serre's `Γ_K`-classes, realized canonically as the orbit quotient of `ConjClasses G`. -/
abbrev GaloisPowerClass (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :=
  MulAction.orbitRel.Quotient ΓK (ConjClasses G)

/-- The canonical map from `G` to Serre's `Γ_K`-classes. -/
def galoisPowerClassMk (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    G → GaloisPowerClass ΓK :=
  Quotient.mk'' ∘ ConjClasses.mk

/-- The canonical map `G → GaloisPowerClass ΓK` is surjective. -/
theorem galoisPowerClassMk_surjective
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    Function.Surjective (galoisPowerClassMk (G := G) ΓK : G → GaloisPowerClass ΓK) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  exact ⟨g, rfl⟩

section GaloisPowerClassFunctions

variable {R : Type w}

/-- Helper for Exercise 12-12.7-8: an `R`-valued function is constant on Serre's `Γ_K`-classes
when it factors through the quotient map `galoisPowerClassMk`. This is the minimal quotient API
used by the fiber-first proof route. -/
@[mk_iff]
class IsConstantOnGaloisPowerClasses
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough (galoisPowerClassMk ΓK)

/-- Helper for Exercise 12-12.7-8: equality of `Γ_K`-classes forces equality of values for a
quotient-constant function. -/
theorem IsConstantOnGaloisPowerClasses.eq_of_mk_eq
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) {s t : G}
    (hst : galoisPowerClassMk ΓK s = galoisPowerClassMk ΓK t) :
    f s = f t :=
  hf.factorsThrough hst

/-- Helper for Exercise 12-12.7-8: a `Γ_K`-class-constant function is automatically a class
function. -/
theorem IsConstantOnGaloisPowerClasses.isClassFunction
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) :
    _root_.IsClassFunction f := by
  refine ⟨?_⟩
  intro s t hst
  exact hf.eq_of_mk_eq <| by
    simpa [galoisPowerClassMk] using congrArg Quotient.mk'' hst

/-- Helper for Exercise 12-12.7-8: a `Γ_K`-class-constant function descends to the quotient
`GaloisPowerClass ΓK`. -/
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

/-- Helper for Exercise 12-12.7-8: pulling back a quotient function gives a `Γ_K`-class-constant
function on `G`. -/
instance {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    (f : GaloisPowerClass ΓK → R) :
    IsConstantOnGaloisPowerClasses ΓK (f ∘ galoisPowerClassMk ΓK) := by
  refine ⟨?_⟩
  intro _ _ h
  exact congrArg f h

/-- Helper for Exercise 12-12.7-8: for a class function, Serre's quotient-constancy is exactly
invariance under the `Γ_K`-power maps. -/
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
      exact ⟨t, (ConjClasses.smul_mk_subgroup (G := G) ΓK t s).symm⟩
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

instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) {S : Type*} [SMul S R] (a : S)
    {f : G → R} [IsConstantOnGaloisPowerClasses ΓK f] :
    IsConstantOnGaloisPowerClasses ΓK (a • f) := by
  refine ⟨?_⟩
  intro s t hst
  change a • f s = a • f t
  simpa using congrArg (a • ·)
    ((inferInstance : IsConstantOnGaloisPowerClasses ΓK f).factorsThrough hst)

variable [Semiring R]

/-- Helper for Exercise 12-12.7-8: the bundled owner of `Γ_K`-class-constant functions. -/
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

/-- Membership in the bundled owner `galoisPowerClassFunctionSubmodule ΓK` is exactly Serre's
`Γ_K`-class-constancy condition. -/
@[simp] theorem mem_galoisPowerClassFunctionSubmodule_iff
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (f : G → R) :
    f ∈ (galoisPowerClassFunctionSubmodule (ΓK := ΓK) : Submodule R (G → R)) ↔
      IsConstantOnGaloisPowerClasses ΓK f := by
  rfl

namespace galoisPowerClassFunctionSubmodule

/-- Elements of `galoisPowerClassFunctionSubmodule ΓK` are canonically viewed as `R`-valued
functions on `G`. -/
instance (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    CoeFun (↥(galoisPowerClassFunctionSubmodule (ΓK := ΓK) : Submodule R (G → R)))
      (fun _ ↦ G → R) where
  coe f := f.1

/-- The bundled owner of `Γ_K`-class-constant functions is canonically linearly equivalent to the
full function space on `GaloisPowerClass ΓK`. -/
def equivFun (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    (galoisPowerClassFunctionSubmodule (ΓK := ΓK) : Submodule R (G → R)) ≃ₗ[R]
      GaloisPowerClass ΓK → R :=
  { toFun := fun φ ↦
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      hφ.lift
    invFun := fun φ ↦
      ⟨φ ∘ galoisPowerClassMk ΓK,
        (mem_galoisPowerClassFunctionSubmodule_iff (G := G) (R := R) ΓK
          (φ ∘ galoisPowerClassMk ΓK)).2 inferInstance⟩
    left_inv := fun φ ↦ by
      ext g
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      exact hφ.lift_mk g
    right_inv := fun φ ↦ by
      ext c
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ ∘ galoisPowerClassMk ΓK) :=
        inferInstance
      exact hφ.lift_mk g
    map_add' := by
      intro φ ψ
      ext c
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      let hψ : IsConstantOnGaloisPowerClasses ΓK (ψ : G → R) := ψ.2
      let hφψ :
          IsConstantOnGaloisPowerClasses ΓK
            ((φ + ψ :
              galoisPowerClassFunctionSubmodule (ΓK := ΓK)) : G → R) := (φ + ψ).2
      change hφψ.lift (galoisPowerClassMk ΓK g) =
        hφ.lift (galoisPowerClassMk ΓK g) + hψ.lift (galoisPowerClassMk ΓK g)
      rw [hφψ.lift_mk, hφ.lift_mk, hψ.lift_mk]
      rfl
    map_smul' := by
      intro a φ
      ext c
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
      let hφ : IsConstantOnGaloisPowerClasses ΓK (φ : G → R) := φ.2
      let haφ :
          IsConstantOnGaloisPowerClasses ΓK
            ((a • φ :
              galoisPowerClassFunctionSubmodule (ΓK := ΓK)) : G → R) := (a • φ).2
      change haφ.lift (galoisPowerClassMk ΓK g) =
        a • hφ.lift (galoisPowerClassMk ΓK g)
      rw [haφ.lift_mk, hφ.lift_mk]
      rfl }

end galoisPowerClassFunctionSubmodule

end GaloisPowerClassFunctions

namespace PRegularConjClass

variable {p : ℕ}

/-- Helper for Exercise 12-12.7-8: exponent-unit powers preserve `p`-regularity. -/
private theorem isPRegular_pow_galoisPowerExponentUnit
    (t : (ZMod (Monoid.exponent G))ˣ) {x : G} (hx : IsPRegular p x) :
    IsPRegular p (x ^ galoisPowerExponentUnit (G := G) t) := by
  have hcop :
      Nat.Coprime (orderOf x) (galoisPowerExponentUnit (G := G) t) :=
    (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent x)
      (ZMod.val_coe_unit_coprime t)).symm
  simpa [IsPRegular, hcop.orderOf_pow] using hx

/-- Helper for Exercise 12-12.7-8: powering a `p`-regular conjugacy class by an exponent unit
stays inside the owner of `p`-regular conjugacy classes. -/
private theorem pow_mem
    (t : (ZMod (Monoid.exponent G))ˣ) (c : PRegularConjClass G p) :
    ∀ y ∈ (ConjClasses.pow (galoisPowerExponentUnit (G := G) t) (c : ConjClasses G)).carrier,
      IsPRegular p y := by
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep (c : ConjClasses G)
  have hxreg : IsPRegular p x := c.2 x <| by
    simp [ConjClasses.mem_carrier_iff_mk_eq, hx]
  intro y hy
  have hy' :
      ConjClasses.mk y =
        ConjClasses.pow (galoisPowerExponentUnit (G := G) t) (c : ConjClasses G) :=
    ConjClasses.mem_carrier_iff_mk_eq.mp hy
  rw [← hx, ConjClasses.pow_mk] at hy'
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hy').symm with ⟨a, rfl⟩
  simpa using isPRegular_conj p _ a
    (isPRegular_pow_galoisPowerExponentUnit (G := G) t hxreg)

/-- Helper for Exercise 12-12.7-8: `PRegularConjClass G p` carries the descended exponent-unit
power action. -/
private instance : MulAction (ZMod (Monoid.exponent G))ˣ (PRegularConjClass G p) where
  smul t c :=
    ⟨ConjClasses.pow (galoisPowerExponentUnit (G := G) t) (c : ConjClasses G),
      pow_mem (G := G) t c⟩
  one_smul c := by
    apply Subtype.ext
    change ((1 : (ZMod (Monoid.exponent G))ˣ) • (c : ConjClasses G)) = c
    simp
  mul_smul t u c := by
    exact Subtype.ext <| mul_smul t u (c : ConjClasses G)

/-- Helper for Exercise 12-12.7-8: the exponent-unit action on a `p`-regular representative is
the class of the powered representative. -/
@[simp] private theorem smul_ofSubtype
    (t : (ZMod (Monoid.exponent G))ˣ) (s : {x : G // IsPRegular p x}) :
    t • PRegularConjClass.ofSubtype p s =
      PRegularConjClass.ofSubtype p
        ⟨s.1 ^ galoisPowerExponentUnit (G := G) t,
          isPRegular_pow_galoisPowerExponentUnit (G := G) t s.2⟩ := by
  apply Subtype.ext
  change (t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk s.1 =
    ConjClasses.mk (s.1 ^ galoisPowerExponentUnit (G := G) t)
  exact ConjClasses.smul_mk (G := G) t s.1

/-- Helper for Exercise 12-12.7-8: the subgroup action on `p`-regular classes is given by the
same power formula. -/
@[simp] private theorem smul_ofSubtype_subgroup
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (t : ΓK) (s : {x : G // IsPRegular p x}) :
    t • PRegularConjClass.ofSubtype p s =
      PRegularConjClass.ofSubtype p
        ⟨s.1 ^ t,
          isPRegular_pow_galoisPowerExponentUnit (G := G) (t : _) s.2⟩ := by
  apply Subtype.ext
  change ((t : (ZMod (Monoid.exponent G))ˣ) • ConjClasses.mk s.1) =
    ConjClasses.mk (s.1 ^ t)
  exact ConjClasses.smul_mk_subgroup (G := G) ΓK t s.1

end PRegularConjClass

/-- The `p`-regular Serre `Γ_K`-classes, realized canonically as an orbit quotient. -/
abbrev PRegularGaloisPowerClass (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ) :=
  MulAction.orbitRel.Quotient ΓK (PRegularConjClass G p)

/-- The canonical map from `p`-regular elements to their `p`-regular Serre `Γ_K`-class. -/
def pRegularGaloisPowerClassMk (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ) :
    {x : G // IsPRegular p x} → PRegularGaloisPowerClass ΓK p :=
  Quotient.mk'' ∘ PRegularConjClass.ofSubtype p

/-- Helper for Exercise 12-12.7-8: every `p`-regular Serre `Γ_K`-class is represented by a
`p`-regular element of `G`. -/
theorem pRegularGaloisPowerClassMk_surjective
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ) :
    Function.Surjective (pRegularGaloisPowerClassMk (G := G) ΓK p) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep (c : ConjClasses G)
  have hx_mem : x ∈ (c : ConjClasses G).carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  have hx_reg : IsPRegular p x := c.2 x hx_mem
  refine ⟨⟨x, hx_reg⟩, ?_⟩
  change Quotient.mk'' (PRegularConjClass.ofSubtype p ⟨x, hx_reg⟩) = Quotient.mk'' c
  congr
  apply Subtype.ext
  simpa [PRegularConjClass.coe_ofSubtype, hx]

end LocalGaloisPowerClasses

end Representation
