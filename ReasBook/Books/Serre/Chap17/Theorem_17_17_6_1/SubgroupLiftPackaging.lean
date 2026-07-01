import Mathlib
import Serre.Chap01.Theorem_1_1_4_2
import Serre.GroupTheory.PSolvable
import Serre.Chap07.Proposition_7_7_1_3
import Serre.Chap07.Remark_7_7_1_4
import Serre.Chap15.Exercise_15_15_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {h : ℕ}
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance subgroupLiftPackagingModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance subgroupLiftPackagingScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: restricting a residue-field lift along a group homomorphism
keeps the same reduction map. -/
theorem residueFieldLift_comp_hom
    {G' : Type*} [Group G']
    {ρ : Representation k G V}
    {P : Type x} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A G P}
    {red : P →ₗ[A] V}
    (hLift : IsResidueFieldLift ρ ρA red)
    (f : G' →* G) :
    IsResidueFieldLift (ρ.comp f) (ρA.comp f) red := by
  exact Representation.isResidueFieldLift_comp hLift f

/-- Helper for Theorem 17-17.6-1: a residue-field lift supplies the expected `A`-linear
intertwining map into the restricted-scalars residue representation. -/
theorem residueFieldLift_isIntertwining_restrictScalars
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {σ : Representation k H W}
    {σA : Representation A H P}
    {red : P →ₗ[A] W}
    (hLift : IsResidueFieldLift σ σA red) :
    σA.IsIntertwiningMap (σ.restrictScalars A) red := by
  letI : Module (MonoidAlgebra A H) P := Module.compHom P σA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A H) P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change σA.asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (σA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A H) W :=
    Module.compHom W (σ.restrictScalars A).asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A H) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (σ.restrictScalars A).asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
      simpa [Algebra.smul_def] using
        LinearMap.congr_fun ((σ.restrictScalars A).asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k H) W := Module.compHom W σ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k H) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change σ.asAlgebraHom (algebraMap k (MonoidAlgebra k H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (σ.asAlgebraHom.commutes a) x
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  have hσA : MonoidAlgebra.single g (1 : A) • x = σA g x := by
    change (σA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x = σA g x
    simp [Representation.asAlgebraHom_single]
  calc
    red (σA g x) = red (MonoidAlgebra.single g (1 : A) • x) := by
      rw [hσA]
    _ = MonoidAlgebra.of k H g • red x := by
      simpa [MonoidAlgebra.of] using hLift.map_monoidAlgebra_of g x
    _ = σ g (red x) := by
      change (σ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red x) = σ g (red x)
      simp [Representation.asAlgebraHom_single]
    _ = (σ.restrictScalars A) g (red x) := by
      rfl

/-- Helper for Theorem 17-17.6-1: the lifted subgroup reduction map followed by the ambient
inclusion is already `H`-equivariant for the restricted-scalars action on `ρ`. -/
theorem subrepresentation_lift_to_restricted_intertwining
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IsIntertwiningMap ((ρ.restrictScalars A).comp H.subtype)
      ((W.toSubmodule.subtype.restrictScalars A).comp red_H) := by
  have hred :
      ρA_H.IsIntertwiningMap (W.toRepresentation.restrictScalars A) red_H :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred ⊢
  intro h x
  change (((red_H (ρA_H h x) : W.toSubmodule) : V)) =
      (((W.toRepresentation.restrictScalars A) h (red_H x) : W.toSubmodule) : V)
  exact congrArg Subtype.val (hred h x)

/-- Helper for Theorem 17-17.6-1: the subgroup-side reduction formula can be used pointwise when
bundling the map as a `Rep A H` morphism before induction. -/
theorem subrepresentation_lift_pointwise
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H, ∀ x : P, red_H (ρA_H g x) = (W.toRepresentation.restrictScalars A) g (red_H x) := by
  have hred :
      ρA_H.IsIntertwiningMap (W.toRepresentation.restrictScalars A) red_H :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred
  intro g x
  simpa using hred g x

/-- Helper for Theorem 17-17.6-1: a target linear equivalence transports the base-change part of
the residue-field-lift data. -/
theorem isBaseChange_of_equiv_target
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {red : P →ₗ[A] V'}
    (e : V' ≃ₗ[k] V)
    (hbase : IsBaseChange k red) :
    IsBaseChange k ((e.toLinearMap.restrictScalars A).comp red) := by
  letI : Module A V' := Module.compHom V' (algebraMap A k)
  letI : IsScalarTower A k V' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine IsBaseChange.of_equiv (hbase.equiv ≪≫ₗ e) ?_
  intro x
  simpa [LinearMap.comp_apply] using congrArg e (hbase.equiv_tmul x)

/-- Helper for Theorem 17-17.6-1: the subgroup reduction intertwining relation can be repackaged
as an equality of composed linear maps, which is the exact format needed before induction is
applied to that reduction morphism. -/
theorem subrepresentation_lift_comp_eq
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type x} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H, red_H ∘ₗ ρA_H g = (W.toRepresentation.restrictScalars A) g ∘ₗ red_H := by
  intro g
  ext x
  simpa [LinearMap.comp_apply] using
    subrepresentation_lift_pointwise (A := A) (ρ := ρ) W ρA_H red_H hLiftH g x

/-- Helper for Theorem 17-17.6-1: the subgroup residue-field reduction packages into a genuine
`Rep A H` morphism before induction is applied. -/
noncomputable def subrepresentation_lift_hom
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type x} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    Rep.of ρA_H ⟶ Rep.of (W.toRepresentation.restrictScalars A) :=
  Rep.ofHom
    ⟨red_H, by
      intro g
      ext x
      simpa [LinearMap.comp_apply] using
        subrepresentation_lift_pointwise (A := A) (ρ := ρ) W ρA_H red_H hLiftH g x⟩

/-- Helper for Theorem 17-17.6-1: inducing the packaged subgroup reduction gives the canonical
map between the two induced models, acting coefficientwise on standard generators. -/
noncomputable def induced_subrepresentation_lift_hom
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type x} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    Rep.of ((Rep.ind H.subtype (Rep.of ρA_H)).ρ) ⟶
      Rep.of ((Rep.ind H.subtype (Rep.of (W.toRepresentation.restrictScalars A))).ρ) :=
  Rep.indMap H.subtype
    (subrepresentation_lift_hom (A := A) (ρ := ρ) W ρA_H red_H hLiftH)

/-- Helper for Theorem 17-17.6-1: on the standard induced generators, the induced subgroup
reduction simply applies `red_H` to the coefficient. -/
theorem induced_subrepresentation_lift_hom_apply_mk
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {P : Type x} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA_H : Representation A H P)
    (red_H : P →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (g : G) (x : P) :
    (induced_subrepresentation_lift_hom (A := A) (ρ := ρ) W ρA_H red_H hLiftH).hom
      (Representation.IndV.mk H.subtype ρA_H g x) =
        Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A) g (red_H x) := by
  simp [induced_subrepresentation_lift_hom, subrepresentation_lift_hom, Rep.indMap]

end

end Representation
