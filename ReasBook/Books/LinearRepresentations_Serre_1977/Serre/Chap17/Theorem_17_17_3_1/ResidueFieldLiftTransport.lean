import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance targetResidueFieldModule : Module A V :=
  Module.compHom V (algebraMap A k)
local instance targetResidueFieldIsScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: restricting a residue-field lift along a group homomorphism is
just the Chapter `15` restriction-stability statement, repackaged for the local proof route. -/
theorem residueFieldLift_comp_hom
    {G' : Type*} [Group G']
    {ρ : Representation k G V}
    {W : Type x} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    {ρA : Representation A G W}
    {red : W →ₗ[A] V}
    (hLift : IsResidueFieldLift ρ ρA red)
    (f : G' →* G) :
    IsResidueFieldLift (ρ.comp f) (ρA.comp f) red := by
  exact Representation.isResidueFieldLift_comp hLift f

/-- Helper for Theorem 17-17.3-1: a residue-field lift gives an `A`-linear intertwiner from the
lifted representation to the restricted-scalars residue representation. -/
theorem residueFieldLift_isIntertwining_restrictScalars
    {H : Type*} [Group H]
    {W : Type*} [AddCommGroup W] [Module k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {σ : Representation k H W}
    {σA : Representation A H P}
    {red : P →ₗ[A] W}
    (hLift : IsResidueFieldLift σ σA red) :
    σA.IsIntertwiningMap (Representation.restrictScalars A σ) red := by
  letI : Module A W := Module.compHom W (algebraMap A k)
  letI : IsScalarTower A k W :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module (MonoidAlgebra A H) P := Module.compHom P σA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A H) P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change σA.asAlgebraHom (algebraMap A (MonoidAlgebra A H) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (σA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A H) W :=
    Module.compHom W (Representation.restrictScalars A σ).asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A H) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (Representation.restrictScalars A σ).asAlgebraHom
            (algebraMap A (MonoidAlgebra A H) a) x = a • x
      simpa [Algebra.smul_def] using
        LinearMap.congr_fun
          ((Representation.restrictScalars A σ).asAlgebraHom.commutes a) x
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
    _ = (Representation.restrictScalars A σ) g (red x) := by
      rfl

/-- Helper for Theorem 17-17.3-1: once the Clifford split lands in the proper-overgroup branch,
the lifted subgroup reduction map followed by the ambient inclusion is already `H`-equivariant for
the restricted-scalars action on `ρ`. -/
lemma subrepresentation_lift_to_restricted_intertwining
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IsIntertwiningMap ((Representation.restrictScalars A ρ).comp H.subtype)
      ((W.toSubmodule.subtype.restrictScalars A).comp red_H) := by
  have hred :
      ρA_H.IsIntertwiningMap (Representation.restrictScalars A W.toRepresentation) red_H :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred ⊢
  intro h x
  change (((red_H (ρA_H h x) : W.toSubmodule) : V)) =
      (((Representation.restrictScalars A W.toRepresentation) h (red_H x) : W.toSubmodule) : V)
  exact congrArg Subtype.val (hred h x)

/-- Helper for Theorem 17-17.3-1: the subgroup residue-field reduction already satisfies the
pointwise intertwining identity needed before applying `Rep.indMap`. -/
theorem subrepresentation_lift_pointwise
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H, ∀ x : W0, red_H (ρA_H g x) =
      (Representation.restrictScalars A W.toRepresentation) g (red_H x) := by
  have hred :
      ρA_H.IsIntertwiningMap (Representation.restrictScalars A W.toRepresentation) red_H :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred
  intro g x
  simpa using hred g x

/-- Helper for Theorem 17-17.3-1: the subgroup reduction intertwining relation can be repackaged
as an equality of composed linear maps, which is the exact format needed for `Rep.ofHom`. -/
theorem subrepresentation_lift_comp_eq
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H, red_H ∘ₗ ρA_H g =
      (Representation.restrictScalars A W.toRepresentation) g ∘ₗ red_H := by
  intro g
  ext x
  simpa [LinearMap.comp_apply] using
    subrepresentation_lift_pointwise (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g x

/-- Helper for Theorem 17-17.3-1: postcomposing the reduction map with a target linear equivalence
preserves the base-change part of a residue-field lift. -/
theorem isBaseChange_of_equiv_target
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    {red : W0 →ₗ[A] V'}
    (e : V' ≃ₗ[k] V)
    (hbase : IsBaseChange k red) :
    IsBaseChange k ((e.toLinearMap.restrictScalars A).comp red) := by
  letI : Module A V' := Module.compHom V' (algebraMap A k)
  letI : IsScalarTower A k V' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine IsBaseChange.of_equiv (hbase.equiv ≪≫ₗ e) ?_
  intro x
  simpa [LinearMap.comp_apply] using congrArg e (hbase.equiv_tmul x)

/-- Helper for Theorem 17-17.3-1: transporting a residue-field lift across a target
representation equivalence only changes the reduction map by postcomposition with that
equivalence. -/
theorem residueFieldLift_of_equiv_target
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k G V'}
    {τ : Representation k G V}
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    {ρA : Representation A G W0}
    {red : W0 →ₗ[A] V'}
    (hLift : IsResidueFieldLift σ ρA red)
    (e : σ.Equiv τ) :
    IsResidueFieldLift τ ρA ((e.toLinearMap.restrictScalars A).comp red) := by
  letI : Module (MonoidAlgebra A G) W0 := Module.compHom W0 ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G) W0 :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G) V' := Module.compHom V' σ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G) V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change σ.asAlgebraHom (algebraMap k (MonoidAlgebra k G) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (σ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G) V := Module.compHom V τ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change τ.asAlgebraHom (algebraMap k (MonoidAlgebra k G) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (τ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G) V :=
    Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G) (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G) (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  change (((e.toLinearMap.restrictScalars A).comp red).IsResidueFieldReduction G)
  change red.IsResidueFieldReduction G at hLift
  constructor
  · exact isBaseChange_of_equiv_target (A := A) (V := V) e.toLinearEquiv hLift.1
  · refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    calc
      ((e.toLinearMap.restrictScalars A).comp red) (MonoidAlgebra.of A G g • x)
          = e (red (MonoidAlgebra.of A G g • x)) := by
              rfl
      _ = e (MonoidAlgebra.of k G g • red x) := by
            change e (red (MonoidAlgebra.of A G g • x)) = _
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hLift g x]
      _ = e (σ g (red x)) := by
            change e ((σ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red x)) = _
            simp [Representation.asAlgebraHom_single]
      _ = τ g (((e.toLinearMap.restrictScalars A).comp red) x) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (e.isIntertwining' g) (red x)
      _ = MonoidAlgebra.of k G g • (((e.toLinearMap.restrictScalars A).comp red) x) := by
            change τ g (((e.toLinearMap.restrictScalars A).comp red) x) =
              (τ.asAlgebraHom (MonoidAlgebra.single g (1 : k)))
                (((e.toLinearMap.restrictScalars A).comp red) x)
            simp [Representation.asAlgebraHom_single]
      _ =
          (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) •
            (((e.toLinearMap.restrictScalars A).comp red) x) := by
              simp [MonoidAlgebra.of_apply]
      _ = MonoidAlgebra.of A G g • (((e.toLinearMap.restrictScalars A).comp red) x) := by
            rfl

/-- Helper for Theorem 17-17.3-1: the subgroup residue map itself is already an intertwiner into
the restricted-scalars lift of the inducing subrepresentation. -/
theorem subrepresentation_lift_as_intertwiningMap
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IsIntertwiningMap (Representation.restrictScalars A W.toRepresentation) red_H := by
  rw [Representation.isIntertwiningMap_iff]
  intro g x
  exact subrepresentation_lift_pointwise (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g x

/-- Helper for Theorem 17-17.3-1: after composing with the inclusion `W ↪ V`, the subgroup
reduction commutes with the restricted ambient action as an equality of composed linear maps. -/
theorem subrepresentation_lift_to_restricted_comp_eq
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H,
      ((W.toSubmodule.subtype.restrictScalars A).comp red_H) ∘ₗ ρA_H g =
        ((Representation.restrictScalars A ρ).comp H.subtype) g ∘ₗ
          ((W.toSubmodule.subtype.restrictScalars A).comp red_H) := by
  have hred :
      ρA_H.IsIntertwiningMap ((Representation.restrictScalars A ρ).comp H.subtype)
        ((W.toSubmodule.subtype.restrictScalars A).comp red_H) :=
    subrepresentation_lift_to_restricted_intertwining
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred
  intro g
  ext x
  simpa [LinearMap.comp_apply] using hred g x

/-- Helper for Theorem 17-17.3-1: after composing with the inclusion `W ↪ V`, the subgroup
reduction satisfies the ambient restricted-action compatibility pointwise. -/
theorem subrepresentation_lift_to_restricted_pointwise
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : H, ∀ x : W0,
      ((W.toSubmodule.subtype.restrictScalars A).comp red_H) (ρA_H g x) =
        ((Representation.restrictScalars A ρ).comp H.subtype) g
          (((W.toSubmodule.subtype.restrictScalars A).comp red_H) x) := by
  have hred :
      ρA_H.IsIntertwiningMap ((Representation.restrictScalars A ρ).comp H.subtype)
        ((W.toSubmodule.subtype.restrictScalars A).comp red_H) :=
    subrepresentation_lift_to_restricted_intertwining
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  rw [Representation.isIntertwiningMap_iff] at hred
  intro g x
  simpa using hred g x

/-- Helper for Theorem 17-17.3-1: the subgroup reduction descends directly to the standard
induced `k`-model by first inserting the reduced coefficient at the unit coset and then applying
the induction adjunction. -/
theorem induced_subrepresentation_lift_unit_isIntertwining
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IsIntertwiningMap
      ((Representation.restrictScalars A
          (Representation.ind H.subtype W.toRepresentation)).comp H.subtype)
      (((Representation.IndV.mk H.subtype W.toRepresentation 1).restrictScalars A) ∘ₗ red_H) := by
  have hredPointwise :
      ∀ h : H, ∀ x : W0, red_H (ρA_H h x) =
        (Representation.restrictScalars A W.toRepresentation) h (red_H x) :=
    subrepresentation_lift_pointwise (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  rw [Representation.isIntertwiningMap_iff]
  intro h x
  change
    Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H (ρA_H h x)) =
      (Representation.ind H.subtype W.toRepresentation) h
        (Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H x))
  rw [hredPointwise h x]
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  simpa [Representation.IndV.mk, Representation.ind_mk, Representation.ofMulAction_single] using
    (Representation.Coinvariants.mk_inv_tmul
      (ρ := (Representation.leftRegular k G).comp H.subtype)
      (τ := W.toRepresentation)
      (x := Finsupp.single (1 : G) (1 : k))
      (y := red_H x)
      (g := h)).symm

end

end Representation
