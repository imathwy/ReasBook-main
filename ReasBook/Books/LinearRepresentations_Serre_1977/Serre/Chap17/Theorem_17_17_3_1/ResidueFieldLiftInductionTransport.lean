import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance residueFieldLiftInductionTransportResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance residueFieldLiftInductionTransportResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: the raw Chapter `14` residue-field reduction package attached
to a pair of source/target representations, without the extra free/finite hypotheses bundled into
`IsResidueFieldLift`. -/
abbrev RawIsResidueFieldReduction_local
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    (ρ : Representation k G' V')
    (ρA : Representation A G' P0)
    (red : P0 →ₗ[A] V') : Prop :=
  letI : Module (MonoidAlgebra A G') P0 := Module.compHom P0 ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P0 :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G' (algebraMap A k))
            (MonoidAlgebra.single (1 : G') a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G') (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G')
                    (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  red.IsResidueFieldReduction G'

/-- Helper for Theorem 17-17.3-1: transporting a residue-field lift across a source
representation equivalence only changes the reduction map by precomposition with that
equivalence. -/
theorem residueFieldLift_of_equiv_source_local
    {G' : Type*} [Group G'] [Finite G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P' : Type*} [AddCommGroup P'] [Module A P']
    [Module.Free A P'] [Module.Finite A P']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    [Module.Free A P0] [Module.Finite A P0]
    {ρ : Representation k G' V'}
    {ρA' : Representation A G' P'}
    {ρA : Representation A G' P0}
    {red : P0 →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red)
    (e : ρA'.Equiv ρA) :
    IsResidueFieldLift ρ ρA' (red.comp e.toLinearMap) := by
  letI : Module (MonoidAlgebra A G') P' := Module.compHom P' ρA'.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA'.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA'.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') P0 := Module.compHom P0 ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P0 :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G' (algebraMap A k))
            (MonoidAlgebra.single (1 : G') a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G') (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G')
                    (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  change (red.comp e.toLinearMap).IsResidueFieldReduction G'
  change red.IsResidueFieldReduction G' at hLift
  constructor
  · -- The source carrier only changes by an `A`-linear equivalence, so compose the two base
    -- change witnesses directly.
    have he : IsBaseChange A e.toLinearMap := IsBaseChange.ofEquiv e.toLinearEquiv
    simpa [LinearMap.comp_assoc] using
      (IsBaseChange.comp (R := A) (S := A) (T := k) he hLift.1)
  · -- Check the equivariance after rewriting the transported source action through `e`.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq : e (MonoidAlgebra.of A G' g • x) = MonoidAlgebra.of A G' g • e x := by
      change
        e ((ρA'.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x) =
          (ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) (e x)
      simpa [Representation.asAlgebraHom_single] using
        LinearMap.congr_fun (e.isIntertwining' g) x
    calc
      (red.comp e.toLinearMap) (MonoidAlgebra.of A G' g • x)
          = red (MonoidAlgebra.of A G' g • e x) := by
              simpa [LinearMap.comp_apply] using congrArg red heq
      _ = MonoidAlgebra.of k G' g • red (e x) := by
            simpa using LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hLift g (e x)
      _ =
          (MonoidAlgebra.mapRingHom G' (algebraMap A k) (MonoidAlgebra.of A G' g)) •
            (((red.comp e.toLinearMap) x)) := by
              simp [MonoidAlgebra.of_apply, LinearMap.comp_apply]
      _ = MonoidAlgebra.of A G' g • (((red.comp e.toLinearMap) x)) := by
            rfl

/-- Helper for Theorem 17-17.3-1: transporting the raw Chapter `14` residue-field reduction data
across a source representation equivalence only changes the reduction map by precomposition with
that equivalence. -/
theorem residueFieldReduction_of_equiv_source_local
    {G' : Type*} [Group G'] [Finite G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P' : Type*} [AddCommGroup P'] [Module A P']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    {ρ : Representation k G' V'}
    {ρA' : Representation A G' P'}
    {ρA : Representation A G' P0}
    {red : P0 →ₗ[A] V'}
    (hbase : IsBaseChange k red)
    (hinter : ρA.IsIntertwiningMap (ρ.restrictScalars A) red)
    (e : ρA'.Equiv ρA) :
    RawIsResidueFieldReduction_local (A := A) ρ ρA' (red.comp e.toLinearMap) := by
  letI : Module (MonoidAlgebra A G') P' := Module.compHom P' ρA'.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA'.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA'.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') P0 := Module.compHom P0 ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P0 :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G' (algebraMap A k))
            (MonoidAlgebra.single (1 : G') a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G') (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G')
                    (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  change (red.comp e.toLinearMap).IsResidueFieldReduction G'
  constructor
  · -- The source carrier only changes by an `A`-linear equivalence, so compose the two base
    -- change witnesses directly.
    have he : IsBaseChange A e.toLinearMap := IsBaseChange.ofEquiv e.toLinearEquiv
    simpa [LinearMap.comp_assoc] using
      (IsBaseChange.comp (R := A) (S := A) (T := k) he hbase)
  · -- Check equivariance after rewriting the transported source action through `e`.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq : e (MonoidAlgebra.of A G' g • x) = MonoidAlgebra.of A G' g • e x := by
      change
        e ((ρA'.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x) =
          (ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) (e x)
      simpa [Representation.asAlgebraHom_single] using
        LinearMap.congr_fun (e.isIntertwining' g) x
    calc
      (red.comp e.toLinearMap) (MonoidAlgebra.of A G' g • x)
          = red (MonoidAlgebra.of A G' g • e x) := by
              simpa [LinearMap.comp_apply] using congrArg red heq
      _ = red (ρA g (e x)) := by
            change
              red ((ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) (e x)) =
                red (ρA g (e x))
            simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
      _ = ρ g (red (e x)) := by
            simpa [Representation.restrictScalars_apply] using
              hinter.isIntertwining g (e x)
      _ = MonoidAlgebra.of k G' g • red (e x) := by
            change ρ g (red (e x)) =
              (ρ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red (e x))
            simp [Representation.asAlgebraHom_single]
      _ =
          (MonoidAlgebra.mapRingHom G' (algebraMap A k) (MonoidAlgebra.of A G' g)) •
            (((red.comp e.toLinearMap) x)) := by
              simp [MonoidAlgebra.of_apply, LinearMap.comp_apply]
      _ = MonoidAlgebra.of A G' g • (((red.comp e.toLinearMap) x)) := by
            rfl

/-- Helper for Theorem 17-17.3-1: once the base-change and intertwining parts are proved
separately, they package back into the Chapter `14` residue-field reduction owner. -/
theorem residueFieldReduction_of_isBaseChange_isIntertwining
    {G' : Type*} [Group G'] [Finite G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P0}
    {red : P0 →ₗ[A] V'}
    (hbase : IsBaseChange k red)
    (hinter : ρA.IsIntertwiningMap (ρ.restrictScalars A) red) :
    RawIsResidueFieldReduction_local (A := A) ρ ρA red := by
  letI : Module (MonoidAlgebra A G') P0 := Module.compHom P0 ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P0 :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G' (algebraMap A k))
            (MonoidAlgebra.single (1 : G') a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G') (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G')
                    (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  change red.IsResidueFieldReduction G'
  refine ⟨hbase, ?_⟩
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  calc
    red (MonoidAlgebra.of A G' g • x) = red (ρA g x) := by
      change
        red ((ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x) = red (ρA g x)
      simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
    _ = ρ g (red x) := by
          simpa [Representation.restrictScalars_apply] using hinter.isIntertwining g x
    _ = MonoidAlgebra.of k G' g • red x := by
          change ρ g (red x) = (ρ.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red x)
          simp [Representation.asAlgebraHom_single]
    _ =
        (MonoidAlgebra.mapRingHom G' (algebraMap A k) (MonoidAlgebra.of A G' g)) • red x := by
          simp [MonoidAlgebra.of_apply]
    _ = MonoidAlgebra.of A G' g • red x := by
          rfl

/-- Helper for Theorem 17-17.3-1: a lifted `A[G]`-representation may be moved into a `ULift`
carrier without changing its action. -/
def uliftRepresentation_witness_local
    {G' : Type v} [Group G']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    (ρA : Representation A G' P0) :
    Representation A G' (ULift.{max (max u v) w} P0) where
  toFun g :=
    { toFun := fun p ↦ ⟨ρA g p.down⟩
      map_add' := by
        intro p q
        ext
        simp
      map_smul' := by
        intro a p
        ext
        simp }
  map_one' := by
    ext p
    simp
  map_mul' g h := by
    ext p
    simp [map_mul]

/-- Helper for Theorem 17-17.3-1: raising the lifted source carrier to a `ULift` universe
preserves the residue-field lift. -/
theorem residueFieldLift_ulift_witness_local
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type w} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    {P0 : Type*} [AddCommGroup P0] [Module A P0]
    [Module.Free A P0] [Module.Finite A P0]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P0}
    {red : P0 →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    IsResidueFieldLift ρ (uliftRepresentation_witness_local (A := A) ρA)
      (red.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} P0 ≃ₗ[A] P0).toLinearMap) := by
  let eU :
      (uliftRepresentation_witness_local (A := A) ρA).Equiv ρA :=
    Representation.Equiv.mk ULift.moduleEquiv fun g ↦ by
      -- Both actions are definitionally the same after inserting the `ULift` wrapper.
      ext x
      rfl
  -- Specialize the generic source transport to the tautological `ULift` equivalence.
  exact residueFieldLift_of_equiv_source_local (A := A) (ρ := ρ) hLift eU

/-- Helper for Theorem 17-17.3-1: the tautological inclusion of an `H`-stable subrepresentation
into the restricted ambient representation is an intertwining map. -/
noncomputable def subrepresentation_inclusion_hom_generic
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (σ : Representation k G' V')
    (H : Subgroup G')
    (W : Subrepresentation (σ.comp H.subtype)) :
    W.toRepresentation.IntertwiningMap (σ.comp H.subtype) :=
  W.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    W.toRepresentation (σ.comp H.subtype) fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: the subgroup reduction descends directly to the standard
induced restricted-scalars `A`-model by applying `Rep.indMap` to the subgroup reduction morphism.
-/
noncomputable def induced_subrepresentation_lift_direct
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    Representation.IndV H.subtype ρA_H →ₗ[A]
      Representation.IndV H.subtype (W.toRepresentation.restrictScalars A) := by
  -- Route correction: stay on the first restricted-scalars induced target and descend the
  -- subgroup reduction directly through coinvariants before any comparison with the ambient
  -- standard induced `k`-model.
  letI : Module A A := Semiring.toModule
  letI : Module A (G →₀ A) := Finsupp.module G A
  have hintertwine :
      ∀ g : H, red_H ∘ₗ ρA_H g = (W.toRepresentation.restrictScalars A) g ∘ₗ red_H :=
    subrepresentation_lift_comp_eq (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  refine Representation.Coinvariants.map _ _ (LinearMap.lTensor (G →₀ A) red_H) ?_
  intro g
  ext a b
  simp [LinearMap.lTensor_comp_map, LinearMap.map_comp_lTensor, hintertwine g]

/-- Helper for Theorem 17-17.3-1: the descended induced reduction sends a standard induced
generator to the corresponding generator with coefficient reduced by `red_H`. -/
theorem induced_subrepresentation_lift_direct_apply_mk
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (g : G) (x : W0) :
    induced_subrepresentation_lift_direct
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
        (Representation.IndV.mk H.subtype ρA_H g x) =
      Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A) g (red_H x) := by
  -- On standard induced generators, `Rep.indMap` acts coefficientwise by the subgroup reduction.
  letI : Module A A := Semiring.toModule
  letI : Module A (G →₀ A) := Finsupp.module G A
  simp [induced_subrepresentation_lift_direct]

/-- Helper for Theorem 17-17.3-1: on standard induced generators, applying the ambient `G`-action
before the direct induced reduction is the same as reducing first and then applying the induced
restricted-scalars action. -/
theorem induced_subrepresentation_lift_direct_apply_induced_generator_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (g g' : G) (x : W0) :
    induced_subrepresentation_lift_direct
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
        ((Representation.ind H.subtype ρA_H) g
          (Representation.IndV.mk H.subtype ρA_H g' x)) =
      (Representation.ind H.subtype (W.toRepresentation.restrictScalars A)) g
        (Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A) g' (red_H x)) := by
  -- Rewrite both sides by the standard `IndV.mk` formula and the induced action formula.
  calc
    induced_subrepresentation_lift_direct
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
        ((Representation.ind H.subtype ρA_H) g
          (Representation.IndV.mk H.subtype ρA_H g' x))
        =
      induced_subrepresentation_lift_direct
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
        (Representation.IndV.mk H.subtype ρA_H (g' * g⁻¹) x) := by
          rw [Representation.ind_mk]
    _ = Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A)
          (g' * g⁻¹) (red_H x) := by
            rw [induced_subrepresentation_lift_direct_apply_mk
              (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
    _ =
      (Representation.ind H.subtype (W.toRepresentation.restrictScalars A)) g
        (Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A) g' (red_H x)) := by
          rw [Representation.ind_mk]

/-- Helper for Theorem 17-17.3-1: the direct induced reduction already intertwines the induced
`A[G]`-model with the induced restricted-scalars target before any comparison with the ambient
standard induced model is applied. -/
theorem induced_subrepresentation_lift_direct_isIntertwining_restricted_target_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    (Representation.ind H.subtype ρA_H).IsIntertwiningMap
      (Representation.ind H.subtype (W.toRepresentation.restrictScalars A))
      (induced_subrepresentation_lift_direct
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro g v
  have hcomp :
      induced_subrepresentation_lift_direct
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH ∘ₗ
        (Representation.ind H.subtype ρA_H) g =
        (Representation.ind H.subtype (W.toRepresentation.restrictScalars A)) g ∘ₗ
          induced_subrepresentation_lift_direct
            (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH := by
    -- The induced model is generated by the standard `IndV.mk` classes, so it is enough to check
    -- the equality on those generators.
    refine
      Representation.IndV.hom_ext
        (φ := H.subtype) (ρ := ρA_H)
        (B := Representation.IndV H.subtype (W.toRepresentation.restrictScalars A)) ?_
    intro g'
    ext x
    calc
      induced_subrepresentation_lift_direct
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
          ((Representation.ind H.subtype ρA_H) g
            (Representation.IndV.mk H.subtype ρA_H g' x))
          =
        induced_subrepresentation_lift_direct
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
            (Representation.IndV.mk H.subtype ρA_H (g' * g⁻¹) x) := by
              rw [Representation.ind_mk]
      _ = Representation.IndV.mk H.subtype (W.toRepresentation.restrictScalars A)
            (g' * g⁻¹) (red_H x) := by
              rw [induced_subrepresentation_lift_direct_apply_mk
                (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
      _ =
        (Representation.ind H.subtype (W.toRepresentation.restrictScalars A)) g
          (induced_subrepresentation_lift_direct
            (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
            (Representation.IndV.mk H.subtype ρA_H g' x)) := by
              rw [induced_subrepresentation_lift_direct_apply_mk
                (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
              rw [Representation.ind_mk]
  exact LinearMap.congr_fun hcomp v

/-- Helper for Theorem 17-17.3-1: the direct induced reduction intertwines the two induced
actions as an equality of composed linear maps, which is the transport-stable format needed for
the next packaging step in the proper-overgroup branch. -/
theorem induced_subrepresentation_lift_direct_comp_eq_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∀ g : G,
      induced_subrepresentation_lift_direct
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH ∘ₗ
        (Representation.ind H.subtype ρA_H) g =
        (Representation.ind H.subtype (W.toRepresentation.restrictScalars A)) g ∘ₗ
          induced_subrepresentation_lift_direct
            (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH := by
  intro g
  -- Repackage the pointwise induced equivariance into the linear-map equality needed later.
  have hInter :
      (Representation.ind H.subtype ρA_H).IsIntertwiningMap
        (Representation.ind H.subtype (W.toRepresentation.restrictScalars A))
        (induced_subrepresentation_lift_direct
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH) :=
    induced_subrepresentation_lift_direct_isIntertwining_restricted_target_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  rw [Representation.isIntertwiningMap_iff] at hInter
  apply LinearMap.ext
  intro z
  exact hInter g z

/-- Helper for Theorem 17-17.3-1: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
noncomputable def comp_subtype_equiv_local_c17
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G') :
    Representation.Equiv (ρ₁.comp H.subtype) (ρ₂.comp H.subtype) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro h
  -- Restricting the ambient intertwiner does not change its pointwise formula.
  simpa using e.isIntertwining' (h : G')

/-- Helper for Theorem 17-17.3-1: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
noncomputable def transported_subrepresentation_of_equiv_local_c17
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (U : Subrepresentation ρ₁) :
    Subrepresentation ρ₂ where
  toSubmodule := U.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule := by
    intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    -- Mapping the carrier through the intertwiner preserves stability under the action.
    exact ⟨ρ₁ g y, U.apply_mem_toSubmodule g hy, by
      simpa using LinearMap.congr_fun (e.isIntertwining' g) y⟩

/-- Helper for Theorem 17-17.3-1: transporting the inducing subrepresentation along an ambient
equivalence transports each left-coset summand by the same linear equivalence. -/
theorem leftQuotientSubmodule_eq_map_of_equiv_local_c17
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype)) (q : G' ⧸ H) :
    ρ₂.leftQuotientSubmodule H
        (transported_subrepresentation_of_equiv_local_c17
          (comp_subtype_equiv_local_c17 e H) U) q =
      (ρ₁.leftQuotientSubmodule H U q).map e.toLinearMap := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both quotient summands are images of the same source carrier under the translated action.
  rw [Representation.leftQuotientSubmodule_mk, Representation.leftQuotientSubmodule_mk]
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ₁ g u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa using LinearMap.congr_fun (e.isIntertwining' g) u
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨e u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa using (LinearMap.congr_fun (e.isIntertwining' g) u).symm

/-- Helper for Theorem 17-17.3-1: inducedness data is preserved when the ambient representation is
replaced by an equivalent one. -/
theorem isInducedFromSubrepresentation_of_equiv_local_c17
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype))
    (hU : ρ₁.IsInducedFromSubrepresentation H U) :
    ρ₂.IsInducedFromSubrepresentation H
      (transported_subrepresentation_of_equiv_local_c17
        (comp_subtype_equiv_local_c17 e H) U) := by
  classical
  let _ : DecidableEq (G' ⧸ H) := Classical.decEq _
  let U' :=
    transported_subrepresentation_of_equiv_local_c17
      (comp_subtype_equiv_local_c17 e H) U
  have hinternal : DirectSum.IsInternal (ρ₁.leftQuotientSubmodule H U) := by
    -- Unpack the Chapter 3 owner so the transport can proceed on the quotient-indexed family.
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  have hleft_fun :
      ρ₂.leftQuotientSubmodule H U' =
        fun q ↦ (ρ₁.leftQuotientSubmodule H U q).map e.toLinearMap := by
    funext q
    simpa [U'] using leftQuotientSubmodule_eq_map_of_equiv_local_c17 e H U q
  have hindep : iSupIndep (ρ₂.leftQuotientSubmodule H U') := by
    -- Independence transports because the ambient equivalence is injective.
    rw [hleft_fun]
    exact LinearMap.iSupIndep_map e.toLinearMap e.injective hinternal.submodule_iSupIndep
  have hspan : iSup (ρ₂.leftQuotientSubmodule H U') = ⊤ := by
    -- Surjectivity transports the spanning equality of the old quotient family.
    calc
      iSup (ρ₂.leftQuotientSubmodule H U') =
          iSup (fun q ↦ (ρ₁.leftQuotientSubmodule H U q).map e.toLinearMap) := by
            rw [hleft_fun]
      _ = (iSup (ρ₁.leftQuotientSubmodule H U)).map e.toLinearMap := by
            rw [Submodule.map_iSup]
      _ = ⊤ := by
            rw [hinternal.submodule_iSup_eq_top, Submodule.map_top]
            exact LinearMap.range_eq_top.mpr e.surjective
  -- Repackage the transported independence and spanning statements back into the owner predicate.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Theorem 17-17.3-1: induction along a source equivalence preserves the standard
induced model. -/
noncomputable def ind_equiv_of_source_equiv_local_c17
    {G' K : Type*} [Group G'] [Group K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (f : G' →* K) {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) :
    (Representation.ind f ρ₁).Equiv (Representation.ind f ρ₂) := by
  letI : Module k k := Semiring.toModule
  letI : Module k (K →₀ k) := Finsupp.module K k
  let inducedSourceHom :
      (Representation.ind f ρ₁).IntertwiningMap (Representation.ind f ρ₂) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        intro g
        ext h a
        simp }
  let inducedSourceInv :
      (Representation.ind f ρ₂).IntertwiningMap (Representation.ind f ρ₁) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg
              (fun z ↦ (Finsupp.single (f g * x) (1 : k)) ⊗ₜ[k] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedSourceInv.toLinearMap ∘ₗ inducedSourceHom.toLinearMap = LinearMap.id := by
    -- On standard generators the two induced maps are inverse because `e.symm ∘ e = id`.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  have hinduced_hom_inv :
      inducedSourceHom.toLinearMap ∘ₗ inducedSourceInv.toLinearMap = LinearMap.id := by
    -- The same generator computation proves the inverse identity in the other direction.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedSourceHom.toLinearMap inducedSourceInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedSourceHom.isIntertwining'

/-- Helper for Theorem 17-17.3-1: the same induced-source transport works over any coefficient
ring, so it may also be used on the recursively lifted `A[H]`-model. -/
noncomputable def ind_equiv_of_source_equiv_over_local
    {R : Type*} [CommRing R]
    {G' K : Type*} [Group G'] [Group K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    (f : G' →* K) {ρ₁ : Representation R G' V₁} {ρ₂ : Representation R G' V₂}
    (e : ρ₁.Equiv ρ₂) :
    (Representation.ind f ρ₁).Equiv (Representation.ind f ρ₂) := by
  letI : Module R R := Semiring.toModule
  letI : Module R (K →₀ R) := Finsupp.module K R
  let inducedSourceHom :
      (Representation.ind f ρ₁).IntertwiningMap (Representation.ind f ρ₂) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        -- The induced action commutes with the transported source map on standard generators.
        intro g
        ext h a
        simp }
  let inducedSourceInv :
      (Representation.ind f ρ₂).IntertwiningMap (Representation.ind f ρ₁) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg
              (fun z ↦ (Finsupp.single (f g * x) (1 : R)) ⊗ₜ[R] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        -- The same generator computation gives the inverse intertwining map.
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedSourceInv.toLinearMap ∘ₗ inducedSourceHom.toLinearMap = LinearMap.id := by
    -- On standard generators the two induced maps are inverse because `e.symm ∘ e = id`.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  have hinduced_hom_inv :
      inducedSourceHom.toLinearMap ∘ₗ inducedSourceInv.toLinearMap = LinearMap.id := by
    -- The same generator computation proves the inverse identity in the other direction.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedSourceHom.toLinearMap inducedSourceInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedSourceHom.isIntertwining'

/-- Helper for Theorem 17-17.3-1: the induced transport attached to a source equivalence sends
each standard `IndV.mk` generator to the corresponding generator with transported coefficient. -/
theorem ind_equiv_of_source_equiv_over_local_apply_mk
    {R : Type*} [CommRing R]
    {G' K : Type*} [Group G'] [Group K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    (f : G' →* K) {ρ₁ : Representation R G' V₁} {ρ₂ : Representation R G' V₂}
    (e : ρ₁.Equiv ρ₂) (g : K) (x : V₁) :
    ind_equiv_of_source_equiv_over_local (R := R) f e
      (Representation.IndV.mk f ρ₁ g x) =
        Representation.IndV.mk f ρ₂ g (e x) := by
  letI : Module R R := Semiring.toModule
  letI : Module R (K →₀ R) := Finsupp.module K R
  -- Unfold the induced transport once: on generators it is just `Coinvariants.map` applied to
  -- the source tensor factor, so the coefficient is carried by `e` and the coset label is fixed.
  dsimp [ind_equiv_of_source_equiv_over_local]

/-- Helper for Theorem 17-17.3-1: the induced transport attached to a source equivalence is
`R`-linear on standard generators, so scalar multiples of `IndV.mk` are transported coefficientwise
without changing the ambient coset label. -/
theorem ind_equiv_of_source_equiv_over_local_apply_smul_mk
    {R : Type*} [CommRing R]
    {G' K : Type*} [Group G'] [Group K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    (f : G' →* K) {ρ₁ : Representation R G' V₁} {ρ₂ : Representation R G' V₂}
    (e : ρ₁.Equiv ρ₂) (a : R) (g : K) (x : V₁) :
    ind_equiv_of_source_equiv_over_local (R := R) f e
      (a • Representation.IndV.mk f ρ₁ g x) =
        a • Representation.IndV.mk f ρ₂ g (e x) := by
  -- Pull the scalar through the induced equivalence, then reuse the generator formula.
  rw [map_smul]
  rw [ind_equiv_of_source_equiv_over_local_apply_mk]

/-- Helper for Theorem 17-17.3-1: after lifting the subgroup source carrier to `ULift`, the
inverse induced-source equivalence sends each standard generator back to the corresponding lifted
generator. -/
theorem induced_source_ulift_equiv_symm_apply_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_H : Representation A H W0)
    (g : G) (x : W0) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
    let eU : ρA_HU.Equiv ρA_H :=
      Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
        -- The `ULift` wrapper preserves the subgroup action pointwise.
        ext y
        rfl
    let eInd := ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
    eInd.symm (Representation.IndV.mk H.subtype ρA_H g x) =
      Representation.IndV.mk H.subtype ρA_HU g ⟨x⟩ := by
  letI : Module A A := Semiring.toModule
  letI : Module A (G →₀ A) := Finsupp.module G A
  -- With the coefficient-module instances fixed, the inverse transport on `IndV.mk` is
  -- definitionally the `ULift` source map on the tensor factor.
  dsimp [ind_equiv_of_source_equiv_over_local]

/-- Helper for Theorem 17-17.3-1: the inverse induced-source equivalence for the `ULift` source is
`A`-linear on standard generators, so scalar multiples are carried back coefficientwise as well. -/
theorem induced_source_ulift_equiv_symm_apply_smul_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_H : Representation A H W0)
    (a : A) (g : G) (x : W0) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
    let eU : ρA_HU.Equiv ρA_H :=
      Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
        -- The `ULift` wrapper preserves the subgroup action pointwise.
        ext y
        rfl
    let eInd := ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
    eInd.symm (a • Representation.IndV.mk H.subtype ρA_H g x) =
      a • Representation.IndV.mk H.subtype ρA_HU g ⟨x⟩ := by
  letI : Module A A := Semiring.toModule
  letI : Module A (G →₀ A) := Finsupp.module G A
  -- Multiply the established generator identity by `a`; the only extra bookkeeping is that
  -- `IndV.mk` unfolds to a `Coinvariants` class on both sides.
  simpa [Representation.IndV.mk] using
    congrArg
      (fun y : Representation.IndV H.subtype
          (uliftRepresentation_witness_local (A := A) ρA_H) ↦ a • y)
      (induced_source_ulift_equiv_symm_apply_mk_local
        (A := A) (G := G) (ρA_H := ρA_H) g x)



end

end Representation
