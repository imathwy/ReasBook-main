import Mathlib
import Serre.Chap01.Theorem_1_1_4_2
import Serre.Chap07.Proposition_7_7_1_1
import Serre.Chap07.Proposition_7_7_1_3
import Serre.Chap07.Remark_7_7_1_4
import Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import Serre.Chap08.Corollary_8_8_3_8
import Serre.Chap15.Exercise_15_15_5_3
import Serre.GroupTheory.PSolvable
import Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import Serre.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import Serre.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import Serre.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan

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
noncomputable local instance theorem1731ResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance theorem1731ResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: the raw Chapter `14` residue-field reduction package attached
to a pair of source/target representations, without the extra free/finite hypotheses bundled into
`IsResidueFieldLift`. -/
private abbrev RawIsResidueFieldReduction_local
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
private theorem residueFieldLift_of_equiv_source_local
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
private theorem residueFieldReduction_of_equiv_source_local
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
private theorem residueFieldReduction_of_isBaseChange_isIntertwining
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
private def uliftRepresentation_witness_local
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
private theorem residueFieldLift_ulift_witness_local
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
private noncomputable def subrepresentation_inclusion_hom_generic
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (σ : Representation k G' V')
    (H : Subgroup G')
    (W : Subrepresentation (σ.comp H.subtype)) :
    W.toRepresentation.IntertwiningMap (σ.comp H.subtype) :=
  W.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    W.toRepresentation (σ.comp H.subtype) fun _ _ ↦ rfl

/- Domain-style sampling for Theorem 17-17.3-1:
* primary domain: modular lifting of irreducible representations for finite groups with a cyclic
  normal Hall subgroup and `p`-group quotient;
* relevant owner declarations inspected in this domain:
  `LinearMap.IsResidueFieldReduction`,
  `Representation.IsResidueFieldLift`,
  `Representation.exists_residueFieldLift`,
  `Subgroup.IsComplement'.QuotientMulEquiv`,
  `IsPElementaryDecomposition`;
* best owner abstraction in this file: the source-facing semidirect-product subgroup data
  themselves. The Chapter `15` owners `IsResidueFieldLift` and
  `exists_residueFieldLift` already own the lifting conclusion over a henselian local ring, but no
  earlier project owner packages exactly the present noncentral cyclic-normal-by-`p`-group
  hypotheses without adding extra mathematics.
* primitive data: the normal cyclic Hall subgroup `C`, the `p`-group complement `P`, the
  complement proof `hCP`, and the finite-dimensional residue-field representation `ρ`;
* derived API: the quotient-level fact `IsPGroup p (G ⧸ C)`, obtained canonically from
  `hCP.symm.QuotientMulEquiv`, and the lifting conclusion expressed by `IsResidueFieldLift`.

Source/core/bridge triage:
* source-facing: Serre's cyclic-normal-by-`p`-group semidirect-product lifting criterion;
* core/canonical: `LinearMap.IsResidueFieldReduction` for the reduction map, and
  `Subgroup.IsComplement'` together with `Subgroup.IsComplement'.QuotientMulEquiv` for the
  complementary-subgroup quotient data;
* bridge/view: `Representation.IsResidueFieldLift` for phrasing the conclusion in Serre's
  representation language, together with the quotient `p`-group instance derived from the
  complement data. The theorem keeps the subgroup hypotheses explicit because replacing them by the
  quotient witness would erase part of the source-facing decomposition.

Proof sketch: work in the modular situation where `k = IsLocalRing.ResidueField A` has
characteristic `p` and `A` is henselian local. Decompose the irreducible representation into
`C`-isotypic pieces, reduce by induction on `|G|`, and in the remaining isotypic case construct
the lift from the unramified extension attached to the character field.
-/

/-- Helper for Theorem 17-17.3-1: the subgroup reduction descends directly to the standard
induced restricted-scalars `A`-model by applying `Rep.indMap` to the subgroup reduction morphism.
-/
private noncomputable def induced_subrepresentation_lift_direct
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
private theorem induced_subrepresentation_lift_direct_apply_mk
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
private theorem induced_subrepresentation_lift_direct_apply_induced_generator_local
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
private theorem induced_subrepresentation_lift_direct_isIntertwining_restricted_target_local
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
private theorem induced_subrepresentation_lift_direct_comp_eq_local
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
private noncomputable def comp_subtype_equiv_local
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
private noncomputable def transported_subrepresentation_of_equiv_local
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
private theorem leftQuotientSubmodule_eq_map_of_equiv_local
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype)) (q : G' ⧸ H) :
    ρ₂.leftQuotientSubmodule H
        (transported_subrepresentation_of_equiv_local
          (comp_subtype_equiv_local e H) U) q =
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
private theorem isInducedFromSubrepresentation_of_equiv_local
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype))
    (hU : ρ₁.IsInducedFromSubrepresentation H U) :
    ρ₂.IsInducedFromSubrepresentation H
      (transported_subrepresentation_of_equiv_local
        (comp_subtype_equiv_local e H) U) := by
  classical
  let _ : DecidableEq (G' ⧸ H) := Classical.decEq _
  let U' :=
    transported_subrepresentation_of_equiv_local
      (comp_subtype_equiv_local e H) U
  have hinternal : DirectSum.IsInternal (ρ₁.leftQuotientSubmodule H U) := by
    -- Unpack the Chapter 3 owner so the transport can proceed on the quotient-indexed family.
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  have hleft_fun :
      ρ₂.leftQuotientSubmodule H U' =
        fun q ↦ (ρ₁.leftQuotientSubmodule H U q).map e.toLinearMap := by
    funext q
    simpa [U'] using leftQuotientSubmodule_eq_map_of_equiv_local e H U q
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
private noncomputable def ind_equiv_of_source_equiv_local
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
private noncomputable def ind_equiv_of_source_equiv_over_local
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
private theorem ind_equiv_of_source_equiv_over_local_apply_mk
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
private theorem ind_equiv_of_source_equiv_over_local_apply_smul_mk
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
private theorem induced_source_ulift_equiv_symm_apply_mk_local
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
private theorem induced_source_ulift_equiv_symm_apply_smul_mk_local
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

/-- Helper for Theorem 17-17.3-1: every free finite `A[G]`-representation can be moved to the
same-universe coordinate model `Fin (finrank A W) → A` without changing the action up to
equivalence. -/
private theorem exists_same_universe_finite_free_rep_model_local
    {G' : Type*} [Group G']
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA : Representation A G' W0) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρW : Representation A G' W'),
        Nonempty (ρW.Equiv ρA) := by
  letI : Module A A := Semiring.toModule
  let n := Module.finrank A W0
  let W' : Type u := Fin n → A
  letI : AddCommGroup W' := Pi.addCommGroup
  letI : Module A W' := Pi.Function.module (Fin n) A A
  letI : Module.Free A W' := Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A W' := Module.Finite.of_basis (Pi.basisFun A (Fin n))
  let e : W0 ≃ₗ[A] W' := (Module.finBasis A W0).equivFun
  let ρW : Representation A G' W' :=
    { toFun := fun g ↦ e.conj (ρA g)
      map_one' := by
        -- Conjugation carries the identity action to the coordinate identity operator.
        calc
          e.conj (ρA 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        -- The transported action remains multiplicative after conjugation.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  refine
    ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  apply LinearMap.ext
  intro x
  change e.symm (e (ρA g (e.symm x))) = ρA g (e.symm x)
  simp

/-- Helper for Theorem 17-17.3-1: after induction on the native lifted subgroup carrier, the only
remaining proper-overgroup blocker is a comparison from that native reduced target to the standard
`k`-induced target. Once that comparison is packaged, the native induced source is already the
right `A[G]`-lift before same-universe compression. -/
private noncomputable def induced_subrepresentation_lift_unit_intertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IntertwiningMap
      (((Representation.ind H.subtype W.toRepresentation).restrictScalars A).comp H.subtype) := by
  -- Route correction: before invoking Frobenius reciprocity, package the unit-coset map as an
  -- actual subgroup intertwiner. This isolates the adjunction step from the pointwise proof.
  let f := ((Representation.IndV.mk H.subtype W.toRepresentation 1).restrictScalars A) ∘ₗ red_H
  exact
    LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := ρA_H)
      (σ := (((Representation.ind H.subtype W.toRepresentation).restrictScalars A).comp H.subtype))
      f
    (fun g x ↦
      (induced_subrepresentation_lift_unit_isIntertwining
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH).isIntertwining g x)

/-- Helper for Theorem 17-17.3-1: the packaged unit-coset subgroup intertwiner still sends
`x : W0` to the unit-coset generator with coefficient `red_H x`. -/
private theorem induced_subrepresentation_lift_unit_intertwining_apply_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (x : W0) :
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH x =
        Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H x) := by
  -- The bundled intertwiner was constructed from the explicit unit-coset insertion map.
  change
    (((Representation.IndV.mk H.subtype W.toRepresentation 1).restrictScalars A) ∘ₗ red_H) x =
      Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H x)
  rfl

/-- Helper for Theorem 17-17.3-1: the inverse Frobenius-reciprocity map evaluates on a standard
induced generator by translating the subgroup intertwiner along that generator. -/
private theorem indResHomEquiv_symm_apply_mk_local
    {H' : Type*} [Group H']
    {G' : Type*} [Group G']
    (φ : H' →* G')
    (M : Rep A H')
    (N : Rep A G')
  (f : M ⟶ Rep.res φ N)
  (g : G') (x : M.V) :
    (((Rep.indResHomEquiv φ M N).symm f).hom) (Representation.IndV.mk φ M.ρ g x) =
      N.ρ g⁻¹ (f.hom x) := by
  let inv : Rep.ind φ M ⟶ N := (Rep.indResHomEquiv φ M N).symm f
  have hseed :
      inv.hom (Representation.IndV.mk φ M.ρ 1 x) = f.hom x := by
    have hEq : (Rep.indResHomEquiv φ M N) inv = f :=
      LinearEquiv.apply_symm_apply (Rep.indResHomEquiv φ M N) f
    have htmp :
        (((Rep.indResHomEquiv φ M N) inv).hom) x =
          inv.hom (Representation.IndV.mk φ M.ρ 1 x) := by
      rw [Rep.indResHomEquiv_apply]
      rfl
    simpa [hEq] using htmp.symm
  -- Move the general generator back to the unit-coset seed, then use intertwining.
  calc
    inv.hom (Representation.IndV.mk φ M.ρ g x) =
        inv.hom ((Representation.ind φ M.ρ) g⁻¹ (Representation.IndV.mk φ M.ρ 1 x)) := by
          rw [Representation.ind_mk]
          simp
    _ = N.ρ g⁻¹ (inv.hom (Representation.IndV.mk φ M.ρ 1 x)) := by
        simpa using
          (hom_comm_apply inv g⁻¹ (Representation.IndV.mk φ M.ρ 1 x))
    _ = N.ρ g⁻¹ (f.hom x) := by
        rw [hseed]

/-- Helper for Theorem 17-17.3-1: the Frobenius-induced map built from the `ULift`ed subgroup
source sends each standard induced generator to the corresponding standard target generator with
the coefficient reduced by `red_HU`. -/
private theorem induced_subrepresentation_lift_ulift_source_apply_mk_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (g : G) (xU : ULift.{max (max u v) w} W0) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let fHU :=
      induced_subrepresentation_lift_unit_intertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
      (Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  -- First evaluate the Frobenius-produced map on the generator, then rewrite the packaged unit
  -- intertwiner and the induced action on the standard target.
  calc
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
      (Representation.IndV.mk H.subtype ρA_HU g xU) =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g⁻¹ (fHU xU) := by
          exact
            indResHomEquiv_symm_apply_mk_local
              (A := A) H.subtype (Rep.of ρA_HU)
              (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))
              (Rep.ofHom fHU) g xU
    _ =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g⁻¹
          (Representation.IndV.mk H.subtype W.toRepresentation 1 (red_HU xU)) := by
            rw [induced_subrepresentation_lift_unit_intertwining_apply_local
              (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU]
    _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
          simpa only [Representation.restrictScalars_apply, inv_inv, one_mul] using
            (Representation.ind_mk
              (φ := H.subtype) (ρ := W.toRepresentation) g⁻¹ 1 (red_HU xU))

/-- Helper for Theorem 17-17.3-1: the Frobenius-produced map on the `ULift`ed subgroup source
already intertwines the induced `A[G]`-action with the standard target action. -/
private theorem induced_subrepresentation_lift_ulift_source_isIntertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let fHU :=
      induced_subrepresentation_lift_unit_intertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
    let red_u :
        Representation.IndV H.subtype ρA_HU →ₗ[A]
          Representation.IndV H.subtype W.toRepresentation :=
      (((Rep.indResHomEquiv
          H.subtype (Rep.of ρA_HU)
          (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
        (Rep.ofHom fHU)).hom)
    (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
      ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
      red_u := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  let red_u :
      Representation.IndV H.subtype ρA_HU →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
  refine Representation.IsIntertwiningMap.mk ?_
  intro g v
  -- The induced source is generated by `IndV.mk`, so the generator formula for `red_u` already
  -- determines the whole equivariance statement after repackaging it as a linear-map equality.
  have hcomp :
      red_u ∘ₗ (Representation.ind H.subtype ρA_HU) g =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g ∘ₗ red_u := by
    apply Representation.IndV.hom_ext
    intro g'
    ext xU
    have hmk_mul :
        red_u (Representation.IndV.mk H.subtype ρA_HU (g' * g⁻¹) xU) =
          Representation.IndV.mk H.subtype W.toRepresentation (g' * g⁻¹) (red_HU xU) := by
      simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
        induced_subrepresentation_lift_ulift_source_apply_mk_local
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH (g' * g⁻¹) xU
    have hmk :
        red_u (Representation.IndV.mk H.subtype ρA_HU g' xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g' (red_HU xU) := by
      simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
        induced_subrepresentation_lift_ulift_source_apply_mk_local
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g' xU
    calc
      red_u
          ((Representation.ind H.subtype ρA_HU) g
            (Representation.IndV.mk H.subtype ρA_HU g' xU)) =
        red_u (Representation.IndV.mk H.subtype ρA_HU (g' * g⁻¹) xU) := by
          rw [Representation.ind_mk]
      _ = Representation.IndV.mk H.subtype W.toRepresentation (g' * g⁻¹) (red_HU xU) := by
          exact hmk_mul
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (Representation.IndV.mk H.subtype W.toRepresentation g' (red_HU xU)) := by
              rw [Representation.restrictScalars_apply, Representation.ind_mk]
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
          (red_u (Representation.IndV.mk H.subtype ρA_HU g' xU)) := by
              rw [hmk]
  exact LinearMap.congr_fun hcomp v

/-- Helper for Theorem 17-17.3-1: on pure tensors, the subgroup residue-field lift on the
`ULift`ed source already satisfies the scalar-extension equivariance identity required before
induction. -/
private theorem scalarExtension_source_equiv_tmul_intertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let _ : Module A k := Algebra.toModule
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    ∀ h : H, ∀ z : k, ∀ xU : ULift.{max (max u v) w} W0,
      hLiftHU.1.equiv (((ρA_HU h).baseChange k) (z ⊗ₜ[A] xU)) =
        W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU)) := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  letI : Module A k := Algebra.toModule
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  -- The subgroup reduction already intertwines the `H`-action after passing to `ULift`.
  have hulift_intertwining :
      ∀ h : H, ∀ xU : ULift.{max (max u v) w} W0,
        red_HU (ρA_HU h xU) = (W.toRepresentation.restrictScalars A) h (red_HU xU) := by
    intro h xU
    have hred0 :
        red_H (ρA_H h xU.down) = (W.toRepresentation.restrictScalars A) h (red_H xU.down) := by
      simpa using
        subrepresentation_lift_pointwise
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH h xU.down
    simpa [red_HU, ρA_HU, Representation.restrictScalars_apply] using hred0
  dsimp only
  intro h z xU
  -- Check equivariance on pure tensors, where the base-change action is explicit.
  rw [LinearMap.baseChange_tmul]
  calc
    hLiftHU.1.equiv (z ⊗ₜ[A] (ρA_HU h xU)) = z • red_H ((ρA_HU h xU).down) := by
      simpa using hLiftHU.1.equiv_tmul z (ρA_HU h xU)
    _ = z • red_HU (ρA_HU h xU) := by
      rfl
    _ = z • ((W.toRepresentation.restrictScalars A) h (red_HU xU)) := by
      rw [hulift_intertwining h xU]
    _ = z • (W.toRepresentation h (red_HU xU)) := by
      rfl
    _ = W.toRepresentation h (z • red_HU xU) := by
      simp [smul_assoc]
    _ = W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU)) := by
      rw [hLiftHU.1.equiv_tmul]

/-- Helper for Theorem 17-17.3-1: the subgroup residue-field base-change equivalence already
intertwines the scalar-extended `H`-action on pure tensors, so it is an honest representation
intertwiner. -/
private theorem scalarExtension_source_equiv_isIntertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    (Representation.scalarExtension ρA_HU).IsIntertwiningMap
      W.toRepresentation hLiftHU.1.equiv.toLinearMap := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  refine Representation.IsIntertwiningMap.mk ?_
  intro h
  intro v
  -- On pure tensors, the packaged base-change equivalence is exactly the previously proved
  -- scalar-extension intertwining identity.
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro z xU
    change hLiftHU.1.equiv (((ρA_HU h).baseChange k) (z ⊗ₜ[A] xU)) =
        W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU))
    simpa [ρA_HU, hLiftHU] using
      scalarExtension_source_equiv_tmul_intertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH h z xU
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Theorem 17-17.3-1: the pure-tensor intertwining identity packages the subgroup
scalar extension into an honest `H`-equivariant source equivalence. -/
private noncomputable abbrev scalarExtension_source_equiv_of_residueFieldLift_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  let hInter :=
    scalarExtension_source_equiv_isIntertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  Representation.Equiv.mk hLiftHU.1.equiv
    (fun h ↦ LinearMap.ext fun v ↦ hInter.isIntertwining h v)

/-- Helper for Theorem 17-17.3-1: scalar extension carries the `A`-valued finitely supported
coefficient functions in the induced source to the corresponding `k`-valued functions. -/
private noncomputable abbrev induced_scalarExtension_coeff_equiv_local :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    TensorProduct A k (G →₀ A) ≃ₗ[k] (G →₀ k) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  simpa using (TensorProduct.finsuppScalarRight A k k G)

/-- Helper for Theorem 17-17.3-1: on a single-supported coefficient tensor, the coefficient
transport is exactly the expected residue-field scalar on that support point. -/
private theorem induced_scalarExtension_coeff_equiv_tmul_single_local
    (z : k) (g : G) (a : A) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    induced_scalarExtension_coeff_equiv_local (z ⊗ₜ[A] Finsupp.single g a) =
        Finsupp.single g ((algebraMap A k a) * z) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  ext g'
  by_cases h : g' = g
  · -- On the support point, the transport is just the scalar action of `a` on `z`.
    simpa [h, Algebra.smul_def] using
      (TensorProduct.finsuppScalarRight_apply_tmul_apply
        (R := A) (S := k) (M := k) (ι := G)
        (m := z) (p := Finsupp.single g a) (i := g'))
  · -- Away from the support, both finitely supported functions vanish.
    simpa [h] using
      (TensorProduct.finsuppScalarRight_apply_tmul_apply
        (R := A) (S := k) (M := k) (ι := G)
        (m := z) (p := Finsupp.single g a) (i := g'))

/-- Helper for Theorem 17-17.3-1: the coefficient transport sends the standard induced basis
coefficient `single g 1` to the corresponding residue-field basis coefficient. -/
private theorem induced_scalarExtension_coeff_equiv_tmul_single_one_local
    (z : k) (g : G) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    induced_scalarExtension_coeff_equiv_local (z ⊗ₜ[A] Finsupp.single g (1 : A)) =
        Finsupp.single g z := by
  -- Specialize the general coefficient formula to the unit coefficient used by `IndV.mk`.
  simpa using
    induced_scalarExtension_coeff_equiv_tmul_single_local
      (A := A) (G := G) z g (1 : A)

/-- Helper for Theorem 17-17.3-1: the inverse coefficient transport rewrites a residue-field basis
coefficient as the corresponding pure tensor over `A`. -/
private theorem induced_scalarExtension_coeff_equiv_symm_single_local
    (z : k) (g : G) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    (induced_scalarExtension_coeff_equiv_local (A := A) (G := G)).symm (Finsupp.single g z) =
        z ⊗ₜ[A] Finsupp.single g (1 : A) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  -- Apply the already established forward formula and solve by injectivity of the equivalence.
  apply (induced_scalarExtension_coeff_equiv_local (A := A) (G := G)).injective
  simpa using
    induced_scalarExtension_coeff_equiv_tmul_single_one_local
      (A := A) (G := G) z g

/-- Helper for Theorem 17-17.3-1: before descending to `Coinvariants`, the scalar extension of the
raw induced source is canonically identified with the raw induced source of the scalar-extended
representation. -/
private noncomputable def induced_scalarExtension_source_raw_tensor_equiv_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct A k (TensorProduct A (G →₀ A) W0) ≃ₗ[k]
      TensorProduct k (G →₀ k) (TensorProduct A k W0) := by
  let _ : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (G →₀ k) := Finsupp.module G k
  let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let X := TensorProduct A (G →₀ A) W0
  let e0 :
      TensorProduct A k X ≃ₗ[k] TensorProduct k k (TensorProduct A k X) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k k X).symm
  let e1 :
      TensorProduct k k (TensorProduct A k X) ≃ₗ[k] TensorProduct A (TensorProduct k k k) X :=
    (TensorProduct.AlgebraTensorModule.assoc A k k k k X).symm
  let e2 :
      TensorProduct A (TensorProduct k k k) X ≃ₗ[k]
        TensorProduct k (TensorProduct A k (G →₀ A)) (TensorProduct A k W0) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm A A k k k (G →₀ A) k W0).symm
  let e3 :
      TensorProduct k (TensorProduct A k (G →₀ A)) (TensorProduct A k W0) ≃ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0) :=
    TensorProduct.congr
      (induced_scalarExtension_coeff_equiv_local (A := A) (G := G))
      (LinearEquiv.refl k (TensorProduct A k W0))
  simpa [X] using (((e0.trans e1).trans e2).trans e3)

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport is the forward linear map of
the pre-coinvariants scalar-extension/source equivalence. -/
private noncomputable abbrev induced_scalarExtension_source_hom_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
      TensorProduct k (G →₀ k) (TensorProduct A k W0) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  exact
    (induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)).toLinearMap

/-- Helper for Theorem 17-17.3-1: the raw inverse tensor transport is the inverse linear map of
the pre-coinvariants scalar-extension/source equivalence. -/
private noncomputable abbrev induced_scalarExtension_source_inv_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
      TensorProduct A k (TensorProduct A (G →₀ A) W0) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  exact
    (induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)).symm.toLinearMap

/-- Helper for Theorem 17-17.3-1: on the standard pure tensor corresponding to `IndV.mk`, the raw
forward transport only moves the coefficient function across scalar extension. -/
private theorem induced_scalarExtension_source_hom_apply_basis_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (W0 := W0)
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] x)) =
      (Finsupp.single g z) ⊗ₜ[k] (1 ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- Unfold the explicit raw comparison and rewrite each tensor reassociation on the chosen basis
  -- tensor. The only genuine content is the coefficient-transport formula.
  simp [induced_scalarExtension_source_hom_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_apply_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]

/-- Helper for Theorem 17-17.3-1: the raw inverse transport sends a scalar-extended basis tensor
back to the corresponding pure tensor over `A`. -/
private theorem induced_scalarExtension_source_inv_apply_basis_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_inv_local
        (W0 := W0)
        ((Finsupp.single g z) ⊗ₜ[k] (1 ⊗ₜ[A] x)) =
      z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- The inverse composite first rewrites the coefficient basis vector back to a pure tensor, then
  -- cancels the auxiliary base change and reassociates the tensor factors back to the source.
  simp [induced_scalarExtension_source_inv_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_symm_apply_single,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul]

/-- Helper for Theorem 17-17.3-1: on a single-supported coefficient tensor with arbitrary
coefficient, the raw forward transport rewrites only the coefficient function and leaves the source
vector untouched. This is the coefficient-level step still needed in the quotient descent. -/
private theorem induced_scalarExtension_source_hom_apply_single_local
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (a : A) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0)
        (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] x)) =
      (Finsupp.single g ((algebraMap A k a) * z)) ⊗ₜ[k] (1 ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- Unfold the raw comparison once; the only nontrivial step is the already isolated coefficient
  -- transport on the singleton basis vector.
  simp [induced_scalarExtension_source_hom_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_apply_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]
  simpa [Algebra.smul_def]

/-- Helper for Theorem 17-17.3-1: the scalar-extended source action on a singleton-supported pure
tensor is already the translated singleton formula from Serre's induced-model relation. -/
private theorem induced_scalarExtension_source_sourceAct_apply_single_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (z : k) (g : G) (a : A) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let sourceAct :=
      (Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h
    sourceAct (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU)) =
      z ⊗ₜ[A] ((Finsupp.single ((h : G) * g) a) ⊗ₜ[A] (ρA_HU h xU)) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  -- Normalize the scalar-extended source action before applying the raw tensor transport.
  change
    (((Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU) h).baseChange
      k) (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU)) =
      z ⊗ₜ[A] ((Finsupp.single ((h : G) * g) a) ⊗ₜ[A] (ρA_HU h xU))
  rw [LinearMap.baseChange_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
  simp [Representation.ofMulAction_single]

/-- Helper for Theorem 17-17.3-1: the target induced action on a singleton-supported pure tensor
is the translated singleton formula after scalar extension on the subgroup source. -/
private theorem induced_scalarExtension_source_targetAct_apply_single_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (c : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let targetAct :=
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h
    targetAct ((Finsupp.single g c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] xU)) =
      (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] (ρA_HU h xU)) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  -- Normalize the target action directly on the singleton-supported tensor.
  change
    (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h)
      ((Finsupp.single g c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] xU)) =
        (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] (ρA_HU h xU))
  rw [Representation.tprod_apply, TensorProduct.map_tmul]
  simp [Representation.ofMulAction_single]
  have hbase :
      (ρA_HU.scalarExtension h) ((1 : k) ⊗ₜ[A] xU) = (1 : k) ⊗ₜ[A] (ρA_HU h xU) := by
    change ((ρA_HU h).baseChange k) ((1 : k) ⊗ₜ[A] xU) = (1 : k) ⊗ₜ[A] (ρA_HU h xU)
    rw [LinearMap.baseChange_tmul]
  exact congrArg (fun y ↦ (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] y) hbase

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport already commutes with the
singleton-supported induction relation on arbitrary coefficients. This is the generator-level
compatibility needed before descending through coinvariants. -/
private theorem induced_scalarExtension_source_hom_commutes_on_single_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (z : k) (g : G) (a : A) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let sourceAct :=
      (Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h
    let targetAct :=
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0)
        (sourceAct (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU))) =
      targetAct
        (induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0)
          (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU))) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  let _ := sourceAct
  let _ := targetAct
  dsimp only [sourceAct, targetAct]
  -- First normalize the source action, then apply the already-proved raw singleton transport.
  rw [induced_scalarExtension_source_sourceAct_apply_single_local
    (A := A) (G := G) (ρA_HU := ρA_HU)]
  rw [induced_scalarExtension_source_hom_apply_single_local
    (A := A) (G := G) (W0 := W0)]
  -- Normalize the target action on the transported singleton tensor; both sides are now identical.
  rw [induced_scalarExtension_source_hom_apply_single_local
    (A := A) (G := G) (W0 := W0)]
  rw [induced_scalarExtension_source_targetAct_apply_single_local
    (A := A) (G := G) (ρA_HU := ρA_HU)]

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport respects the full induction
relation, so it can be descended through `Representation.Coinvariants.map`. -/
private theorem induced_scalarExtension_source_hom_rel_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0) ∘ₗ
      ((Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h) =
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Representation.scalarExtension ρA_HU) h ∘ₗ
        induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  -- Extend the singleton commutation relation first across coefficient sums, then across both
  -- tensor factors, so the map descends through the full induction relation.
  apply LinearMap.ext
  intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp [sourceAct, targetAct]
  · intro z y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [sourceAct, targetAct]
    · intro f xU
      induction f using Finsupp.induction_linear with
      | zero =>
          simp [sourceAct, targetAct]
      | add f₁ f₂ hf₁ hf₂ =>
          calc
            (induced_scalarExtension_source_hom_local
                  (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
                (z ⊗ₜ[A] ((f₁ + f₂) ⊗ₜ[A] xU)) =
              (induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
                  (z ⊗ₜ[A] ((f₁ ⊗ₜ[A] xU) + (f₂ ⊗ₜ[A] xU))) := by
                    rw [TensorProduct.add_tmul]
            _ =
              (induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
                  ((z ⊗ₜ[A] (f₁ ⊗ₜ[A] xU)) + (z ⊗ₜ[A] (f₂ ⊗ₜ[A] xU))) := by
                    rw [TensorProduct.tmul_add]
            _ =
              (induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
                  (z ⊗ₜ[A] (f₁ ⊗ₜ[A] xU)) +
                (induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
                  (z ⊗ₜ[A] (f₂ ⊗ₜ[A] xU)) := by
                    simp [map_add]
            _ =
              (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0))
                  (z ⊗ₜ[A] (f₁ ⊗ₜ[A] xU)) +
                (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                    (A := A) (G := G) (W0 := W0))
                  (z ⊗ₜ[A] (f₂ ⊗ₜ[A] xU)) := by
                    rw [hf₁, hf₂]
            _ =
              (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                  (A := A) (G := G) (W0 := W0))
                ((z ⊗ₜ[A] (f₁ ⊗ₜ[A] xU)) + (z ⊗ₜ[A] (f₂ ⊗ₜ[A] xU))) := by
                  symm
                  simp [map_add]
            _ =
              (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                  (A := A) (G := G) (W0 := W0))
                (z ⊗ₜ[A] ((f₁ ⊗ₜ[A] xU) + (f₂ ⊗ₜ[A] xU))) := by
                  rw [TensorProduct.tmul_add]
            _ =
              (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                  (A := A) (G := G) (W0 := W0))
                (z ⊗ₜ[A] ((f₁ + f₂) ⊗ₜ[A] xU)) := by
                  rw [TensorProduct.add_tmul]
      | single g a =>
          simpa [sourceAct, targetAct] using
            induced_scalarExtension_source_hom_commutes_on_single_local
              (A := A) (G := G) (ρA_HU := ρA_HU) h z g a xU
    · intro y₁ y₂ hy₁ hy₂
      calc
        (induced_scalarExtension_source_hom_local
              (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
            (z ⊗ₜ[A] (y₁ + y₂)) =
          (induced_scalarExtension_source_hom_local
                (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
              (z ⊗ₜ[A] y₁) +
            (induced_scalarExtension_source_hom_local
                (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct)
              (z ⊗ₜ[A] y₂) := by
                simp [TensorProduct.tmul_add, map_add]
        _ =
          (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                (A := A) (G := G) (W0 := W0))
              (z ⊗ₜ[A] y₁) +
            (targetAct ∘ₗ induced_scalarExtension_source_hom_local
                (A := A) (G := G) (W0 := W0))
              (z ⊗ₜ[A] y₂) := by
                rw [hy₁, hy₂]
        _ =
          (targetAct ∘ₗ induced_scalarExtension_source_hom_local
              (A := A) (G := G) (W0 := W0))
            (z ⊗ₜ[A] (y₁ + y₂)) := by
              symm
              simp [TensorProduct.tmul_add, map_add]
  · intro v₁ v₂ hv₁ hv₂
    simp [map_add, hv₁, hv₂, sourceAct, targetAct]

/-- Helper for Theorem 17-17.3-1: once the raw forward tensor transport is known to commute with
the induction relation, the inverse map inherits the same compatibility by transport through the
raw tensor equivalence. -/
private theorem induced_scalarExtension_source_inv_rel_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_inv_local
        (A := A) (G := G) (W0 := W0) ∘ₗ
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Representation.scalarExtension ρA_HU) h =
      ((Representation.scalarExtension
          (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h) ∘ₗ
        induced_scalarExtension_source_inv_local
          (A := A) (G := G) (W0 := W0) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let rawHom :=
    induced_scalarExtension_source_hom_local (A := A) (G := G) (W0 := W0)
  let rawInv :=
    induced_scalarExtension_source_inv_local (A := A) (G := G) (W0 := W0)
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  let _ := rawHom
  let _ := rawInv
  let _ := sourceAct
  let _ := targetAct
  -- Conjugate the forward relation through the raw tensor equivalence instead of normalizing the
  -- inverse action separately.
  apply LinearMap.ext
  intro v
  let rawEquiv :=
    induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)
  apply rawEquiv.injective
  have hforward :
      rawHom (sourceAct (rawInv v)) = targetAct (rawHom (rawInv v)) := by
    simpa [rawHom, sourceAct, targetAct] using
      LinearMap.congr_fun
        (induced_scalarExtension_source_hom_rel_local
          (A := A) (G := G) (ρA_HU := ρA_HU) h)
        (rawInv v)
  calc
    rawHom (rawInv (targetAct v)) = targetAct v := by
      simp [rawHom, rawInv]
    _ = targetAct (rawHom (rawInv v)) := by
      simp [rawHom, rawInv]
    _ = rawHom (sourceAct (rawInv v)) := hforward.symm

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, avoiding the earlier transport-heavy `range = ker` detour. -/
private theorem scalarExtension_induced_source_coinvariants_forward_apply_act_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ y : TensorProduct A (G →₀ A) W0,
      Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (ρrawA h y)) =
        Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : IsScalarTower A k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro z y
        simp [IsLocalRing.ResidueField.algebraMap_eq, Algebra.smul_def, TensorProduct.smul_tmul']
      · intro x₁ x₂ hx₁ hx₂
        have hx₁' : (IsLocalRing.residue A a) • x₁ = a • x₁ := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx₁
        have hx₂' : (IsLocalRing.residue A a) • x₂ = a • x₂ := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx₂
        rw [smul_add, smul_add, hx₁, hx₂]
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Route correction: normalize the scalar-extended action on `z ⊗ y` before applying the
  -- coinvariants quotient relation, rather than transporting through a `range = ker` equality.
  change ∀ y : TensorProduct A (G →₀ A) W0,
      Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (ρrawA h y)) =
        Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)
  intro y
  -- The scalar extension action is the base-changed raw action, so `baseChange_tmul` rewrites the
  -- left side into the canonical orbit representative killed by `mk_self_apply`.
  rw [← LinearMap.baseChange_tmul (f := ρrawA h) (A := k) z y]
  exact Representation.Coinvariants.mk_self_apply sourceScalarρ h (z ⊗ₜ[A] y)

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, avoiding the earlier transport-heavy `range = ker` detour. -/
private noncomputable def scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    TensorProduct A (G →₀ A) W0 →ₗ[A] Representation.Coinvariants sourceScalarρ := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Package the raw map `y ↦ [z ⊗ y]` as an explicit composition so Lean never has to infer the
  -- inner `A`-linearity from an anonymous lambda.
  refine
    { toFun := fun y ↦ Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)
      map_add' := by
        intro y₁ y₂
        simp [TensorProduct.tmul_add]
      map_smul' := by
        intro a y
        show
          Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (a • y)) =
            Representation.Coinvariants.mk sourceScalarρ (((a • z : k)) ⊗ₜ[A] y)
        exact congrArg (Representation.Coinvariants.mk sourceScalarρ)
          (TensorProduct.tmul_smul a z y) }

/-- Helper for Theorem 17-17.3-1: for fixed `z`, the raw map `y ↦ [z ⊗ y]` descends through the
induction coinvariants quotient because the scalar-extended action preserves those classes. -/
private noncomputable def scalarExtension_induced_source_coinvariants_forward_fixed_z_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ρrawA.Coinvariants →ₗ[A] sourceScalarρ.Coinvariants := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Descend the fixed-`z` raw map once; the needed relation is exactly the generator equality
  -- proved in `scalarExtension_induced_source_coinvariants_forward_apply_act_local`.
  exact
    Representation.Coinvariants.lift ρrawA
      (scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local
        (A := A) (G := G) (ρA_HU := ρA_HU) z)
      (fun h ↦ by
        apply TensorProduct.ext'
        intro f xU
        simpa [scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local,
          LinearMap.comp_apply] using
          scalarExtension_induced_source_coinvariants_forward_apply_act_local
            (A := A) (G := G) (ρA_HU := ρA_HU) z h ((f : G →₀ A) ⊗ₜ[A] xU))

/-- Helper for Theorem 17-17.3-1: on standard induced generators, the fixed-`z` descended map is
exactly Serre's class `[(z ⊗ single g ⊗ x)]`. -/
private theorem scalarExtension_induced_source_coinvariants_forward_fixed_z_apply_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU z
        (Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Evaluate the quotient lift on the canonical induced generator and then unfold the fixed-`z`
  -- wrapper only once.
  simp [scalarExtension_induced_source_coinvariants_forward_fixed_z_local,
    scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local,
    Representation.IndV.mk, LinearMap.comp_apply]

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, with the outer scalar handled by base change of the fixed-`1` quotient
map. -/
private noncomputable def scalarExtension_induced_source_coinvariants_forward_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    TensorProduct A k (Representation.IndV H.subtype ρA_HU) →ₗ[k]
      Representation.Coinvariants sourceScalarρ := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Route correction: first descend the fixed-`1` raw map, then let `liftBaseChange` handle the
  -- outer scalar variable. This keeps the source proof's quotient map while avoiding the failed
  -- anonymous-lambda elaboration path.
  exact
    (scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)).liftBaseChange k

/-- Helper for Theorem 17-17.3-1: on pure tensors, the forward map is Serre's formula
`z ⊗ [x] ↦ [z ⊗ x]`. -/
private theorem scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_forward_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Evaluate the base-changed fixed-`1` quotient map on the pure tensor, then rewrite the outer
  -- scalar as a scalar on the raw tensor representative.
  calc
    scalarExtension_induced_source_coinvariants_forward_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)
        =
      z •
        scalarExtension_induced_source_coinvariants_forward_fixed_z_local
          (A := A) (G := G) (ρA_HU := ρA_HU) (1 : k)
          (Representation.IndV.mk H.subtype ρA_HU g xU) := by
            simp [scalarExtension_induced_source_coinvariants_forward_local,
              LinearMap.liftBaseChange_tmul]
    _ =
      z • Representation.Coinvariants.mk sourceScalarρ
        ((1 : k) ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
          rw [scalarExtension_induced_source_coinvariants_forward_fixed_z_apply_mk_local
            (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ =
      Representation.Coinvariants.mk sourceScalarρ
        (z • ((1 : k) ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          rw [← (Representation.Coinvariants.mk sourceScalarρ).map_smul]
    _ =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
          congr 1
          simpa [one_mul] using
            (TensorProduct.smul_tmul' z (1 : k)
              (((Finsupp.single g (1 : A)) ⊗ₜ[A] xU) :
                TensorProduct A (G →₀ A) W0))

/-
The duplicate induced-lift packaging block that was previously inlined here has been replaced
 by the split support owner `Serre.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift`. Keeping
 the old local copy caused multiple elaboration timeouts without changing the final proof route. -/
/-
private theorem scalarExtension_induced_source_coinvariants_backward_invariant_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ h : H,
      ((Representation.Coinvariants.mk ρrawA).baseChange k) ∘ₗ sourceScalarρ h =
        (Representation.Coinvariants.mk ρrawA).baseChange k := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  intro h
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp [LinearMap.comp_apply]
  · intro z y
    -- Normalize the scalar-extended action to `z ⊗ ρrawA h y`, then apply the raw coinvariants
    -- relation before base change.
    change
      ((Representation.Coinvariants.mk ρrawA).baseChange k)
          (z ⊗ₜ[A] (ρrawA h y)) =
        ((Representation.Coinvariants.mk ρrawA).baseChange k) (z ⊗ₜ[A] y)
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    exact congrArg (fun t ↦ z ⊗ₜ[A] t)
      (Representation.Coinvariants.mk_self_apply ρrawA h y)
  · intro t₁ t₂ ht₁ ht₂
    simp [LinearMap.comp_apply, map_add, ht₁, ht₂]

/- Helper for Theorem 17-17.3-1: the inverse quotient map descends the base-changed quotient map
`k ⊗ mk : k ⊗ X → k ⊗ X_G`, again using only the universal property of `Coinvariants`. -/
set_option maxHeartbeats 4000000 in
private noncomputable def scalarExtension_induced_source_coinvariants_backward_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    Representation.Coinvariants sourceScalarρ →ₗ[k]
      TensorProduct A k (Representation.IndV H.subtype ρA_HU) :=
  by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Descend the base-changed quotient map once; the relation is exactly the pure-tensor
  -- compatibility proved above.
  exact
    Representation.Coinvariants.lift sourceScalarρ
      ((Representation.Coinvariants.mk ρrawA).baseChange k)
      (scalarExtension_induced_source_coinvariants_backward_invariant_local ρA_HU)

/-- Helper for Theorem 17-17.3-1: on raw tensor classes, the backward map is the obvious
base-changed quotient map `[(z ⊗ y)] ↦ z ⊗ [y]`. -/
private theorem scalarExtension_induced_source_coinvariants_backward_apply_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
      scalarExtension_induced_source_coinvariants_backward_local ρA_HU
          (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)) =
        z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  intro z y
  -- Evaluate the descended quotient lift on the raw tensor representative and unfold the
  -- base-changed quotient map once.
  simp [scalarExtension_induced_source_coinvariants_backward_local, LinearMap.baseChange_tmul]

/-- Helper for Theorem 17-17.3-1: scalar extension commutes with the induction coinvariants
quotient, expressed directly as a linear equivalence rather than through a submodule equality. -/
private theorem scalarExtension_induced_source_coinvariants_backward_forward_apply_tmul_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- On the standard pure tensors, Serre's forward map and the base-changed quotient map are
  -- visibly inverse after both are rewritten on the canonical raw representative.
  calc
    scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (Representation.Coinvariants.mk sourceScalarρ
          (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
            rw [scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ = z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA
          ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU) := by
            rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ = z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU := by
          rfl

/-- Helper for Theorem 17-17.3-1: scalar extension commutes with the induction coinvariants
quotient, expressed directly as a linear equivalence rather than through a submodule equality. -/
private noncomputable def scalarExtension_induced_source_coinvariants_tensor_equiv_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    TensorProduct A k (Representation.IndV H.subtype ρA_HU) ≃ₗ[k]
      Representation.Coinvariants sourceScalarρ :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  have hfixed_apply_mk :
      ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
            (Representation.Coinvariants.mk ρrawA y) =
          Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y) := by
    intro y
    rfl
  have hforward_backward_mk :
      ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_forward_local
            (A := A) (G := G) (ρA_HU := ρA_HU)
            (scalarExtension_induced_source_coinvariants_backward_local ρA_HU
              (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y))) =
          Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
    intro z y
    -- Rewrite the backward map on the quotient generator, then evaluate the fixed-`1` descended
    -- forward map on the resulting raw coinvariants class.
    calc
      scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (scalarExtension_induced_source_coinvariants_backward_local ρA_HU
            (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y))) =
        scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y) := by
              rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
                (A := A) (G := G) (ρA_HU := ρA_HU)]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
            (Representation.Coinvariants.mk ρrawA y) := by
              simp [scalarExtension_induced_source_coinvariants_forward_local,
                LinearMap.liftBaseChange_tmul]
      _ =
        z • Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y) := by
            rw [hfixed_apply_mk y]
      _ =
        Representation.Coinvariants.mk sourceScalarρ (z • ((1 : k) ⊗ₜ[A] y)) := by
            rw [← (Representation.Coinvariants.mk sourceScalarρ).map_smul]
      _ = Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
            congr 1
            simpa [one_mul] using TensorProduct.smul_tmul' z (1 : k) y
  have hbackward_forward_mk :
      ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (scalarExtension_induced_source_coinvariants_forward_local
              (A := A) (G := G) (ρA_HU := ρA_HU)
              (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y)) =
          z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y := by
    intro z y
    -- The source-side inverse uses the same fixed-`1` quotient map together with the explicit
    -- backward formula on raw tensor classes.
    calc
      scalarExtension_induced_source_coinvariants_backward_local
          ρA_HU
          (scalarExtension_induced_source_coinvariants_forward_local
            (A := A) (G := G) (ρA_HU := ρA_HU)
            (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y)) =
      scalarExtension_induced_source_coinvariants_backward_local
          ρA_HU
          (z •
            scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
              (Representation.Coinvariants.mk ρrawA y)) := by
              simp [scalarExtension_induced_source_coinvariants_forward_local,
                LinearMap.liftBaseChange_tmul]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
              (Representation.Coinvariants.mk ρrawA y)) := by
                rw [map_smul]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y)) := by
                rw [hfixed_apply_mk y]
      _ = z • ((1 : k) ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y) := by
            rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
      _ = z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y := by
            simpa [one_mul] using
              (TensorProduct.smul_tmul' z (1 : k)
                (Representation.Coinvariants.mk ρrawA y))
  -- Route correction: package the already-defined Serre forward/backward quotient maps, and
  -- discharge the inverse laws separately on tensor generators and quotient generators.
  refine LinearEquiv.ofLinear
    (scalarExtension_induced_source_coinvariants_forward_local
      (A := A) (G := G) (ρA_HU := ρA_HU))
    (scalarExtension_induced_source_coinvariants_backward_local ρA_HU)
    ?_ ?_
  · -- Check the quotient-side inverse on raw tensor classes, then descend by the coinvariants
    -- universal property.
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [LinearMap.comp_apply]
    · intro z y
      simpa [LinearMap.comp_apply] using
        hforward_backward_mk z y
    · intro t₁ t₂ ht₁ ht₂
      simp [LinearMap.comp_apply, map_add, ht₁, ht₂]
  · -- Check the tensor-side inverse on pure tensors, then reduce the coinvariants factor to the
    -- standard `IndV.mk` generators.
    apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [LinearMap.comp_apply]
    · intro z v
      refine Representation.Coinvariants.induction_on (ρ := ρrawA) v ?_
      intro y
      simpa [LinearMap.comp_apply] using hbackward_forward_mk z y
    · intro t₁ t₂ ht₁ ht₂
      simp [LinearMap.comp_apply, map_add, ht₁, ht₂]

/-- Helper for Theorem 17-17.3-1: descending the raw tensor equivalence through the induction
relation gives the quotient-level comparison used in the proper-overgroup branch. -/
private noncomputable def induced_scalarExtension_source_coinvariants_equiv_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A k := Algebra.toModule;
    let _ : Module k k := Semiring.toModule;
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule;
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule;
    (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) ≃ₗ[k]
      (Representation.IndV H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU)) :=
  by
    letI : Module A k := Algebra.toModule
    letI : Module k k := Semiring.toModule
    letI : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    letI : Module k (G →₀ k) := Finsupp.module G k
    letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let rawCoinvEquiv :
        Representation.Coinvariants
            (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
              Representation.scalarExtension
                (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) ≃ₗ[k]
          Representation.IndV H.subtype
            (show Representation k H (TensorProduct A k W0) from
              Representation.scalarExtension ρA_HU) := by
      -- Route correction: descend the already-proved raw tensor transport instead of rebuilding
      -- the quotient comparison from scratch.
      let rawHom :
          Representation.Coinvariants
              (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
                Representation.scalarExtension
                  (Representation.tprod ((Representation.leftRegular A G).comp H.subtype)
                    ρA_HU)) →ₗ[k]
            Representation.IndV H.subtype
              (show Representation k H (TensorProduct A k W0) from
                Representation.scalarExtension ρA_HU) :=
        Representation.Coinvariants.map _ _
          (induced_scalarExtension_source_hom_local
            (A := A) (G := G) (W0 := W0))
          (induced_scalarExtension_source_hom_rel_local
            (A := A) (G := G) (ρA_HU := ρA_HU))
      let rawInv :
          Representation.IndV H.subtype
              (show Representation k H (TensorProduct A k W0) from
                Representation.scalarExtension ρA_HU) →ₗ[k]
            Representation.Coinvariants
              (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
                Representation.scalarExtension
                  (Representation.tprod ((Representation.leftRegular A G).comp H.subtype)
                    ρA_HU)) :=
        Representation.Coinvariants.map _ _
          (induced_scalarExtension_source_inv_local
            (A := A) (G := G) (W0 := W0))
          (induced_scalarExtension_source_inv_rel_local
            (A := A) (G := G) (ρA_HU := ρA_HU))
      -- The descended forward and inverse maps remain inverse because the raw maps already were.
      refine LinearEquiv.ofLinear rawHom rawInv ?_ ?_
      · ext x
        simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
      · ext x
        simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
    -- Compose the direct scalar-extension/coinvariants bridge with the descended raw
    -- coinvariants equivalence in the same order as Serre's source proof.
    exact
      (scalarExtension_induced_source_coinvariants_tensor_equiv_local
          (A := A) (G := G) (ρA_HU := ρA_HU)).trans
        rawCoinvEquiv

/-- Helper for Theorem 17-17.3-1: on standard generators, the direct scalar-extension/coinvariants
equivalence sends `1 ⊗ IndV.mk g x` to the scalar-extended raw basis class `[(1 ⊗ single g ⊗ x)]`.
-/
private theorem scalarExtension_induced_source_coinvariants_tensor_equiv_apply_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_tensor_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Evaluate the packaged equivalence on the standard generator by unfolding only its forward
  -- half, which was already computed on pure tensors.
  simpa [scalarExtension_induced_source_coinvariants_tensor_equiv_local] using
    scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
      (A := A) (G := G) (ρA_HU := ρA_HU) (1 : k) g xU

/-- Helper for Theorem 17-17.3-1: on standard generators, the descended scalar-extension/source
equivalence carries the induced source basis vector to the corresponding scalar-extended basis
vector. -/
private theorem induced_scalarExtension_source_coinvariants_equiv_apply_mk_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (g : G) (xU : W0) :
    let _ : Module A k := Algebra.toModule;
    let _ : Module k k := Semiring.toModule;
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule;
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule;
    induced_scalarExtension_source_coinvariants_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.IndV.mk H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU) g
        (1 ⊗ₜ[A] xU) := by
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  let targetρ :
      Representation k H (TensorProduct k (G →₀ k) (TensorProduct A k W0)) :=
    Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)
  let tensorEquiv :=
    scalarExtension_induced_source_coinvariants_tensor_equiv_local
      (A := A) (G := G) (ρA_HU := ρA_HU)
  let rawMap :
      Representation.Coinvariants sourceScalarρ →ₗ[k]
        Representation.IndV H.subtype
          (show Representation k H (TensorProduct A k W0) from
            Representation.scalarExtension ρA_HU) :=
    Representation.Coinvariants.map _ _
      (induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0))
      (induced_scalarExtension_source_hom_rel_local
        (A := A) (G := G) (ρA_HU := ρA_HU))
  -- Rewrite the generator directly through the new tensor/coinvariants equivalence, then apply
  -- the already-closed raw generator formula.
  change rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
    Representation.IndV.mk H.subtype
      (show Representation k H (TensorProduct A k W0) from
        Representation.scalarExtension ρA_HU) g
      (1 ⊗ₜ[A] xU)
  calc
    rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      rawMap (Representation.Coinvariants.mk sourceScalarρ
        (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          rw [scalarExtension_induced_source_coinvariants_tensor_equiv_apply_mk_local
            (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ =
      Representation.Coinvariants.mk targetρ
        (induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0)
          (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          simp [rawMap, targetρ]
    _ =
      Representation.Coinvariants.mk targetρ
        ((Finsupp.single g (1 : k)) ⊗ₜ[k] (1 ⊗ₜ[A] xU)) := by
          rw [induced_scalarExtension_source_hom_apply_basis_local
            (A := A) (G := G) (W0 := W0)]
    _ =
      Representation.IndV.mk H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU) g
        (1 ⊗ₜ[A] xU) := by
          rfl

/-- Helper for Theorem 17-17.3-1: the subgroup scalar-extension/source equivalence sends the pure
tensor `1 ⊗ xU` to the reduced coefficient `red_HU xU`. -/
private theorem scalarExtension_source_equiv_apply_one_tmul_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (xU : ULift.{max (max u v) w} W0) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    let eHU :
        (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
      scalarExtension_source_equiv_of_residueFieldLift_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
    eHU (1 ⊗ₜ[A] xU) = red_HU xU := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  let eHU :
      (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
    scalarExtension_source_equiv_of_residueFieldLift_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  -- This is exactly the coefficient-level bridge coming from the subgroup residue-field lift.
  simpa [eHU, scalarExtension_source_equiv_of_residueFieldLift_local, ρA_HU, red_HU, hLiftHU] using
    hLiftHU.1.equiv_tmul (1 : k) xU

/-- Helper for Theorem 17-17.3-1: after the generator formula is fixed, the remaining proper-
overgroup gap is the universal-property proof that the Frobenius-induced `ULift`-source map is a
genuine base change. -/
theorem induced_subrepresentation_lift_ulift_source_isBaseChange_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (red_u :
        Representation.IndV H.subtype
          (uliftRepresentation_witness_local (A := A) ρA_H) →ₗ[A]
          Representation.IndV H.subtype W.toRepresentation)
    (hred_u :
        ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
          red_u
              (Representation.IndV.mk H.subtype
                (uliftRepresentation_witness_local (A := A) ρA_H) g xU) =
            Representation.IndV.mk H.subtype W.toRepresentation g
              ((red_H.comp
                  (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap) xU)) :
    IsBaseChange k red_u := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
    TensorProduct.leftModule
  let _ : Module k
      (TensorProduct A k
        (Representation.IndV H.subtype (uliftRepresentation_witness_local (A := A) ρA_H))) :=
    TensorProduct.leftModule
  let eHU :
      (Representation.scalarExtension (uliftRepresentation_witness_local (A := A) ρA_H)).Equiv
        W.toRepresentation :=
    scalarExtension_source_equiv_of_residueFieldLift_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let eCanon :
      TensorProduct A k
          (Representation.IndV H.subtype (uliftRepresentation_witness_local (A := A) ρA_H)) ≃ₗ[k]
        Representation.IndV H.subtype W.toRepresentation :=
    (induced_scalarExtension_source_coinvariants_equiv_local
      (A := A) (G := G)
      (ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H)).trans
      ((ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU).toLinearEquiv)
  let redCanon :
      Representation.IndV H.subtype (uliftRepresentation_witness_local (A := A) ρA_H) →ₗ[A]
        Representation.IndV H.subtype W.toRepresentation :=
    (eCanon.toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A k
        (Representation.IndV H.subtype (uliftRepresentation_witness_local (A := A) ρA_H)) 1)
  -- Route correction: freeze Serre's canonical comparison map `x ↦ eCanon (1 ⊗ x)` first, prove
  -- it is the desired base change by `of_equiv`, and only then compare it with the Frobenius map.
  have hCanon : IsBaseChange k redCanon := by
    refine IsBaseChange.of_equiv eCanon ?_
    intro x
    rfl
  have hEq : redCanon = red_u := by
    -- The canonical map and the Frobenius-produced map agree on the standard induced generators,
    -- so `Representation.IndV.hom_ext` upgrades the source-faithful generator computation to a
    -- linear-map equality.
    apply Representation.IndV.hom_ext
    intro g
    ext xU
    calc
      redCanon
          (Representation.IndV.mk H.subtype
            (uliftRepresentation_witness_local (A := A) ρA_H) g xU) =
          eCanon
            (1 ⊗ₜ[A] Representation.IndV.mk H.subtype
              (uliftRepresentation_witness_local (A := A) ρA_H) g xU) := by
            rfl
      _ =
          (ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU)
            (Representation.IndV.mk H.subtype
              (show Representation k H
                  (TensorProduct A k (ULift.{max (max u v) w} W0)) from
                Representation.scalarExtension
                  (uliftRepresentation_witness_local (A := A) ρA_H)) g
              (1 ⊗ₜ[A] xU)) := by
                rw [LinearEquiv.trans_apply]
                rw [induced_scalarExtension_source_coinvariants_equiv_apply_mk_local
                  (A := A) (G := G)
                  (ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H)]
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (eHU (1 ⊗ₜ[A] xU)) := by
            rw [ind_equiv_of_source_equiv_over_local_apply_mk]
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
            rw [scalarExtension_source_equiv_apply_one_tmul_local
              (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
      _ =
          red_u
            (Representation.IndV.mk H.subtype ρA_HU g xU) := by
            symm
            simpa [ρA_HU, red_HU] using hred_u g xU
  rw [hEq] at hCanon
  exact hCanon
/-- Helper for Theorem 17-17.3-1: evaluating a coinduced function on inverse representatives
identifies the coinduced model over a commutative ring with functions on a finite left
transversal. -/
private noncomputable def coind_representative_equiv_local
    {H : Subgroup G}
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    (ρA_H : Representation A H W0)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G)) :
    Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W0) where
  toFun f r := f.1 ((r : G)⁻¹)
  invFun ξ :=
    ⟨fun g ↦
        let x := hR.equiv g⁻¹
        ρA_H x.2⁻¹ (ξ x.1), by
        intro h g
        -- Move the subgroup factor in the complement decomposition to the coefficient action.
        simpa [mul_assoc, ← Module.End.mul_apply, ← map_mul] using
          congrArg
            (fun x : ↥(R : Set G) × H ↦ ρA_H x.2⁻¹ (ξ x.1))
            (hR.equiv_mul_right g⁻¹ h⁻¹)⟩
  map_add' _ _ := by
    ext r
    simp
  map_smul' _ _ := by
    ext r
    simp
  left_inv f := by
    ext g
    let x := hR.equiv g⁻¹
    have hg : ((x.2 : H) : G)⁻¹ * ((x.1 : (R : Set G)) : G)⁻¹ = g := by
      simpa [x, mul_inv_rev] using congrArg Inv.inv (hR.equiv_fst_mul_equiv_snd g⁻¹)
    -- Rewrite `g` through the complement decomposition of `g⁻¹`.
    change ρA_H x.2⁻¹ (f.1 (((x.1 : ↥(R : Set G)) : G)⁻¹)) = f.1 g
    simpa [hg] using
      ((f.2 x.2⁻¹ (((x.1 : (R : Set G)) : G)⁻¹)).symm)
  right_inv ξ := by
    ext r
    have hfst :
        (hR.equiv (r : G)).fst = r :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    have hsnd :
        (hR.equiv (r : G)).snd = (1 : H) :=
      hR.equiv_snd_eq_one_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    -- At a representative inverse, the complement decomposition is the trivial one `r * 1`.
    dsimp
    simp [hfst, hsnd]
/-- Helper for Theorem 17-17.3-1: after inducing a free finite `A[H]`-model, the induced source
can be compressed to a same-universe free finite carrier by passing through the finite-index
coinduced model on representative coordinates. -/
theorem exists_same_universe_finite_free_induced_model_from_rep_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0) :
    ∃ (W_ind : Type u) (_ : AddCommGroup W_ind) (_ : Module A W_ind)
      (_ : Module.Free A W_ind) (_ : Module.Finite A W_ind)
      (ρA_ind : Representation A G W_ind),
        Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) := by
  classical
  obtain ⟨S, hS, _⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : Subgroup.IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  let eIndCoind :
      (Representation.ind H.subtype ρA_H).Equiv
        (Representation.coind H.subtype ρA_H) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of ρA_H))
  let eCoind :
      Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W0) :=
    coind_representative_equiv_local (A := A) (G := G) ρA_H R hR
  let ρR : Representation A G (↥(R : Set G) → W0) :=
    { toFun := fun g ↦ eCoind.conj ((Representation.coind H.subtype ρA_H) g)
      map_one' := by
        calc
          eCoind.conj ((Representation.coind H.subtype ρA_H) 1) = eCoind.conj 1 := by
            rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eR : ρR.Equiv (Representation.coind H.subtype ρA_H) :=
    Representation.Equiv.mk eCoind.symm fun g ↦ by
      apply LinearMap.ext
      intro x
      change
        eCoind.symm (eCoind ((Representation.coind H.subtype ρA_H) g (eCoind.symm x))) =
          (Representation.coind H.subtype ρA_H) g (eCoind.symm x)
      simp [ρR]
  letI : Finite ↥(R : Set G) := Set.toFinite (R : Set G)
  letI : Fintype ↥(R : Set G) := Fintype.ofFinite _
  rcases
      exists_same_universe_finite_free_rep_model_local
        (A := A) (G' := G) (ρA := ρR) with
    ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, hEquiv⟩
  rcases hEquiv with ⟨ePack⟩
  refine ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, ?_⟩
  exact ⟨ePack.trans (eR.trans eIndCoind.symm)⟩

private theorem induced_subrepresentation_lift_standard_target_isResidueFieldLift_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    [_hFreeInd : Module.Free A (Representation.IndV H.subtype ρA_H)]
    [_hFiniteInd : Module.Finite A (Representation.IndV H.subtype ρA_H)]
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∃ red_native :
        Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation,
      IsResidueFieldLift
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
  let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  let red_u :
      Representation.IndV H.subtype ρA_HU →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
  have hred_u :
      ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
        red_u (Representation.IndV.mk H.subtype ρA_HU g xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
    intro g xU
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_apply_mk_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g xU
  have hBase_u : IsBaseChange k red_u := by
    exact
      induced_subrepresentation_lift_ulift_source_isBaseChange_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH red_u hred_u
  have hInter_u :
      (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_u := by
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_isIntertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let _ := hBase_u
  let _ := hInter_u
  let eU : ρA_HU.Equiv ρA_H :=
    Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
      -- The `ULift` wrapper leaves the subgroup action unchanged pointwise.
      ext y
      rfl
  let eInd :
      (Representation.ind H.subtype ρA_HU).Equiv
        (Representation.ind H.subtype ρA_H) :=
    ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
  let red_native :
      Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_u.comp eInd.symm.toLinearMap
  -- Transport the raw reduction data back across the induced `ULift` source equivalence.
  have hred_native :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    simpa [red_native] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        hBase_u hInter_u eInd.symm
  -- Repackage the transported raw reduction as the native induced residue-field lift.
  have hLift_native :
      IsResidueFieldLift
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_native
  exact ⟨red_native, hLift_native⟩

-/
theorem induced_standard_model_residueFieldLift_exists
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA_ind : Representation A G W')
      (red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation),
        IsResidueFieldLift (Representation.ind H.subtype W.toRepresentation) ρA_ind red_ind := by
  -- Route correction: do not first force the native induced source into an `IsResidueFieldLift`,
  -- since that would require free/finite instances on `IndV`. Instead, transport the raw
  -- reduction data from the `ULift` source to the native induced source, then to the packaged
  -- same-universe source.
  let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  let red_u :
      Representation.IndV H.subtype ρA_HU →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
  have hred_u :
      ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
        red_u (Representation.IndV.mk H.subtype ρA_HU g xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
    intro g xU
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_apply_mk_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g xU
  have hBase_u : IsBaseChange k red_u := by
    exact
      induced_subrepresentation_lift_ulift_source_isBaseChange_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH red_u hred_u
  have hInter_u :
      (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_u := by
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_isIntertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let eU : ρA_HU.Equiv ρA_H :=
    Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
      -- The `ULift` wrapper leaves the subgroup action unchanged pointwise.
      ext y
      rfl
  let eInd_native :
      (Representation.ind H.subtype ρA_HU).Equiv
        (Representation.ind H.subtype ρA_H) :=
    ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
  let red_native :
      Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_u.comp eInd_native.symm.toLinearMap
  have hred_native :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    -- First remove the `ULift` from the induced source while keeping only the raw reduction data.
    simpa [red_native] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        hBase_u hInter_u eInd_native.symm
  have hBase_native : IsBaseChange k red_native := by
    simpa [RawIsResidueFieldReduction_local] using hred_native.1
  have hInter_native :
      (Representation.ind H.subtype ρA_H).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_native := by
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq :
        eInd_native.symm ((Representation.ind H.subtype ρA_H) g x) =
          (Representation.ind H.subtype ρA_HU) g (eInd_native.symm x) := by
      simpa using LinearMap.congr_fun (eInd_native.symm.isIntertwining' g) x
    calc
      red_native ((Representation.ind H.subtype ρA_H) g x) =
          red_u ((Representation.ind H.subtype ρA_HU) g (eInd_native.symm x)) := by
            simpa [red_native, LinearMap.comp_apply] using congrArg red_u heq
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_u (eInd_native.symm x)) := by
              simpa [Representation.restrictScalars_apply] using
                hInter_u.isIntertwining g (eInd_native.symm x)
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_native x) := by
              simp [red_native, LinearMap.comp_apply]
  rcases
      exists_same_universe_finite_free_induced_model_from_rep_local
        (A := A) (G := G) (H := H) ρA_H with
    ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, hEquiv⟩
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  rcases hEquiv with ⟨ePack⟩
  let red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_native.comp ePack.toLinearMap
  have hred_ind :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        ρA_ind
        red_ind := by
    -- Then move from the native induced source to the packaged same-universe source.
    simpa [red_ind] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        (ρA' := ρA_ind)
        (ρA := Representation.ind H.subtype ρA_H)
        (red := red_native)
        hBase_native hInter_native ePack
  refine ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, ?_⟩
  -- The packaged source is free and finite, so the raw reduction data upgrades immediately to an
  -- actual residue-field lift.
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_ind

/-

/-- Helper for Theorem 17-17.3-1: once the standard induced model already has a packaged
residue-field lift, any explicit representation equivalence from that model to the ambient
representation `ρ` finishes the proper-overgroup branch by a single postcomposition of the
reduction map. -/
private theorem transport_induced_residueFieldLift_along_equiv
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W' : Type u} [AddCommGroup W'] [Module A W']
    [Module.Free A W'] [Module.Finite A W']
    (ρA_ind : Representation A G W')
    (red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation)
    (hLiftInd :
      IsResidueFieldLift (Representation.ind H.subtype W.toRepresentation) ρA_ind red_ind)
    (eInd : (Representation.ind H.subtype W.toRepresentation).Equiv ρ) :
    ∃ (W'' : Type u) (_ : AddCommGroup W'') (_ : Module A W'')
      (_ : Module.Free A W'') (_ : Module.Finite A W'')
      (ρA : Representation A G W'')
      (red : W'' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- The source route has already finished induction; only the final target transport remains.
  exact
    ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, ρA_ind,
      (eInd.toLinearMap.restrictScalars A).comp red_ind,
      residueFieldLift_of_equiv_target
        (A := A) (G := G) (V := V) hLiftInd eInd⟩

/-- Helper for Theorem 17-17.3-1: the Chapter `7` inducedness witness should give an explicit
representation equivalence from the standard induced model back to the ambient representation,
without assuming the ambient carrier already lives in `Type (max u v w)`. -/
private noncomputable def inducedFromSubrepresentation_explicit_equiv_general_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
  by
  let ρU : Representation k G (ULift.{max (max u v) w, w} V) :=
    { toFun := fun g =>
        { toFun := fun x ↦ ⟨ρ g x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let eU : ρ.Equiv ρU :=
    Representation.Equiv.mk
      (ULift.moduleEquiv.symm : V ≃ₗ[k] ULift.{max (max u v) w, w} V) fun g ↦ by
        -- The `ULift` wrapper does not change the pointwise action of `ρ`.
        ext x
        rfl
  let WU : Subrepresentation (ρU.comp H.subtype) :=
    transported_subrepresentation_of_equiv_local
      (comp_subtype_equiv_local eU H) W
  have hIndU :
      ρU.IsInducedFromSubrepresentation H WU := by
    -- Transport the inducedness data to the lifted ambient carrier.
    simpa [WU] using
      (isInducedFromSubrepresentation_of_equiv_local
        (ρ₁ := ρ) (ρ₂ := ρU) eU H W hInd)
  let eW : W.toRepresentation.Equiv WU.toRepresentation :=
    by
      -- Reuse the standard image-subrepresentation equivalence for the transported carrier.
      simpa [WU, transported_subrepresentation_of_equiv_local, subrepresentationOrderIso_local]
        using
          (subrepresentation_equiv_of_equiv_image_local
            (comp_subtype_equiv_local eU H) W)
  let eIndU :
      (Representation.ind H.subtype WU.toRepresentation).Equiv ρU :=
    Representation.inducedFromSubrepresentation_explicit_equiv
      (ρ := ρU) (W := WU) hIndU
  let eSource :
      (Representation.ind H.subtype W.toRepresentation).Equiv
        (Representation.ind H.subtype WU.toRepresentation) :=
    ind_equiv_of_source_equiv_local H.subtype eW
  -- Build the explicit induced equivalence on the lifted carrier, then remove the `ULift`.
  exact (eSource.trans eIndU).trans eU.symm

-/
/-- Helper for Theorem 17-17.3-1: once the standard induced model has been lifted on a same-
universe carrier, the only remaining proper-overgroup step is the final Chapter `7` transport
across `ρ.inducedFromSubrepresentationHom H W`. -/
private lemma exists_residueFieldLift_of_isInducedFromSubrepresentation_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA : Representation A G W')
      (red : W' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  obtain ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, hLiftInd⟩ :=
    induced_standard_model_residueFieldLift_exists
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  let eInd :
      (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
    inducedFromSubrepresentation_explicit_equiv_general_local
      (A := A) (G := G) (V := V) ρ W hInd
  -- After packaging the induced lift on a same-universe source, only the final Chapter `7`
  -- transport back to the ambient representation remains.
  exact
    transport_induced_residueFieldLift_along_equiv
      (A := A) (G := G) (V := V) ρ W ρA_ind red_ind hLiftInd eInd

/-- Helper for Theorem 17-17.3-1: once the Clifford split lands in the proper-overgroup branch,
the proof continues by recursing on that smaller subgroup and then inducing the lifted module back
to `G`. -/
lemma exists_residueFieldLift_of_proper_overgroup_induced
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (hrecSame :
      ∀ {H : Subgroup G} {W0 : Type w} [AddCommGroup W0] [Module k W0]
        [FiniteDimensional k W0]
        {C0 P0 : Subgroup H}
        (hH : H < ⊤)
        (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
        (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
        (σ : Representation k H W0) [σ.IsIrreducible],
          ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
            (_ : Module.Free A W') (_ : Module.Finite A W')
            (ρA_H : Representation A H W')
            (red_H : W' →ₗ[A] W0),
              IsResidueFieldLift σ ρA_H red_H)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        C ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hproper with ⟨H, hCH, hHlt, W, hWirred, hInd⟩
  let C0 : Subgroup H := C.subgroupOf H
  let P0 : Subgroup H := (H ⊓ P).subgroupOf H
  have hHdecomp :
      C0.Normal ∧ C0.IsComplement' P0 ∧ IsCyclic C0 ∧ Nat.Coprime p (Nat.card C0) ∧ IsPGroup p P0 :=
    subgroup_cyclicNormalByPGroupDecomposition_of_le
      (p := p) (C := C) (P := P) hCH hC hCP hCyclic hCoprime hP
  rcases hHdecomp with ⟨hC0, hC0P0, hC0cyc, hC0cop, hP0⟩
  letI : W.toRepresentation.IsIrreducible := hWirred
  -- Route correction: the outer cardinal induction now supplies the smaller-group recursion, so
  -- the only remaining work in this branch is the induced transport step below.
  have hLiftH :
      ∃ (W0 : Type u) (_ : AddCommGroup W0) (_ : Module A W0)
        (_ : Module.Free A W0) (_ : Module.Finite A W0)
        (ρA_H : Representation A H W0)
        (red_H : W0 →ₗ[A] W.toSubmodule),
          IsResidueFieldLift W.toRepresentation ρA_H red_H := by
    -- Apply the recursive hypothesis to the inherited cyclic-normal-by-`p` decomposition on `H`.
    exact hrecSame hHlt hC0 hC0P0 hC0cyc hC0cop hP0 W.toRepresentation
  rcases hLiftH with ⟨W0, hW0add, hW0mod, hW0free, hW0finite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup W0 := hW0add
  letI : Module A W0 := hW0mod
  letI : Module.Free A W0 := hW0free
  letI : Module.Finite A W0 := hW0finite
  -- The recursion on `H` is now isolated above; from here on we only need the induction
  -- transport from the lifted `H`-model of `W` back to the ambient representation `ρ`.
  exact
    exists_residueFieldLift_of_isInducedFromSubrepresentation_local
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH hInd

/-- Helper for Theorem 17-17.3-1: every residue-field lift has surjective reduction map, because
its base-change equivalence identifies the target with the tensor product over the residue field. -/
private theorem residueFieldLift_surjective
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W : Type*} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' W}
    {red : W →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    Function.Surjective red := by
  letI : Module A k := Algebra.toModule
  -- Unpack the tensor-product base change equivalence and use surjectivity of `A → k`.
  intro y
  obtain ⟨t, ht⟩ := hLift.1.equiv.surjective y
  obtain ⟨x, hx⟩ :=
    TensorProduct.mk_surjective A W (IsLocalRing.ResidueField A) Ideal.Quotient.mk_surjective t
  refine ⟨x, ?_⟩
  calc
    red x = hLift.1.equiv (TensorProduct.mk A (IsLocalRing.ResidueField A) W 1 x) := by
      simpa using (hLift.1.equiv_tmul (1 : k) x).symm
    _ = hLift.1.equiv t := by rw [hx]
    _ = y := ht

/-- Helper for Theorem 17-17.3-1: conjugating the restricted `C`-representation by an element of
`P` is equivalent to the original restricted action via `ρ s` on the carrier. -/
private noncomputable def restricted_conjugation_equiv_of_p_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (s : P) :
    Representation.Equiv
      (((ρ.comp C.subtype).comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom))
      (ρ.comp C.subtype) := by
  let _ := hC
  let e : V ≃ₗ[k] V :=
    LinearEquiv.ofBijective (ρ (s : G)) (ρ.apply_bijective (s : G))
  refine Representation.Equiv.mk e ?_
  intro c
  ext v
  -- Rewrite the conjugated `C`-action as literal multiplication in `G`, then cancel the
  -- conjugation by the defining formula for `MulAut.conjNormal`.
  calc
    e ((((ρ.comp C.subtype).comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom) c) v)
        = ρ (s : G) (ρ (((MulAut.conjNormal ((s : G))⁻¹) c : C)) v) := by
            rfl
    _ = ρ ((s : G) * (((MulAut.conjNormal ((s : G))⁻¹) c : C))) v := by
          exact
            (LinearMap.congr_fun
              (ρ.map_mul (s : G) (((MulAut.conjNormal ((s : G))⁻¹) c : C))) v).symm
    _ = ρ ((c : G) * (s : G)) v := by
          simp [mul_assoc]
    _ = ((ρ.comp C.subtype) c) (e v) := by
          exact LinearMap.congr_fun (ρ.map_mul (c : G) (s : G)) v

/-- Helper for Theorem 17-17.3-1: for each `s : P`, Serre's conjugated `C`-lift and the chosen
fixed `C`-lift are already compared by Chapter `15` uniqueness after shrinking `C` into the
coefficient universe. -/
private theorem character_field_transport_conjugate_lift_compare_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (hCndvd : ¬ p ∣ Nat.card C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (s : P) :
    ∃ u :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C,
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
          A).comp red_C) := by
  let ρC : Representation k C V := ρ.comp C.subtype
  let ρA_conj_s : Representation A C W :=
    ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom
  let red_s : W →ₗ[A] V :=
    (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
      A).comp red_C)
  have hConjLift :
      IsResidueFieldLift
        (ρC.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_conj_s
        red_C := by
    -- Restrict the chosen `C`-lift along the conjugation action of `s⁻¹`.
    simpa [ρC, ρA_conj_s] using
      (Representation.isResidueFieldLift_comp hLiftC
        (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
  have hLiteralTransport :
      IsResidueFieldLift ρC ρA_conj_s red_s := by
    -- Transport the conjugated reduced target back to the original restricted `C`-action.
    simpa [ρC, ρA_conj_s, red_s] using
      (residueFieldLift_of_equiv_target
        (A := A) (G := C) (V := V) (ρA := ρA_conj_s) hConjLift
        (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s))
  have hSmallC : Small.{u} C := by
    obtain ⟨n, ⟨efin⟩⟩ := Finite.exists_equiv_fin C
    exact Small.mk' (efin.trans Equiv.ulift.symm)
  letI : Small.{u} C := hSmallC
  let eShrink : Shrink.{u} C ≃* C := Shrink.mulEquiv
  have hShrink_ndvd : ¬ p ∣ Nat.card (Shrink.{u} C) := by
    simpa [Nat.card_congr eShrink.toEquiv] using hCndvd
  have hConjLift_shrink :
      IsResidueFieldLift
        (ρC.comp eShrink.toMonoidHom)
        (ρA_conj_s.comp eShrink.toMonoidHom)
        red_s := by
    exact Representation.isResidueFieldLift_comp hLiteralTransport eShrink.toMonoidHom
  have hFixedLift_shrink :
      IsResidueFieldLift
        (ρC.comp eShrink.toMonoidHom)
        (ρA_C.comp eShrink.toMonoidHom)
        red_C := by
    exact Representation.isResidueFieldLift_comp hLiftC eShrink.toMonoidHom
  obtain ⟨uShrink, hu⟩ :=
    residueFieldLift_unique_up_to_equivariant_iso
      (A := A) (p := p) (G := Shrink.{u} C) (V := V)
      hShrink_ndvd
      (ρC.comp eShrink.toMonoidHom)
      (ρA_conj_s.comp eShrink.toMonoidHom)
      red_s
      hConjLift_shrink
      (ρA_C.comp eShrink.toMonoidHom)
      red_C
      hFixedLift_shrink
  let u : ρA_conj_s.Equiv ρA_C :=
    Representation.Equiv.mk uShrink.toLinearEquiv fun g ↦ by
      -- The shrink comparison is equivariant for every `g' : Shrink C`, hence also for the
      -- original element `g : C` after rewriting along `eShrink`.
      simpa [ρA_conj_s] using uShrink.isIntertwining' (eShrink.symm g)
  refine ⟨u, ?_⟩
  change red_C.comp uShrink.toLinearMap = red_s
  exact hu

/-- Helper for Theorem 17-17.3-1: the Chapter `15` comparison sends the chosen lifted generator
`w0` to another lift of the same `P`-fixed residue vector `ν`. -/
private theorem character_field_transport_conjugate_lift_compare_fixed_vector_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (hCndvd : ¬ p ∣ Nat.card C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (s : P) :
    ∃ u :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C,
      red_C.comp u.toLinearMap =
          (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
            A).comp red_C) ∧
        red_C (u w0) = ν := by
  obtain ⟨u, hu⟩ :=
    character_field_transport_conjugate_lift_compare_local
      (A := A) (G := G) (p := p) (V := V) (C := C) (P := P)
      ρ hC hCndvd ρA_C red_C hLiftC s
  refine ⟨u, hu, ?_⟩
  -- Evaluate the uniqueness comparison on `w0`; the residue-side action is `ρ s`, hence it fixes
  -- `ν` by the `P`-fixed hypothesis.
  have huw0 :
      red_C (u w0) =
        (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
          A).comp red_C) w0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : W →ₗ[A] V ↦ f w0) hu
  calc
    red_C (u w0)
        = (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
            A).comp red_C) w0 := huw0
    _ = (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s) (red_C w0) := by
          rfl
    _ = (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s) ν := by
          rw [hw0]
    _ = ρ (s : G) ν := by
          rfl
    _ = (ρ.comp P.subtype) s ν := by
          rfl
    _ = ν := hνfixed s

/-- Helper for Theorem 17-17.3-1: every comparison image `u w0` still generates the lifted
`C`-module because it reduces to the same cyclic residue generator `ν`. -/
private theorem character_field_transport_compare_generator_span_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w1 : W) (ν : V)
    (hw1 : red_C w1 = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤) :
    Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤ := by
  -- Once `w1` reduces to the same residue generator, the previously proved cyclic-lift argument
  -- applies verbatim with `w1` in place of the original chosen lift.
  exact
    cyclic_lift_span_top_of_fixed_lift
      (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC w1 ν hw1 hOrbitSpan

/-- Helper for Theorem 17-17.3-1: on the regular `A[C]`-module of a lifted `C`-representation,
left multiplication by any `r : A[C]` is `C`-equivariant because `C` is cyclic and hence
`A[C]` is commutative. This is the source-level commutativity input in Serre's cyclic-presentation
comparison. -/
private theorem character_field_transport_regular_action_isIntertwining_local
    {C0 : Type*} [Group C0] [IsMulCommutative C0]
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C0 W)
    (r : MonoidAlgebra A C0) :
    ρA_C.IsIntertwiningMap ρA_C (ρA_C.asAlgebraHom r) := by
  rw [Representation.isIntertwiningMap_iff]
  intro c x
  -- The `A[C]`-action commutes with the `C`-action because both come from the same commutative
  -- group algebra `A[C]`.
  have hcomm :
      (ρA_C.asAlgebraHom r) * (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) =
        (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) * (ρA_C.asAlgebraHom r) := by
    ext y
    have hmul : r * MonoidAlgebra.of A C0 c = MonoidAlgebra.of A C0 c * r := by
      ext g
      simpa [MonoidAlgebra.of_apply] using congrArg r (mul_comm' g c⁻¹)
    calc
      (ρA_C.asAlgebraHom r) ((ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) y)
          = (ρA_C.asAlgebraHom (r * MonoidAlgebra.of A C0 c)) y := by
              simp [Module.End.mul_apply]
      _ = (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c * r)) y := by
            rw [hmul]
      _ = (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) ((ρA_C.asAlgebraHom r) y) := by
            simp [Module.End.mul_apply]
  simpa [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply, Module.End.mul_apply] using
    LinearMap.congr_fun hcomm x

/-- Helper for Theorem 17-17.3-1: two cyclic generators with full `C`-orbit span define the same
kernel in the regular `A[C]`-module. This is the common cyclic presentation behind Serre's
normalization step. -/
private theorem character_field_transport_cyclic_kernel_eq_local
    {W : Type u} [AddCommGroup W] [Module A W] [IsMulCommutative C]
    (ρA_C : Representation A C W)
    (w0 w1 : W)
    (hspan0 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (hspan1 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤) :
    letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
    letI : IsScalarTower A (MonoidAlgebra A C) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
    ∀ r : MonoidAlgebra A C, r • w0 = 0 ↔ r • w1 = 0 := by
  intro r
  let fr : W →ₗ[A] W := ρA_C.asAlgebraHom r
  have hfr : ρA_C.IsIntertwiningMap ρA_C fr := by
    -- The source-faithful input is that the regular `A[C]`-action commutes with the `C`-action.
    simpa [fr] using
      character_field_transport_regular_action_isIntertwining_local
        (A := A) (C0 := C) (ρA_C := ρA_C) r
  rw [Representation.isIntertwiningMap_iff] at hfr
  constructor
  · intro hr0
    have hr0' : fr w0 = 0 := by
      simpa [fr] using hr0
    have hzero_on_span0 :
        ∀ y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w0), fr y = 0 := by
      intro y hy
      -- Once `r` kills the cyclic generator `w0`, `C`-equivariance forces it to kill the whole
      -- `C`-orbit span, hence every vector of `W`.
      refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w0) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨c, rfl⟩
        calc
          fr (ρA_C c w0) = ρA_C c (fr w0) := hfr c w0
          _ = ρA_C c 0 := by rw [hr0']
          _ = 0 := by simp
      · rw [map_zero]
      · intro y z hy hz hy0 hz0
        simpa [map_add, hy0, hz0]
      · intro a y hy hy0
        simpa [map_smul, hy0]
    have hfr_w1 : fr w1 = 0 := by
      have hy : w1 ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) := by
        rw [hspan0]
        exact Submodule.mem_top
      exact hzero_on_span0 w1 hy
    simpa [fr] using hfr_w1
  · intro hr1
    have hr1' : fr w1 = 0 := by
      simpa [fr] using hr1
    have hzero_on_span1 :
        ∀ y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w1), fr y = 0 := by
      intro y hy
      -- The same cyclic-presentation argument in the opposite direction gives the reverse
      -- kernel inclusion.
      refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w1) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨c, rfl⟩
        calc
          fr (ρA_C c w1) = ρA_C c (fr w1) := hfr c w1
          _ = ρA_C c 0 := by rw [hr1']
          _ = 0 := by simp
      · rw [map_zero]
      · intro y z hy hz hy0 hz0
        simpa [map_add, hy0, hz0]
      · intro a y hy hy0
        simpa [map_smul, hy0]
    have hfr_w0 : fr w0 = 0 := by
      have hy : w0 ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) := by
        rw [hspan1]
        exact Submodule.mem_top
      exact hzero_on_span1 w0 hy
    simpa [fr] using hfr_w0

/-- Helper for Theorem 17-17.3-1: if the `C`-orbit of `w` spans `W`, then every vector of `W`
is of the form `r • w` for some `r ∈ A[C]`. This is the surjectivity input needed before passing
to Serre's common cyclic quotient. -/
private theorem character_field_transport_cyclic_presentation_surjective_local
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C W)
    (w : W)
    (hspan : Submodule.span A (Set.range fun c : C ↦ ρA_C c w) = ⊤) :
    letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
    letI : IsScalarTower A (MonoidAlgebra A C) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
    ∀ y : W, ∃ r : MonoidAlgebra A C, r • w = y := by
  letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
  intro y
  have hy : y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w) := by
    rw [hspan]
    exact Submodule.mem_top
  -- Build the desired coefficient `r` by induction on the cyclic `A`-span of the `C`-orbit.
  refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w) ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨c, rfl⟩
    refine ⟨MonoidAlgebra.single c (1 : A), ?_⟩
    change ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A)) w = ρA_C c w
    simp [Representation.asAlgebraHom_single]
  · exact ⟨0, by simp⟩
  · intro y z hy' hz' hriy hriz
    rcases hriy with ⟨ry, rfl⟩
    rcases hriz with ⟨rz, rfl⟩
    refine ⟨ry + rz, by simp [add_smul]⟩
  · intro a y hy' hriy
    rcases hriy with ⟨r, rfl⟩
    refine ⟨(algebraMap A (MonoidAlgebra A C) a) * r, ?_⟩
    calc
      ((algebraMap A (MonoidAlgebra A C) a) * r) • w
          = (algebraMap A (MonoidAlgebra A C) a) • (r • w) := by
              rw [mul_smul]
      _ = a • (r • w) := by
            simpa using (IsScalarTower.algebraMap_smul (MonoidAlgebra A C) a (r • w))

/-- Helper for Theorem 17-17.3-1: an equality of annihilator submodules transports the common
cyclic quotient without introducing any new carrier-level data. This isolates the only quotient
transport used in Serre's normalization step. -/
private noncomputable def quotient_transport_linearEquiv_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {K L : Submodule A M} (h : K = L) :
    (M ⧸ K) ≃ₗ[A] M ⧸ L :=
  h ▸ (LinearEquiv.refl A (M ⧸ K))

/-- Helper for Theorem 17-17.3-1: the quotient transport above sends each quotient generator class
to the identically represented class in the transported quotient. -/
private theorem quotient_transport_linearEquiv_apply_mk_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {K L : Submodule A M} (h : K = L) (x : M) :
    quotient_transport_linearEquiv_local (A := A) (M := M) h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : M ⧸ L) := by
  -- After rewriting by the kernel equality, the transport is literally the identity map.
  cases h
  rfl

/-- Helper for Theorem 17-17.3-1: two surjective linear maps with the same kernel identify the
same target with one frozen quotient of the common source. This packages the common cyclic model
used later with `π₀ r = r • w₀` and `π₁ r = r • w₁`. -/
private theorem common_quotient_model_of_surjective_linearMaps_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {W : Type*} [AddCommGroup W] [Module A W]
    (π0 π1 : M →ₗ[A] W)
    (hπ0 : Function.Surjective π0)
    (hπ1 : Function.Surjective π1)
    (hker : LinearMap.ker π0 = LinearMap.ker π1) :
    let Q := M ⧸ LinearMap.ker π0
    ∃ e0 e1 : Q ≃ₗ[A] W,
      (∀ x : M, e0 (Submodule.Quotient.mk x) = π0 x) ∧
        ∀ x : M, e1 (Submodule.Quotient.mk x) = π1 x := by
  let Q := M ⧸ LinearMap.ker π0
  let e0 : Q ≃ₗ[A] W := π0.quotKerEquivOfSurjective hπ0
  let q01 : Q ≃ₗ[A] M ⧸ LinearMap.ker π1 :=
    quotient_transport_linearEquiv_local (A := A) (M := M) hker
  let e1 : Q ≃ₗ[A] W := q01.trans (π1.quotKerEquivOfSurjective hπ1)
  refine ⟨e0, e1, ?_, ?_⟩
  · intro x
    -- The first model is the standard first-isomorphism-theorem quotient for `π0`.
    simpa [Q, e0] using LinearMap.quotKerEquivOfSurjective_apply_mk π0 hπ0 x
  · intro x
    -- The second model uses the same quotient after one kernel transport, then applies the
    -- standard first-isomorphism-theorem quotient for `π1`.
    change (π1.quotKerEquivOfSurjective hπ1) (q01 (Submodule.Quotient.mk x)) = π1 x
    rw [quotient_transport_linearEquiv_apply_mk_local
      (A := A) (M := M) (h := hker)]
    simpa using LinearMap.quotKerEquivOfSurjective_apply_mk π1 hπ1 x

/-- Helper for Theorem 17-17.3-1: once two lifts `w0` and `w1` of the same cyclic residue
generator define the same annihilator in `A[C]`, Serre's common-quotient argument yields a
`C`-equivariant automorphism reducing to the identity and sending `w1` back to `w0`. -/
private theorem character_field_transport_correction_equiv_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    [IsMulCommutative C]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 w1 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    (hw1 : red_C w1 = ν)
    (hspan0 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (hspan1 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤) :
    ∃ corr : ρA_C.Equiv ρA_C,
      red_C.comp corr.toLinearMap = red_C ∧
        corr w1 = w0 := by
  -- Route correction: the common quotient model is now packaged by
  -- `common_quotient_model_of_surjective_linearMaps_local`. The remaining blocker is to descend
  -- the reduction map through the frozen quotient and then promote the resulting comparison
  -- `e0.trans e1.symm` from a linear equivalence to a `C`-equivariant automorphism of `ρA_C`.
  letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x =
          (algebraMap A (Module.End A W) a) x
      exact LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
  let ρC : Representation A C V := Representation.restrictScalars A (ρ.comp C.subtype)
  letI : Module (MonoidAlgebra A C) V := Module.compHom V ρC.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        ρC.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x =
          (algebraMap A (Module.End A V) a) x
      exact LinearMap.congr_fun (ρC.asAlgebraHom.commutes a) x
  letI : Module A A := Semiring.toModule
  letI : Module A (MonoidAlgebra A C) := MonoidAlgebra.module
  let π0 : MonoidAlgebra A C →ₗ[A] W :=
    { toFun := fun r ↦ r • w0
      map_add' := by
        intro r s
        simp [add_smul]
      map_smul' := by
        intro a r
        -- Read `π0` through the algebra homomorphism `A[C] → End_A(W)` and evaluate its
        -- `A`-linearity at the cyclic generator `w0`.
        exact congrArg (fun f : Module.End A W ↦ f w0) (ρA_C.asAlgebraHom.toLinearMap.map_smul a r) }
  let π1 : MonoidAlgebra A C →ₗ[A] W :=
    { toFun := fun r ↦ r • w1
      map_add' := by
        intro r s
        simp [add_smul]
      map_smul' := by
        intro a r
        -- The same `A`-linearity computation evaluated at `w1`.
        exact congrArg (fun f : Module.End A W ↦ f w1) (ρA_C.asAlgebraHom.toLinearMap.map_smul a r) }
  have hπ0 : Function.Surjective π0 := by
    intro y
    simpa [π0] using
      character_field_transport_cyclic_presentation_surjective_local
        (A := A) (C := C) ρA_C w0 hspan0 y
  have hπ1 : Function.Surjective π1 := by
    intro y
    simpa [π1] using
      character_field_transport_cyclic_presentation_surjective_local
        (A := A) (C := C) ρA_C w1 hspan1 y
  have hker : LinearMap.ker π0 = LinearMap.ker π1 := by
    ext r
    change r • w0 = 0 ↔ r • w1 = 0
    exact
      character_field_transport_cyclic_kernel_eq_local
        (A := A) (C := C) ρA_C w0 w1 hspan0 hspan1 r
  rcases
      common_quotient_model_of_surjective_linearMaps_local
        (A := A) (M := MonoidAlgebra A C) (W := W) π0 π1 hπ0 hπ1 hker with
    ⟨e0, e1, he0, he1⟩
  let corrLin : W ≃ₗ[A] W := e1.symm.trans e0
  have hredInter :
      ρA_C.IsIntertwiningMap (Representation.restrictScalars A (ρ.comp C.subtype)) red_C :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftC
  have hred_smul : ∀ r : MonoidAlgebra A C, ∀ x : W, red_C (r • x) = r • red_C x := by
    intro r
    -- The reduction map is `A[C]`-linear because it intertwines the lifted and reduced
    -- `C`-actions on group generators.
    refine MonoidAlgebra.induction_on
      (p := fun r : MonoidAlgebra A C ↦ ∀ x : W, red_C (r • x) = r • red_C x) r ?_ ?_ ?_
    · intro c
      intro x
      calc
        red_C (MonoidAlgebra.of A C c • x) = red_C (ρA_C c x) := by
          change red_C ((ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) x) = _
          simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
        _ = ρC c (red_C x) := hredInter.isIntertwining c x
        _ = MonoidAlgebra.of A C c • red_C x := by
          change ρC c (red_C x) = (ρC.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (red_C x)
          simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
    · intro a b ha hb x
      simp [add_smul, ha x, hb x]
    · intro a r hr x
      calc
        red_C ((a • r) • x) = red_C (a • (r • x)) := by
          simpa [smul_assoc]
        _ = a • red_C (r • x) := by rw [LinearMap.map_smul]
        _ = a • (r • red_C x) := by rw [hr x]
        _ = (a • r) • red_C x := by
          simpa [smul_assoc]
  have hred_classes :
      ∀ r : MonoidAlgebra A C,
        red_C (e0 (Submodule.Quotient.mk r)) = red_C (e1 (Submodule.Quotient.mk r)) := by
    intro r
    -- Both quotient models reduce to the same cyclic residue vector `ν`, so they agree after
    -- applying `red_C` on every quotient class.
    calc
      red_C (e0 (Submodule.Quotient.mk r)) = red_C (r • w0) := by simpa [π0] using congrArg red_C (he0 r)
      _ = r • red_C w0 := hred_smul r w0
      _ = r • ν := by rw [hw0]
      _ = r • red_C w1 := by rw [hw1]
      _ = red_C (r • w1) := by rw [hred_smul r w1]
      _ = red_C (e1 (Submodule.Quotient.mk r)) := by simpa [π1] using congrArg red_C (he1 r).symm
  have he0_mul :
      ∀ c : C, ∀ r : MonoidAlgebra A C,
        e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) =
          ρA_C c (e0 (Submodule.Quotient.mk r)) := by
    intro c r
    -- On quotient classes, `e0` is the cyclic presentation `r ↦ r • w0`, so left
    -- multiplication by `c` becomes the original `C`-action on `W`.
    calc
      e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))
          = (MonoidAlgebra.of A C c * r) • w0 := by
              simpa [π0] using he0 (MonoidAlgebra.of A C c * r)
      _ = MonoidAlgebra.of A C c • (r • w0) := by rw [mul_smul]
      _ = ρA_C c (r • w0) := by
            change (ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (r • w0) = _
            simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
      _ = ρA_C c (e0 (Submodule.Quotient.mk r)) := by
            simpa [π0] using congrArg (ρA_C c) (he0 r).symm
  have he1_mul :
      ∀ c : C, ∀ r : MonoidAlgebra A C,
        e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) =
          ρA_C c (e1 (Submodule.Quotient.mk r)) := by
    intro c r
    -- The same computation for the second cyclic model identifies its transported generator.
    calc
      e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))
          = (MonoidAlgebra.of A C c * r) • w1 := by
              simpa [π1] using he1 (MonoidAlgebra.of A C c * r)
      _ = MonoidAlgebra.of A C c • (r • w1) := by rw [mul_smul]
      _ = ρA_C c (r • w1) := by
            change (ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (r • w1) = _
            simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
      _ = ρA_C c (e1 (Submodule.Quotient.mk r)) := by
            simpa [π1] using congrArg (ρA_C c) (he1 r).symm
  have hcorrRedLin : red_C.comp corrLin.toLinearMap = red_C := by
    apply LinearMap.ext
    intro x
    obtain ⟨q, rfl⟩ := e1.surjective x
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker π0) q
    -- Compare both quotient models on the same class and use the common reduction above.
    calc
      red_C (corrLin (e1 (Submodule.Quotient.mk r)))
          = red_C (e0 (Submodule.Quotient.mk r)) := by
              simp [corrLin]
      _ = red_C (e1 (Submodule.Quotient.mk r)) := hred_classes r
  have hcorrw : corrLin w1 = w0 := by
    -- The class of `1 ∈ A[C]` is the common cyclic generator of both quotient models.
    calc
      corrLin w1 = corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))) := by
        change corrLin w1 = corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C)))
        rw [he1]
        simp [π1]
      _ = e0 (Submodule.Quotient.mk (1 : MonoidAlgebra A C)) := by
        change corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))) =
          e0 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))
        simp [corrLin]
      _ = w0 := by
        rw [he0]
        simp [π0]
  have hcorrInter : ρA_C.IsIntertwiningMap ρA_C corrLin.toLinearMap := by
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    obtain ⟨q, rfl⟩ := e1.surjective x
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker π0) q
    -- The correction map compares the two quotient models of the same cyclic presentation, so
    -- it commutes with the `C`-action generatorwise on quotient classes.
    calc
      corrLin (ρA_C c (e1 (Submodule.Quotient.mk r)))
          = corrLin (e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))) := by
              rw [← he1_mul c r]
      _ = e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) := by
            simp [corrLin]
      _ = ρA_C c (e0 (Submodule.Quotient.mk r)) := he0_mul c r
      _ = ρA_C c (corrLin (e1 (Submodule.Quotient.mk r))) := by
            simp [corrLin]
  let corr : ρA_C.Equiv ρA_C := Representation.Equiv.mk corrLin fun g ↦ by
    ext x
    exact hcorrInter.isIntertwining g x
  refine ⟨corr, ?_, hcorrw⟩
  -- Forgetting the equivariant structure leaves the already proved reduction identity.
  simpa [corr] using hcorrRedLin

/-- Helper for Theorem 17-17.3-1: on the lifted cyclic `C`-module, a `C`-equivariant
endomorphism is the identity as soon as it fixes the chosen generator `w0`. -/
private theorem character_field_transport_endomorphism_eq_id_of_generator_local
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C W)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    {f : W →ₗ[A] W}
    (hf : ρA_C.IsIntertwiningMap ρA_C f)
    (hw0 : f w0 = w0) :
    f = LinearMap.id := by
  have hid : ρA_C.IsIntertwiningMap ρA_C (LinearMap.id : W →ₗ[A] W) := by
    -- The identity endomorphism commutes with the `C`-action tautologically.
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    rfl
  -- Generator extensionality turns equality at `w0` into equality on all of `W`.
  simpa using
    c_equivariant_endomorphism_ext_of_generator
      (A := A) (C := C) ρA_C w0 hspanLifted hf hid hw0

/-- Helper for Theorem 17-17.3-1: the identity comparison already belongs to the transport fiber
over `1 ∈ P`. This is Serre's neutral normalized transport once the correction step is done. -/
private noncomputable def character_field_transport_fiber_one_local
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W) :
    Representation.Equiv
      (ρA_C.comp (MulAut.conjNormal (((1 : P) : G))⁻¹).toMonoidHom)
      ρA_C := by
  refine Representation.Equiv.mk (LinearEquiv.refl A W) ?_
  intro a
  ext x
  simp [MulAut.conjNormal_apply]

/-- Helper for Theorem 17-17.3-1: transport fibers compose by reusing the same carrier map for
the second factor after conjugating its source action by the first factor. This is the literal
source-faithful multiplication law before normalization is imposed. -/
private noncomputable def character_field_transport_fiber_comp_local
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    {s t : P}
    (u :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C)
    (v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((t : G))⁻¹).toMonoidHom)
        ρA_C) :
    Representation.Equiv
      (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
      ρA_C := by
  let v_over_s :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom) := by
    -- The same carrier transport `v` still intertwines after conjugating both source actions by
    -- `s`; this is the source-level cocycle composition step.
    refine Representation.Equiv.mk v.toLinearEquiv ?_
    intro a
    ext x
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (v.isIntertwining' ((MulAut.conjNormal ((s : G))⁻¹) a)) x
  -- Compose the two transport operators in Serre's order: first `t`, then `s`.
  exact v_over_s.trans u

/-- Helper for Theorem 17-17.3-1: once two comparison maps have the same reduction formula and
both fix the chosen lifted generator, generator extensionality forces them to coincide. -/
private theorem character_field_transport_equiv_eq_of_reduction_and_generator_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    {s : P}
    {u v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C}
    (huRed :
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hvRed :
      red_C.comp v.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hu0 : u w0 = w0)
    (hv0 : v w0 = w0) :
    u = v := by
  let σs :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A
  have hu_eval : ∀ y : W, red_C (u y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) huRed
  have hv_eval : ∀ y : W, red_C (v y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) hvRed
  let e : Representation.Equiv ρA_C ρA_C := u.symm.trans v
  have hred_e : red_C.comp e.toLinearMap = red_C := by
    -- The defect map reduces to the identity because both comparisons have the same reduced
    -- action.
    apply LinearMap.ext
    intro x
    calc
      red_C (e x) = red_C (v (u.symm x)) := rfl
      _ = σs (red_C (u.symm x)) := hv_eval (u.symm x)
      _ = red_C (u (u.symm x)) := by
            symm
            exact hu_eval (u.symm x)
      _ = red_C x := by
            simpa using congrArg red_C (u.apply_symm_apply x)
  have huSymm0 : u.symm w0 = w0 := by
    calc
      u.symm w0 = u.symm (u w0) := by rw [hu0]
      _ = w0 := by simpa using (u.symm_apply_apply w0)
  have hw0_e : e w0 = w0 := by
    -- Both comparisons fix `w0`, so their defect endomorphism also fixes `w0`.
    change v (u.symm w0) = w0
    rw [huSymm0, hv0]
  have heInter : ρA_C.IsIntertwiningMap ρA_C e.toLinearMap := by
    -- Forgetting the equivalence keeps the underlying `C`-equivariant endomorphism.
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    exact LinearMap.congr_fun (e.isIntertwining' c) x
  have he_id : e.toLinearMap = LinearMap.id := by
    -- The cyclic-generator lemma turns the fixed-generator condition into triviality.
    exact
      character_field_transport_endomorphism_eq_id_of_generator_local
        (A := A) (C := C) ρA_C w0 hspanLifted heInter hw0_e
  ext x
  -- Evaluate the defect identity at `u x` to recover equality of the original comparisons.
  have hx :
      e.toLinearMap (u x) = (LinearMap.id : W →ₗ[A] W) (u x) := by
    simpa using congrArg (fun f : W →ₗ[A] W ↦ f (u x)) he_id
  calc
    u x = (LinearMap.id : W →ₗ[A] W) (u x) := rfl
    _ = e.toLinearMap (u x) := hx.symm
    _ = v (u.symm (u x)) := rfl
    _ = v x := by rw [u.symm_apply_apply]

/-- Helper for Theorem 17-17.3-1: if two normalized comparisons satisfy the expected reduction
formulas for `s` and `t`, then their Serre-style composition has the expected reduction formula
for `s * t`. -/
private theorem character_field_transport_fiber_comp_reduction_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    {s t : P}
    {u :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C}
    {v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((t : G))⁻¹).toMonoidHom)
        ρA_C}
    (huRed :
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hvRed :
      red_C.comp v.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) t).toLinearMap.restrictScalars A).comp
          red_C)) :
    red_C.comp
        (character_field_transport_fiber_comp_local (A := A) (G := G) (P := P)
          (C := C) ρA_C u v).toLinearMap =
      (((restricted_conjugation_equiv_of_p_local
          (ρ := ρ) (C := C) (inferInstance : C.Normal) (s * t)).toLinearMap.restrictScalars A).comp
        red_C) := by
  let σs :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A
  let σt :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) t).toLinearMap.restrictScalars A
  let σst :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) (s * t)).toLinearMap.restrictScalars A
  have hu_eval : ∀ y : W, red_C (u y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) huRed
  have hv_eval : ∀ y : W, red_C (v y) = σt (red_C y) := by
    intro y
    simpa [σt, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) hvRed
  apply LinearMap.ext
  intro x
  -- The raw composed transport reduces to `ρ s ∘ ρ t`, hence to `ρ (s * t)`.
  calc
    red_C ((character_field_transport_fiber_comp_local
        (A := A) (G := G) (P := P) (C := C) ρA_C u v) x)
        = red_C (u (v x)) := rfl
    _ = σs (red_C (v x)) := hu_eval (v x)
    _ = σs (σt (red_C x)) := by rw [hv_eval x]
    _ = ρ (s : G) (ρ (t : G) (red_C x)) := rfl
    _ = ρ (((s * t : P) : G)) (red_C x) := by
          simpa [Module.End.mul_apply] using
            (LinearMap.congr_fun (ρ.map_mul (s : G) (t : G)) (red_C x)).symm
    _ = σst (red_C x) := rfl

/-- Helper for Theorem 17-17.3-1: once the normalized comparisons are available, the fixed
generator `w0` forces the normalized family to satisfy Serre's multiplicativity law. -/
private theorem character_field_transport_normalized_multiplicative_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (uNorm :
      ∀ s : P,
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C)
    (huRed :
      ∀ s : P,
        red_C.comp (uNorm s).toLinearMap =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
            red_C))
    (hu0 : ∀ s : P, uNorm s w0 = w0) :
    uNorm 1 =
        character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C ∧
      ∀ s t : P,
        character_field_transport_fiber_comp_local
            (A := A) (G := G) (P := P) (C := C) ρA_C (uNorm s) (uNorm t) =
          uNorm (s * t) := by
  have honeRed :
      red_C.comp
          (character_field_transport_fiber_one_local
            (A := A) (G := G) (P := P) (C := C) ρA_C).toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) (1 : P)).toLinearMap.restrictScalars A).comp
          red_C) := by
    -- At `1`, the transport fiber is the identity map, and the reduced action is `ρ 1 = id`.
    apply LinearMap.ext
    intro x
    calc
      red_C ((character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C) x)
          = red_C x := by
              change red_C x = red_C x
              rfl
      _ = ρ (1 : G) (red_C x) := by
            simpa using (LinearMap.congr_fun ρ.map_one (red_C x)).symm
      _ =
          ((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) (inferInstance : C.Normal) (1 : P)).toLinearMap.restrictScalars A)
            (red_C x) := rfl
  have hone0 :
      (character_field_transport_fiber_one_local
        (A := A) (G := G) (P := P) (C := C) ρA_C) w0 = w0 := by
    change w0 = w0
    rfl
  constructor
  · -- The normalized comparison at `1` is uniquely forced by the reduction formula and the fact
    -- that it fixes `w0`.
    exact
      character_field_transport_equiv_eq_of_reduction_and_generator_local
        (A := A) (G := G) (V := V) (C := C) (P := P)
        (ρ := ρ) (ρA_C := ρA_C) (red_C := red_C) (w0 := w0) (hspanLifted := hspanLifted)
        (u := uNorm 1)
        (v := character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C)
        (huRed := huRed 1)
        (hvRed := honeRed)
        (hu0 := hu0 1)
        (hv0 := hone0)
  · intro s t
    -- The Serre-style product comparison has the correct reduced action and still fixes `w0`, so
    -- uniqueness on the cyclic generator identifies it with `uNorm (s * t)`.
    apply
      character_field_transport_equiv_eq_of_reduction_and_generator_local
        (A := A) (G := G) (V := V) (C := C) (P := P)
        ρ ρA_C red_C w0 hspanLifted
    · exact
        character_field_transport_fiber_comp_reduction_local
          (A := A) (G := G) (V := V) (C := C) (P := P)
          ρ ρA_C red_C (huRed s) (huRed t)
    · exact huRed (s * t)
    · change uNorm s (uNorm t w0) = w0
      rw [hu0 t, hu0 s]
    · exact hu0 (s * t)

/-- Helper for Theorem 17-17.3-1: once the `P`-fixed vector and orbit-span checkpoints are
established and a lift of the restricted `C`-representation is chosen, the only remaining work in
the isotypic branch is the character-field transport of the `P`-action to that chosen lift. -/
private theorem character_field_transport_extends_lift
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCndvd : ¬ p ∣ Nat.card C)
    (hCyclic : IsCyclic C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hν0 : ν ≠ 0)
    (hw0 : red_C w0 = ν)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤) :
    ∃ ρA : Representation A G W,
      IsResidueFieldLift ρ ρA red_C := by
  -- Route correction: the cyclic generator `w0` and its lifted orbit span are already fixed, so
  -- the only remaining source-faithful step is to normalize each conjugate comparison so it fixes
  -- `w0` and then assemble those normalized maps into the ambient `P`-action.
  let _ := hC
  let _ := hCP
  let _ := hCndvd
  let _ := hCyclic
  let _ := hLiftC
  let _ := hν0
  let _ := hw0
  let _ := hνfixed
  let _ := hOrbitSpan
  let _ := hspanLifted
  letI : CommGroup C := IsCyclic.commGroup
  have hConjCompare :
      ∀ s : P,
        ∃ u :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp u.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            red_C (u w0) = ν := by
    intro s
    -- The conjugated lift is now packaged exactly as in Serre's source route, and the comparison
    -- already sends `w0` to another lift of the same residue generator `ν`.
    exact
      character_field_transport_conjugate_lift_compare_fixed_vector_local
        (A := A) (G := G) (p := p) (V := V) (C := C) (P := P)
        ρ hC hCndvd ρA_C red_C hLiftC w0 ν hw0 hνfixed s
  have hCompareSpan :
      ∀ s : P,
        ∃ u :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp u.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            red_C (u w0) = ν ∧
            Submodule.span A (Set.range fun c : C ↦ ρA_C c (u w0)) = ⊤ := by
    intro s
    rcases hConjCompare s with ⟨u, huRed, huw0⟩
    refine ⟨u, huRed, huw0, ?_⟩
    -- The comparison vector `u w0` is another lift of `ν`, so it generates the same lifted
    -- cyclic `C`-module by the previously established Nakayama step.
    exact
      character_field_transport_compare_generator_span_local
        (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC (u w0) ν huw0 hOrbitSpan
  classical
  have hNormExists :
      ∀ s : P,
        ∃ uNorm :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp uNorm.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            uNorm w0 = w0 := by
    intro s
    rcases hCompareSpan s with ⟨u, huRed, huw1, hspan1⟩
    rcases
        character_field_transport_correction_equiv_local
          (A := A) (G := G) (C := C) (ρ := ρ)
          ρA_C red_C hLiftC w0 (u w0) ν hw0 huw1 hspanLifted hspan1 with
      ⟨corr, hcorrRed, hcorrw⟩
    let uNorm :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C := u.trans corr
    refine ⟨uNorm, ?_, hcorrw⟩
    -- The correction map preserves reduction, so the normalized transport keeps Serre's reduced
    -- comparison formula while now fixing `w0`.
    apply LinearMap.ext
    intro x
    calc
      red_C (uNorm x) = red_C (corr (u x)) := rfl
      _ = red_C (u x) := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : W →ₗ[A] V ↦ f (u x)) hcorrRed
      _ =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A).comp red_C) x := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : W →ₗ[A] V ↦ f x) huRed
  let uNorm :
      ∀ s : P,
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C :=
    fun s ↦ Classical.choose (hNormExists s)
  have huNormRed :
      ∀ s : P,
        red_C.comp (uNorm s).toLinearMap =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A).comp red_C) := by
    intro s
    exact (Classical.choose_spec (hNormExists s)).1
  have huNorm0 : ∀ s : P, uNorm s w0 = w0 := by
    intro s
    exact (Classical.choose_spec (hNormExists s)).2
  have hNormOneMul :
      uNorm 1 =
          character_field_transport_fiber_one_local
            (A := A) (G := G) (P := P) (C := C) ρA_C ∧
        ∀ s t : P,
          character_field_transport_fiber_comp_local
              (A := A) (G := G) (P := P) (C := C) ρA_C (uNorm s) (uNorm t) =
            uNorm (s * t) :=
    character_field_transport_normalized_multiplicative_local
      (A := A) (G := G) (V := V) (C := C) (P := P)
      ρ ρA_C red_C w0 hspanLifted uNorm huNormRed huNorm0
  rcases hNormOneMul with ⟨hNormOne, hNormMul⟩
  have huNorm_one_apply : ∀ x : W, uNorm 1 x = x := by
    intro x
    rw [hNormOne]
    rfl
  have huNorm_mul_apply : ∀ s t : P, ∀ x : W, uNorm (s * t) x = uNorm s (uNorm t x) := by
    intro s t x
    simpa [character_field_transport_fiber_comp_local] using
      congrArg (fun e :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
          ρA_C ↦ e x) (hNormMul s t).symm
  have huNorm_comm :
      ∀ s : P, ∀ c : C, ∀ x : W,
        uNorm s (ρA_C c x) =
          ρA_C ((MulAut.conjNormal ((s : G)) c)) (uNorm s x) := by
    intro s c x
    -- Evaluate the normalized transport on the conjugate of `c`; the source action simplifies
    -- back to the original `c`-action.
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun ((uNorm s).isIntertwining' ((MulAut.conjNormal ((s : G)) c))) x
  let split : G → C × P := fun g ↦ Classical.choose (hCP.2 g)
  have hsplit_spec : ∀ g : G, ((split g).1 : G) * ((split g).2 : G) = g := by
    intro g
    exact Classical.choose_spec (hCP.2 g)
  have hsplit_one : split (1 : G) = ((1 : C), (1 : P)) := by
    apply hCP.1
    simpa using hsplit_spec (1 : G)
  have hsplit_mul :
      ∀ g h : G,
        split (g * h) =
          ((split g).1 * (MulAut.conjNormal ((split g).2 : G) ((split h).1)),
            (split g).2 * (split h).2) := by
    intro g h
    apply hCP.1
    calc
      (((split (g * h)).1 : C) : G) * (((split (g * h)).2 : P) : G) = g * h := hsplit_spec (g * h)
      _ = ((((split g).1 : C) : G) * (((split g).2 : P) : G)) *
            ((((split h).1 : C) : G) * (((split h).2 : P) : G)) := by
              rw [hsplit_spec g, hsplit_spec h]
      _ =
          ((((split g).1 * (MulAut.conjNormal ((split g).2 : G) ((split h).1)) : C) : G) *
            ((((split g).2 * (split h).2 : P) : G))) := by
              simp [MulAut.conjNormal_apply, mul_assoc]
  let ρA : Representation A G W :=
    { toFun := fun g =>
        let c : C := (split g).1
        let s : P := (split g).2
        { toFun := fun x ↦ ρA_C c (uNorm s x)
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro a x
            simp }
      map_one' := by
        ext x
        -- The normalized family is trivial at `1`, so the factorized action recovers `ρA_C 1 = id`.
        change ρA_C ((split 1).1) (uNorm ((split 1).2) x) = x
        rw [hsplit_one]
        simpa using huNorm_one_apply x
      map_mul' := by
        intro g h
        ext x
        let cg : C := (split g).1
        let sg : P := (split g).2
        let ch : C := (split h).1
        let sh : P := (split h).2
        -- Rewrite the `C`-component of `g * h` using the complement factorization, then move the
        -- `C`-action across the normalized `P`-transport.
        rw [hsplit_mul]
        change
          ρA_C (cg * MulAut.conjNormal (sg : G) ch) (uNorm (sg * sh) x) =
            ρA_C cg (uNorm sg (ρA_C ch (uNorm sh x)))
        rw [huNorm_mul_apply]
        calc
          ρA_C (cg * MulAut.conjNormal (sg : G) ch) (uNorm sg (uNorm sh x))
              = ρA_C cg (ρA_C (MulAut.conjNormal (sg : G) ch) (uNorm sg (uNorm sh x))) := by
                  simpa [Module.End.mul_apply] using
                    LinearMap.congr_fun (ρA_C.map_mul cg (MulAut.conjNormal (sg : G) ch))
                      (uNorm sg (uNorm sh x))
          _ = ρA_C cg (uNorm sg (ρA_C ch (uNorm sh x))) := by
                rw [huNorm_comm sg ch (uNorm sh x)] }
  have hinter : ρA.IsIntertwiningMap (ρ.restrictScalars A) red_C := by
    rw [Representation.isIntertwiningMap_iff]
    intro g x
    let c : C := (split g).1
    let s : P := (split g).2
    have hRedC :
        red_C (ρA_C c (uNorm s x)) =
          (Representation.restrictScalars A (ρ.comp C.subtype)) c (red_C (uNorm s x)) := by
      simpa [Representation.restrictScalars_apply] using
        (residueFieldLift_isIntertwining_restrictScalars
          (A := A) (σ := ρ.comp C.subtype) hLiftC).isIntertwining c (uNorm s x)
    have hRedP :
        red_C (uNorm s x) =
          ((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A) (red_C x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : W →ₗ[A] V ↦ f x) (huNormRed s)
    -- The normalized `P`-transport has the prescribed reduced action, so the factorized `G`
    -- action intertwines with `red_C`.
    calc
      red_C (ρA g x) = red_C (ρA_C c (uNorm s x)) := rfl
      _ = (Representation.restrictScalars A (ρ.comp C.subtype)) c (red_C (uNorm s x)) := hRedC
      _ =
          (Representation.restrictScalars A (ρ.comp C.subtype)) c
            (((restricted_conjugation_equiv_of_p_local
                (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A) (red_C x)) := by
              rw [hRedP]
      _ = ρ (c : G) (ρ (s : G) (red_C x)) := rfl
      _ = ρ (((c : C) : G) * ((s : P) : G)) (red_C x) := by
            simpa [Module.End.mul_apply] using
              (LinearMap.congr_fun (ρ.map_mul ((c : C) : G) ((s : P) : G)) (red_C x)).symm
      _ = ρ g (red_C x) := by rw [hsplit_spec g]
      _ = (ρ.restrictScalars A) g (red_C x) := by rfl
  have hraw :
      RawIsResidueFieldReduction_local (A := A) ρ ρA red_C :=
    residueFieldReduction_of_isBaseChange_isIntertwining
      (A := A) (G' := G) (ρ := ρ) (ρA := ρA) hLiftC.1 hinter
  refine ⟨ρA, ?_⟩
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hraw

/-- Helper for Theorem 17-17.3-1: once the fixed vector and orbit-span checkpoints are in place,
the chosen `C`-lift can be extended to `G` after supplying the coprimality witness on `C`. -/
private theorem exists_residueFieldLift_of_character_field_transport
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCndvd : ¬ p ∣ Nat.card C)
    (hCyclic : IsCyclic C)
    (hIso :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k C) V)
    (ν : V) (hν0 : ν ≠ 0)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤)
    (hLiftC :
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
        (_ : Module.Free A W) (_ : Module.Finite A W)
        (ρA_C : Representation A C W)
        (red_C : W →ₗ[A] V),
          IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hLiftC with ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA_C, red_C, hLiftC⟩
  letI : AddCommGroup W := hWadd
  letI : Module A W := hWmod
  letI : Module.Free A W := hWfree
  letI : Module.Finite A W := hWfinite
  letI : Module A (IsLocalRing.ResidueField A) := Algebra.toModule
  let _ := hν0
  have hred_surj : Function.Surjective red_C :=
    residueFieldLift_surjective (A := A) hLiftC
  obtain ⟨w0, hw0⟩ := hred_surj ν
  have hspanLifted :
      Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤ := by
    -- Route correction: the lifted orbit span is now upgraded to `⊤` before we normalize the
    -- comparison isomorphisms. This follows Serre's source proof more faithfully than trying to
    -- build the `P`-action first and only then recover generation.
    exact
      cyclic_lift_span_top_of_fixed_lift
        (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC w0 ν hw0 hOrbitSpan
  rcases
      character_field_transport_extends_lift
        (A := A) (G := G) (V := V) (C := C) (P := P) (ρ := ρ) hC hCP hCndvd hCyclic
        ρA_C red_C hLiftC w0 ν hν0 hw0 hνfixed hOrbitSpan hspanLifted with
    ⟨ρA, hLift⟩
  -- The lifted `C`-module is fixed above; after extending its action from `C` to `G`, the
  -- residue-field reduction map is unchanged.
  let _ := hIso
  let _ := hOrbitSpan
  exact ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA, red_C, hLift⟩

/-- Helper for Theorem 17-17.3-1: if the restriction to `C` is isotypic, Serre's multiplicity
space argument produces the desired residue-field lift. -/
lemma exists_residueFieldLift_of_restriction_isotypic
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIso :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k C) V) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  let ρC : Representation k C V := ρ.comp C.subtype
  let ρP : Representation k P V := ρ.comp P.subtype
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial V := nontrivial_of_isIrreducible_local (ρ := ρ)
  have hCndvd : ¬ p ∣ Nat.card C := hp.coprime_iff_not_dvd.mp hCoprime
  have hPinv : ρP.invariants ≠ ⊥ := by
    -- Serre's first checkpoint in the isotypic branch is the existence of a nonzero `P`-fixed
    -- vector in characteristic `p`.
    simpa [ρP] using invariants_ne_bot_of_isPGroup_charP ρP hP
  obtain ⟨ν, hνinv, hν0⟩ := ρP.invariants.ne_bot_iff.mp hPinv
  have hνfixed : ∀ s : P, ρP s ν = ν := by
    -- Unpack membership in the invariant subspace as the fixed-vector relation.
    exact (ρP.mem_invariants ν).mp hνinv
  have hOrbitSpan :
      Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤ := by
    -- Serre's orbit-span checkpoint is now closed: the `C`-orbit of the nonzero `P`-fixed vector
    -- spans a nonzero `G`-stable subrepresentation, hence all of `V` by irreducibility.
    exact
      c_orbit_span_eq_top_of_fixed_vector
        (ρ := ρ) hC hCP ν hν0 fun s ↦ by
          simpa [ρP] using hνfixed s
  have hLiftC :
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
        (_ : Module.Free A W) (_ : Module.Finite A W)
        (ρA_C : Representation A C W)
        (red_C : W →ₗ[A] V),
          IsResidueFieldLift ρC ρA_C red_C := by
    -- Chapter `15` already lifts the restricted `C`-representation because `|C|` is prime to `p`.
    exact exists_residueFieldLift_of_non_dvd_card (A := A) (p := p) hCndvd ρC
  -- Route correction: the fixed-vector and orbit-span part of Serre's argument is now completed
  -- here. The only remaining blocker is the character-field transport from the chosen `C`-lift to
  -- an ambient `G`-lift.
  exact
    exists_residueFieldLift_of_character_field_transport
      (A := A) (G := G) (V := V) (C := C) (P := P) ρ hC hCP hCndvd hCyclic hIso ν hν0
      (fun s ↦ by simpa [ρP] using hνfixed s) hOrbitSpan hLiftC

/-- Helper for Theorem 17-17.3-1: explicit cardinal induction isolates the proper-overgroup
recursion from the genuinely new induced-transport and isotypic-model blockers. -/
theorem exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_aux
    (hp : Nat.Prime p) :
    ∀ {n : ℕ} {G' : Type v} [Group G'] [Finite G']
      {V' : Type w} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      {C' P' : Subgroup G'}
      (hcard : Nat.card G' ≤ n)
      (hC' : C'.Normal) (hC'P' : C'.IsComplement' P') (hCyclic' : IsCyclic C')
      (hCoprime' : Nat.Coprime p (Nat.card C')) (hP' : IsPGroup p P')
      (ρ' : Representation k G' V') [ρ'.IsIrreducible],
        ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
          (_ : Module.Free A W') (_ : Module.Finite A W')
          (ρA' : Representation A G' W')
          (red' : W' →ₗ[A] V'),
            IsResidueFieldLift ρ' ρA' red' := by
  intro n
  induction n with
  | zero =>
      intro G' _ _ V' _ _ _ C' P' hcard hC' hC'P' hCyclic' hCoprime' hP' ρ' _
      have hfalse : False := (Nat.not_lt_of_ge hcard) Nat.card_pos
      exact False.elim hfalse
  | succ n ihn =>
      intro G' _ _ V' _ _ _ C' P' hcard hC' hC'P' hCyclic' hCoprime' hP' ρ' _
      have hGsolv : IsPSolvable p G' :=
        isPSolvable_of_cyclicNormalByPGroupDecomposition hC' hC'P' hCoprime' hP'
      let ρC : Representation k C' V' := ρ'.comp C'.subtype
      have hsemiC :
          letI : Module (MonoidAlgebra k C') V' := ρC.instModuleMonoidAlgebraAsModule
          IsSemisimpleModule (MonoidAlgebra k C') V' :=
        isSemisimpleModule_asModule_of_coprime_card
          (A := A) (G := G') (p := p) hp hCoprime' ρC
      have hrecSame :
          ∀ {H : Subgroup G'} {W0 : Type w} [AddCommGroup W0] [Module k W0]
            [FiniteDimensional k W0]
            {C0 P0 : Subgroup H}
            (hH : H < ⊤)
            (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
            (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
            (σ : Representation k H W0) [σ.IsIrreducible],
              ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
                (_ : Module.Free A W') (_ : Module.Finite A W')
                (ρA_H : Representation A H W')
                (red_H : W' →ₗ[A] W0),
                  IsResidueFieldLift σ ρA_H red_H := by
        intro H W0 _ _ _ C0 P0 hH hC0 hC0P0 hC0cyc hC0cop hP0 σ _
        -- Descend the outer cardinal induction from `G'` to the proper subgroup `H`.
        exact
          exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_of_proper_subgroup
            (A := A) (G := G') (p := p) (n := n)
            (hrec := fun {G''} [Group G''] [Finite G'']
              {V''} [AddCommGroup V''] [Module k V''] [FiniteDimensional k V'']
              {C'' P'' : Subgroup G''}
              hC'' hC''P'' hCyclic'' hCoprime'' hP'' hcard'' ρ'' ↦
                ihn hcard'' hC'' hC''P'' hCyclic'' hCoprime'' hP'' ρ'')
            H hH hC0 hC0P0 hC0cyc hC0cop hP0 σ hcard
      -- Follow Serre's two-branch Clifford split on the restricted `C'`-module.
      have hsplit :
          (∃ H : Subgroup G',
            C' ≤ H ∧ H < ⊤ ∧
              ∃ W : Subrepresentation (ρ'.comp H.subtype),
                W.toRepresentation.IsIrreducible ∧ ρ'.IsInducedFromSubrepresentation H W) ∨
            (let ρC : Representation k C' V' := ρ'.comp C'.subtype
             letI : Module (MonoidAlgebra k C') V' := ρC.instModuleMonoidAlgebraAsModule
             IsIsotypic (MonoidAlgebra k C') V') :=
        exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restrict
          (A := A) (G := G') (V := V') (C := C') hC' ρ' hsemiC
      rcases hsplit with hproper | hIso
      · -- In the non-isotypic branch, recurse on the proper stabilizer overgroup.
        exact
          exists_residueFieldLift_of_proper_overgroup_induced
            (A := A) (G := G') (p := p) (V := V') (C := C') (P := P')
            hp hC' hC'P' hCyclic' hCoprime' hP' hrecSame ρ' hproper
      · -- In the isotypic branch, the remaining blocker is Serre's character-field construction.
        exact
          exists_residueFieldLift_of_restriction_isotypic
            (A := A) (G := G') (p := p) (V := V') (C := C') (P := P')
            hp hC' hC'P' hCyclic' hCoprime' hP' ρ' hIso

/-- Helper for Theorem 17-17.3-1: after ruling out the degenerate `p = 0` case, the cyclic
normal-by-`p` hypotheses reduce the lifting problem to the prime-characteristic Clifford/stabilizer
argument on a `p`-solvable group. -/
lemma exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Route correction: the proper-overgroup recursion now lives in the explicit cardinal-induction
  -- auxiliary, so this theorem is just its specialization to the ambient group order.
  exact
    exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_aux
      (A := A) (p := p) (G' := G) (V' := V) (C' := C) (P' := P)
      hp (le_rfl : Nat.card G ≤ Nat.card G) hC hCP hCyclic hCoprime hP ρ

/-- Theorem 17-17.3-1: let `k = IsLocalRing.ResidueField A` have characteristic `p`, with `A`
henselian local. If `G` is the semidirect product of a `p`-group complement `P` by a cyclic
normal subgroup `C` of order prime to `p`, then every finite-dimensional irreducible
representation of `G` over `k` admits a free finitely generated lift over `A`. Equivalently,
every simple finite-dimensional `k[G]`-module lifts to a free finitely generated `A[G]`-module. -/
theorem exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition
    (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Split off the degenerate `p = 0` case first; the genuine textbook content begins when `p` is
  -- prime, exactly as in Serre's theorem statement.
  rcases CharP.char_is_prime_or_zero k p with hp | hp0
  · -- The prime-characteristic branch is the only remaining frontier.
    exact
      exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime
        hp hC hCP hCyclic hCoprime hP ρ
  · -- In characteristic `0`, the Chapter `15` coprime-order theorem already gives the lift.
    exact
      exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_charZero
        (A := A) (G := G) (p := p) hp0 ρ

end

end Representation
