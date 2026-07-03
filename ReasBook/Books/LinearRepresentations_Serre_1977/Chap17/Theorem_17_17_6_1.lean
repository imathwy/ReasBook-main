import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelOwnerTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.QuotientHeightRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelCliffordSplit
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedProjectiveCoverData

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/- Domain-style sampling for Theorem 17-17.6-1:
* primary domain: modular lifting of irreducible representations across local rings for finite
  `p`-solvable groups;
* relevant owner declarations inspected in this domain:
  `IsPSolvable`,
  `IsPSolvableOfHeight.succ_iff`,
  `LinearMap.IsResidueFieldReduction`,
  `Representation.IsResidueFieldLift`,
  `Representation.exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition`,
  `Representation.isResidueFieldLift_comp`;
* best owner abstraction in this file: the source-facing group-theoretic predicate
  `IsPSolvable p G`, with the height-indexed recursive family `IsPSolvableOfHeight p h G` as the
  primitive recursive data and Theorem `17-17.3-1` as the cyclic-normal-by-`p`-group inductive
  step already owned upstream in the chapter;
* primitive data: the recursive normal-subgroup step encoded by `IsPSolvableOfHeight`;
* derived API: the owner-level `IsPSolvable` theorem, obtained from the height-indexed bridge
  below.

Source/core/bridge triage:
* source-facing: `Representation.exists_residueFieldLift_of_isIrreducible_of_isPSolvable`;
* core/canonical: `IsPSolvable` and `IsPSolvableOfHeight` for the group-theoretic hypotheses, and
  `LinearMap.IsResidueFieldReduction` for the reduction map;
* bridge/view: `Representation.IsResidueFieldLift` for the source-facing lifting language, and the
  height-indexed lifting theorem, which exposes the recursive witness driving the proof and from
  which the owner-level statement is recovered immediately.
-/

open scoped TensorProduct

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
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: the tautological inclusion of an `H`-stable subrepresentation
into the restricted ambient representation is an intertwining map. -/
private noncomputable def subrepresentation_inclusion_hom_generic
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (H : Subgroup G')
    (U : Subrepresentation (σ.comp H.subtype)) :
    U.toRepresentation.IntertwiningMap (σ.comp H.subtype) :=
  U.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    U.toRepresentation (σ.comp H.subtype) fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: a subrepresentation whose underlying owner submodule is `⊤`
is equivariantly the ambient representation. -/
private noncomputable def top_subrepresentation_equiv_of_toSubmodule_eq_top
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (U : Subrepresentation σ)
    (hU : U.toSubmodule = ⊤) :
    U.toRepresentation.Equiv σ := by
  have hU_top : U = ⊤ := Subrepresentation.toSubmodule_injective hU
  subst hU_top
  -- Once the subrepresentation is literally `⊤`, its inclusion is the identity on the carrier.
  refine Representation.Equiv.mk Submodule.topEquiv ?_
  intro g
  ext x
  rfl

/-- Helper for Theorem 17-17.6-1: multiplying a representation carrier by a scalar unit gives a
canonical self-equivalence of the same representation. -/
private theorem scalar_representation_self_equiv_isIntertwining
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (a : kˣ) :
    σ.IsIntertwiningMap σ (((a • LinearEquiv.refl k W : W ≃ₗ[k] W) : W →ₗ[k] W)) := by
  -- A scalar homothety commutes with every representation operator on the nose.
  refine Representation.IsIntertwiningMap.mk ?_
  intro g
  ext x
  simp [mul_comm]

/-- Helper for Theorem 17-17.6-1: package a scalar unit as the corresponding representation
self-equivalence. This keeps later transport corrections in the language of representation
equivalences instead of raw linear maps. -/
private noncomputable def scalar_representation_self_equiv
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (a : kˣ) :
    σ.Equiv σ :=
  Representation.Equiv.mk
    (a • LinearEquiv.refl k W)
    (scalar_representation_self_equiv_isIntertwining σ a)

/-- Helper for Theorem 17-17.6-1: once LinearRepresentations_Serre_1977's constituent `S̄` is fixed, the literal
multiplicity-space carrier is `Hom^I(S̄, V)`. Naming this owner avoids reopening the carrier
choice in later projective-extension lemmas. -/
private abbrev fixed_isotypic_multiplicity_space
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) : Type x :=
  Sbar.toRepresentation.IntertwiningMap (ρ.comp I.subtype)

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's multiplicity space `Hom^I(S̄, V)` is finite-dimensional,
since it sits inside the finite-dimensional space of all linear maps from `S̄` to `V`. -/
private noncomputable def fixed_isotypic_multiplicity_space_finiteDimensional
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    FiniteDimensional k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
  -- Unfold the carrier once; the ambient intertwining space inherits finite-dimensionality from
  -- the finite-dimensional source and target representations.
  dsimp [fixed_isotypic_multiplicity_space]
  infer_instance

/-- Helper for Theorem 17-17.6-1: changing the source constituent by an `I`-equivariant
equivalence transports LinearRepresentations_Serre_1977's multiplicity space by precomposition. This is the basic source-side
bridge needed before descending the `G₂`-action to the quotient module `τ`. -/
private noncomputable def fixed_isotypic_multiplicity_space_precompose_linearEquiv
    (I : Subgroup G)
    (ρ : Representation k G V)
    {Sbar T : Subrepresentation (ρ.comp I.subtype)}
    (e : Sbar.toRepresentation.Equiv T.toRepresentation) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) T ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar where
  toFun := fun f ↦ f.comp e.toIntertwiningMap
  invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
  left_inv := by
    intro f
    -- Precompose with `e` and then with `e.symm`; the source equivalence cancels on the nose.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  right_inv := by
    intro f
    -- The same cancellation works in the reverse direction.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  map_add' := by
    intro f g
    -- Precomposition is pointwise additive on intertwining maps.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  map_smul' := by
    intro a f
    -- Scalar multiplication commutes with the same source-side precomposition.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: the canonical transport equivalence `S̄ ≃ sS̄` identifies the
transported multiplicity space with the fixed one. This freezes the source-transport part of the
future `G₂`-action on `Hom^I(S̄, V)` into a reusable linear equivalence. -/
private noncomputable def transported_fixed_isotypic_multiplicity_space_linearEquiv
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fixed_isotypic_multiplicity_space_precompose_linearEquiv
    (I := I) (ρ := ρ) (transportedSubrepresentation_rep_equiv_local ρ Sbar s)

/-- Helper for Theorem 17-17.6-1: if the transport element already lies in the Hall kernel `I`,
then transporting the fixed constituent `S̄` does not change the underlying subrepresentation.
This isolates the literal `I`-stability fact needed in the remaining Hall-kernel comparison
branch. -/
private theorem transportedSubrepresentation_eq_self_of_mem_hall_kernel
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (x : I) :
    transportedSubrepresentation ρ Sbar (x : G) = Sbar := by
  apply Subrepresentation.toSubmodule_injective
  rw [transportedSubrepresentation_toSubmodule]
  ext y
  constructor
  · intro hy
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    -- Any transported vector still lies in `S̄` because `S̄` is `I`-stable.
    exact Sbar.apply_mem_toSubmodule x hz
  · intro hy
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ (x⁻¹ : I) y, ?_, ?_⟩
    · -- Apply the inverse Hall-kernel element to move back into the source of the transport map.
      exact Sbar.apply_mem_toSubmodule x⁻¹ hy
    · -- The ambient `G`-action by `x` cancels its inverse on the nose.
      simpa using LinearMap.congr_fun (ρ.map_mul (x : G) ((x⁻¹ : I) : G)) y

/-- Helper for Theorem 17-17.6-1: transporting a residue-field lift across a target
representation equivalence only changes the reduction map by postcomposition with that
equivalence. -/
private theorem residueFieldLift_of_equiv_target_local
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k G V'}
    {τ : Representation k G V}
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A G P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift σ ρA red)
    (e : σ.Equiv τ) :
    IsResidueFieldLift τ ρA ((e.toLinearMap.restrictScalars A).comp red) := by
  letI : Module (MonoidAlgebra A G) P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G) P :=
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
      -- The ambient `A[G]` action on the target factors through the residue-field scalar action.
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (MonoidAlgebra k G) (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  -- Move to the owner `IsResidueFieldReduction`: the base-change part transports along the target
  -- equivalence, and equivariance is then rewritten on the monoid-algebra generators.
  change (((e.toLinearMap.restrictScalars A).comp red).IsResidueFieldReduction G)
  change red.IsResidueFieldReduction G at hLift
  constructor
  · -- The tensor-product witness is transported directly along the target equivalence.
    exact isBaseChange_of_equiv_target (A := A) (V := V) e.toLinearEquiv hLift.1
  · refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    -- The monoid-algebra action commutes with the target equivalence one generator at a time.
    calc
      ((e.toLinearMap.restrictScalars A).comp red) (MonoidAlgebra.of A G g • x) =
          e (red (MonoidAlgebra.of A G g • x)) := by
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

/-- Helper for Theorem 17-17.6-1: transporting a residue-field lift across a source
representation equivalence only changes the reduction map by precomposition with that
equivalence. -/
private theorem residueFieldLift_of_equiv_source_local
    {G' : Type*} [Group G'] [Finite G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    [FiniteDimensional k V']
    {P' : Type*} [AddCommGroup P'] [Module A P']
    [Module.Free A P'] [Module.Finite A P']
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρ : Representation k G' V'}
    {ρA' : Representation A G' P'}
    {ρA : Representation A G' P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red)
    (e : ρA'.Equiv ρA) :
    IsResidueFieldLift ρ ρA' (red.comp e.toLinearMap) := by
  letI : Module (MonoidAlgebra A G') P' := Module.compHom P' ρA'.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA'.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA'.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x
  letI : Module A V' := Module.compHom V' (algebraMap A k)
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a x
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
                (IsScalarTower.algebraMap_smul (MonoidAlgebra k G') (IsLocalRing.residue A a) x)
      _ = a • x := by
            simpa [IsLocalRing.ResidueField.algebraMap_eq] using
              (IsScalarTower.algebraMap_smul k a x)
  change (red.comp e.toLinearMap).IsResidueFieldReduction G'
  change red.IsResidueFieldReduction G' at hLift
  constructor
  · -- The source carrier changes by an `A`-linear base-change equivalence, so compose the two
    -- base-change witnesses.
    have he : IsBaseChange A e.toLinearMap := IsBaseChange.ofEquiv e.toLinearEquiv
    simpa [LinearMap.comp_assoc] using
      (IsBaseChange.comp (R := A) (S := A) (T := k) he hLift.1)
  · -- Check equivariance on the generators `MonoidAlgebra.of A G' g`.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq0 : e (ρA' g x) = ρA g (e x) := by
      exact LinearMap.congr_fun (e.isIntertwining' g) x
    have hρA' : (MonoidAlgebra.single g (1 : A)) • x = ρA' g x := by
      change (ρA'.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x = ρA' g x
      simp [Representation.asAlgebraHom_single]
    have hρA : ρA g (e x) = (MonoidAlgebra.single g (1 : A)) • e x := by
      change ρA g (e x) = (ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) (e x)
      simp [Representation.asAlgebraHom_single]
    have hstart :
        (red.comp e.toLinearMap) (((Representation.ofModule' P' : Representation A G' P') g) x) =
          red (e ((MonoidAlgebra.single g (1 : A)) • x)) := by
      simp [Representation.ofModule', LinearMap.comp_apply]
    have hstep1 :
        red (e ((MonoidAlgebra.single g (1 : A)) • x)) = red (e (ρA' g x)) := by
      rw [hρA']
    have hstep2 : red (e (ρA' g x)) = red (ρA g (e x)) := by
      rw [heq0]
    have hstep3 :
        red (ρA g (e x)) = red ((MonoidAlgebra.single g (1 : A)) • e x) := by
      rw [hρA]
    have hstep4 :
        red ((MonoidAlgebra.single g (1 : A)) • e x) =
          MonoidAlgebra.single g (1 : k) • red (e x) := by
      exact LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hLift g (e x)
    have hfinal :
        MonoidAlgebra.single g (1 : k) • red (e x) =
          ((Representation.ofModule' V') : Representation A G' V') g
            ((red.comp e.toLinearMap) x) := by
      change
        MonoidAlgebra.single g (1 : k) • red (e x) =
          (MonoidAlgebra.mapRingHom G' (algebraMap A k) (MonoidAlgebra.single g (1 : A))) •
            ((red.comp e.toLinearMap) x)
      simp [LinearMap.comp_apply]
    exact hstart.trans <| hstep1.trans <| hstep2.trans <| hstep3.trans <| hstep4.trans hfinal

/-- Helper for Theorem 17-17.6-1: a lifted `A[G']`-representation may be moved into the common
witness universe by `ULift` without changing its action. -/
private def uliftRepresentation_witness
    {G' : Type v} [Group G']
    {P : Type u} [AddCommGroup P] [Module A P]
    (ρA : Representation A G' P) :
    Representation A G' (ULift.{max v x, u} P) where
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

/-- Helper for Theorem 17-17.6-1: raising the lifted source carrier to the common witness universe
preserves the residue-field lift. -/
private theorem residueFieldLift_ulift_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    {P : Type u} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    IsResidueFieldLift ρ (uliftRepresentation_witness (A := A) ρA)
      (red.comp (ULift.moduleEquiv : ULift.{max v x, u} P ≃ₗ[A] P).toLinearMap) := by
  -- Specialize the general source-side transport bridge to the `ULift` carrier equivalence.
  let eU :
      (uliftRepresentation_witness (A := A) ρA).Equiv ρA :=
    Representation.Equiv.mk ULift.moduleEquiv fun g ↦ by
      -- Both actions are definitionally the same after inserting the `ULift` wrapper.
      ext x
      rfl
  simpa using
    residueFieldLift_of_equiv_source_local (A := A) (ρ := ρ) (ρA := ρA) hLift eU

/-- Helper for Theorem 17-17.6-1: any free finite `A[G']`-model can be transported to the
same-universe coordinate module `Fin (finrank_A P) → A`, and the residue-field lift transports
along that source equivalence. -/
private theorem residueFieldLift_same_universe_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module A P')
      (_ : Module.Free A P') (_ : Module.Finite A P')
      (ρA' : Representation A G' P')
      (red' : P' →ₗ[A] V'),
        IsResidueFieldLift ρ ρA' red' := by
  letI : Module A A := Semiring.toModule
  let n := Module.finrank A P
  let P' : Type u := Fin n → A
  letI : AddCommGroup P' := Pi.addCommGroup
  letI : Module A P' := Pi.Function.module (Fin n) A A
  letI : Module.Free A P' := Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A P' := Module.Finite.of_basis (Pi.basisFun A (Fin n))
  let e : P ≃ₗ[A] P' := (Module.finBasis A P).equivFun
  let ρA' : Representation A G' P' :=
    { toFun := fun g ↦ e.conj (ρA g)
      map_one' := by
        calc
          e.conj (ρA 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eRep : ρA'.Equiv ρA :=
    Representation.Equiv.mk e.symm fun g ↦ by
      apply LinearMap.ext
      intro x
      change e.symm (e (ρA g (e.symm x))) = ρA g (e.symm x)
      simp
  refine
    ⟨P', inferInstance, inferInstance, inferInstance, inferInstance, ρA',
      red.comp e.symm.toLinearMap, ?_⟩
  simpa using
    residueFieldLift_of_equiv_source_local (A := A) (ρ := ρ) (ρA := ρA)
      hLift eRep

/-- Helper for Theorem 17-17.6-1: the Chapter `17.3` prime-to-`p` lifting theorem can be
repackaged into the common witness universe used by this file. -/
private theorem exists_residueFieldLift_of_non_dvd_card_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (hGcop : ¬ p ∣ Nat.card G')
    (ρ : Representation k G' V') :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
        IsResidueFieldLift ρ ρA red := by
  -- Choose the Chapter `17.3` lift in universe `u`, then move it into the common witness
  -- universe by `ULift`.
  rcases
      Representation.exists_residueFieldLift_of_non_dvd_card
        (A := A) (p := p) (H := G') hGcop ρ with
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  refine
    ⟨ULift.{max v x, u} P, inferInstance, inferInstance, inferInstance, inferInstance,
      uliftRepresentation_witness (A := A) ρA,
      red.comp (ULift.moduleEquiv : ULift.{max v x, u} P ≃ₗ[A] P).toLinearMap, ?_⟩
  exact residueFieldLift_ulift_witness (A := A) (ρ := ρ) hLift

/-- Helper for Theorem 17-17.6-1: if a normal subgroup acts trivially and the quotient lift is
already known in the common witness universe, inflating it back yields a lift of the ambient
representation in the same witness universe. -/
private theorem exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (ρ : Representation k G' V')
    (I : Subgroup G') [I.Normal]
    [Representation.IsTrivial (ρ.comp I.subtype)]
    (hquotLift :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A (G' ⧸ I) P)
        (red : P →ₗ[A] V'),
          IsResidueFieldLift (ρ.ofQuotient I) ρA red) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
        IsResidueFieldLift ρ ρA red := by
  rcases hquotLift with ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  -- Inflate the quotient lift and then rewrite the source representation by the trivial-kernel
  -- comparison from the quotient recursion helper file.
  refine ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA.comp (QuotientGroup.mk' I), red, ?_⟩
  have hLift' :
      IsResidueFieldLift
        ((ρ.ofQuotient I).comp (QuotientGroup.mk' I))
        (ρA.comp (QuotientGroup.mk' I))
        red :=
    Representation.isResidueFieldLift_comp hLift (QuotientGroup.mk' I)
  rw [quotient_inflation_eq_original_of_isTrivial (ρ := ρ) (I := I)]
  exact hLift'

/-- Helper for Theorem 17-17.6-1: in the proper-overgroup branch, the same-height recursion on the
stabilizer overgroup already produces a residue-field lift of the inducing subrepresentation. -/
private theorem exists_residueFieldLift_of_proper_overgroup_subrepresentation
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        I ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ H : Subgroup G, ∃ hIH : I ≤ H, ∃ hHlt : H < ⊤,
      ∃ W : Subrepresentation (ρ.comp H.subtype),
        ∃ hInd : ρ.IsInducedFromSubrepresentation H W,
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W.toSubmodule),
              IsResidueFieldLift W.toRepresentation ρA red := by
  rcases hproper with ⟨H, hIH, hHlt, W, hWirred, hInd⟩
  have hHquot :
      IsPSolvableOfHeight p h (H.map (QuotientGroup.mk' I)) := by
    -- The quotient image of the stabilizer overgroup inherits the lower-height hypothesis.
    exact (proper_overgroup_quotient_data (p := p) (h := h) I H hIH hHlt hquot).2.1
  have hHsolv : IsPSolvableOfHeight p (Nat.succ h) H := by
    -- Reinsert the same coprime Hall kernel inside `H` to recover the same-height recursion.
    exact
      isPSolvableOfHeight_succ_of_normal_coprime_subgroup_and_quotient_map
        (p := p) (h := h) I H hIH hIcop hHquot
  letI : W.toRepresentation.IsIrreducible := hWirred
  rcases hrecSame hHlt hHsolv W.toRepresentation with
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩
  -- This packages the entire recursive subgroup step so the ambient branch only has to induce
  -- the resulting lift back to `G`.
  exact
    ⟨H, hIH, hHlt, W, hInd, P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩

/-- Helper for Theorem 17-17.6-1: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
private noncomputable def comp_subtype_equiv_local
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G') :
    Representation.Equiv (ρ₁.comp H.subtype) (ρ₂.comp H.subtype) := by
  -- Restricting an intertwining equivalence does not change its pointwise formula.
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro h
  simpa using e.isIntertwining' (h : G')

/-- Helper for Theorem 17-17.6-1: transporting the inducing subrepresentation across an ambient
equivalence transports each quotient summand by mapping through the same linear equivalence. -/
private theorem leftQuotientSubmodule_eq_map_of_equiv_local
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype)) (q : G' ⧸ H) :
    ρ₂.leftQuotientSubmodule H
        (subrepresentationOrderIso_local (comp_subtype_equiv_local e H) U) q =
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

/-- Helper for Theorem 17-17.6-1: inducedness data is preserved when the ambient representation is
replaced by an equivalent one. -/
private theorem isInducedFromSubrepresentation_of_equiv_local
    {G' : Type*} [Group G']
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G' V₁} {ρ₂ : Representation k G' V₂}
    (e : ρ₁.Equiv ρ₂) (H : Subgroup G')
    (U : Subrepresentation (ρ₁.comp H.subtype))
    (hU : ρ₁.IsInducedFromSubrepresentation H U) :
    ρ₂.IsInducedFromSubrepresentation H
      (subrepresentationOrderIso_local (comp_subtype_equiv_local e H) U) := by
  classical
  let _ : DecidableEq (G' ⧸ H) := Classical.decEq _
  let U' := subrepresentationOrderIso_local (comp_subtype_equiv_local e H) U
  have hinternal : DirectSum.IsInternal (ρ₁.leftQuotientSubmodule H U) := by
    -- Unpack the Chapter 3 owner predicate before transporting the quotient-indexed family.
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
  -- Repackage the transported independence and spanning statements back into inducedness.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Theorem 17-17.6-1: once the recursive lift on the proper stabilizer overgroup is
known, the remaining standard Chapter `7` step is to induce that lift to `G` and transport it
across the explicit induced-model equivalence back to `ρ`. -/
private theorem exists_residueFieldLift_of_isInducedFromSubrepresentation_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W' : Type (max u v x)) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA : Representation A G W')
      (red : W' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Route correction: this is the standard induced-model transport from Chapter `7`, isolated as
  -- a separate frontier so the Hall-kernel proof can keep its focus on LinearRepresentations_Serre_1977's projective
  -- extension branch rather than on induced-model packaging.
  let ρU :
      Representation k G (ULift.{max (max u v) x, x} V) :=
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
      (ULift.moduleEquiv.symm : V ≃ₗ[k] ULift.{max (max u v) x, x} V) fun g ↦ by
        -- The `ULift` wrapper does not change the pointwise action of `ρ`.
        ext x
        rfl
  let WU : Subrepresentation (ρU.comp H.subtype) :=
    subrepresentationOrderIso_local (comp_subtype_equiv_local eU H) W
  have hIndU : ρU.IsInducedFromSubrepresentation H WU := by
    -- Transport the inducedness witness to the lifted ambient carrier.
    simpa [WU] using
      isInducedFromSubrepresentation_of_equiv_local
        (ρ₁ := ρ) (ρ₂ := ρU) eU H W hInd
  rcases
      residueFieldLift_same_universe_witness
        (A := A) (G' := H) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH with
    ⟨W0U, hW0Uadd, hW0Umod, hW0Ufree, hW0Ufinite, ρA_HU, red_HU, hLiftHU_source⟩
  letI : AddCommGroup W0U := hW0Uadd
  letI : Module A W0U := hW0Umod
  letI : Module.Free A W0U := hW0Ufree
  letI : Module.Finite A W0U := hW0Ufinite
  let eW : W.toRepresentation.Equiv WU.toRepresentation := by
    -- The subgroup lift only changes the ambient carrier by the same `ULift` equivalence.
    simpa [WU] using
      subrepresentation_equiv_of_equiv_image_local
        (comp_subtype_equiv_local eU H) W
  have hLiftHU :
      IsResidueFieldLift WU.toRepresentation ρA_HU
        (((eW.toLinearMap.restrictScalars A).comp red_HU)) := by
    -- Transport the subgroup lift across the induced subrepresentation equivalence.
    exact
      residueFieldLift_of_equiv_target_local
        (A := A) (G := H) (ρA := ρA_HU) (red := red_HU) hLiftHU_source eW
  rcases
      Representation.exists_residueFieldLift_of_isInducedFromSubrepresentation
        (A := A) (G := G) (V := ULift.{max (max u v) x, x} V)
        (ρ := ρU) (H := H) WU ρA_HU
        (((eW.toLinearMap.restrictScalars A).comp red_HU)) hLiftHU hIndU with
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA_U, red_U, hLiftU⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  let red_target : P →ₗ[A] V :=
    (eU.symm.toLinearMap.restrictScalars A).comp red_U
  have hLiftTarget :
      IsResidueFieldLift ρ ρA_U red_target := by
    -- The split Chapter `17.3` theorem already gives the induced-model lift on `ρU`; transport
    -- it back to the original target before adjusting the witness universe.
    simpa [red_target, LinearMap.comp_assoc] using
      (residueFieldLift_of_equiv_target_local
        (A := A) (G := G)
        (σ := ρU) (τ := ρ)
        (ρA := ρA_U)
        (red := red_U)
        hLiftU eU.symm)
  let red_lift :=
    red_target.comp (ULift.moduleEquiv : ULift.{max v x, u} P ≃ₗ[A] P).toLinearMap
  have hLiftLift :
      IsResidueFieldLift ρ (uliftRepresentation_witness (A := A) ρA_U) red_lift := by
    -- Now move the lifted source witness into the common witness universe used in this file.
    simpa [red_lift, red_target] using
      residueFieldLift_ulift_witness
        (A := A) (ρ := ρ) (ρA := ρA_U) (red := red_target) hLiftTarget
  refine
    ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
      uliftRepresentation_witness (A := A) ρA_U, red_lift, hLiftLift⟩

/-- Helper for Theorem 17-17.6-1: once the Clifford split lands in the proper-overgroup branch,
the remaining work is to recurse on that subgroup and transport the lift back across induction. -/
private theorem exists_residueFieldLift_of_proper_overgroup_induced_hall
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        I ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases
      exists_residueFieldLift_of_proper_overgroup_subrepresentation
        (A := A) (p := p) (h := h) I hIcop hquot hrecSame ρ hproper with
    ⟨H, hIH, hHlt, W, hInd, P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  -- Route correction: reuse the Chapter `17.3` induced-transport helper directly. In this file,
  -- the proper-overgroup branch should only supply the recursive subgroup lift and the inducedness
  -- witness, not reprove the standard induced-model transport a second time.
  let _ := hp
  rcases
      residueFieldLift_same_universe_witness
        (A := A) (ρ := W.toRepresentation) hLiftH with
    ⟨P', hP'add, hP'mod, hP'free, hP'finite, ρA_H', red_H', hLiftH'⟩
  letI : AddCommGroup P' := hP'add
  letI : Module A P' := hP'mod
  letI : Module.Free A P' := hP'free
  letI : Module.Finite A P' := hP'finite
  rcases
    exists_residueFieldLift_of_isInducedFromSubrepresentation_local
      (A := A) (G := G) (V := V) ρ W ρA_H' red_H' hLiftH' hInd with
    ⟨P'', hP''add, hP''mod, hP''free, hP''finite, ρA, red, hLift⟩
  letI : AddCommGroup P'' := hP''add
  letI : Module A P'' := hP''mod
  letI : Module.Free A P'' := hP''free
  letI : Module.Finite A P'' := hP''finite
  exact ⟨P'', hP''add, hP''mod, hP''free, hP''finite, ρA, red, hLift⟩

/-- Helper for Theorem 17-17.6-1: in the isotypic Hall-kernel branch, one can already choose
LinearRepresentations_Serre_1977's irreducible constituent `S̄` and show that its owner isotypic component is all of the
restricted module. -/
theorem exists_irreducible_constituent_with_isotypic_component_top_of_isotypic_restriction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIsotypic :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k I) V) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∃ Sbar : Subrepresentation ρI,
      Sbar.toRepresentation.IsIrreducible ∧
        isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤ := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  have hsemisimple : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI : IsSemisimpleModule (MonoidAlgebra k I) V := hsemisimple
  have hV_nontrivial : Nontrivial V := nontrivial_of_isIrreducible_local (ρ := ρ)
  letI : Nontrivial V := hV_nontrivial
  -- Route correction: choose LinearRepresentations_Serre_1977's constituent first as a simple owner `k[I]`-submodule of the
  -- restricted module, and only then repackage it as a bundled irreducible subrepresentation.
  obtain ⟨N, -, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra k I) (M := V) (⊤ : Submodule (MonoidAlgebra k I) V)).resolve_left
        top_ne_bot
  let Sbar : Subrepresentation ρI := Subrepresentation.ofSubmodule' N
  have hSbar_irred : Sbar.toRepresentation.IsIrreducible := by
    -- Chapter `1` upgrades the chosen simple owner submodule to an irreducible constituent.
    exact
      isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_without_neZero
        ρI N hNsimple
  have hN_top : isotypicComponent (MonoidAlgebra k I) V N = ⊤ := by
    letI : IsSimpleModule (MonoidAlgebra k I) N := hNsimple
    -- The ambient restricted module is already isotypic, so the component of this constituent is
    -- the whole module.
    exact (isotypicComponent_eq_top_iff (R := MonoidAlgebra k I) (M := V) (S := N)).2
      (hIsotypic N)
  refine ⟨Sbar, hSbar_irred, ?_⟩
  simpa [Sbar] using hN_top

/-- Helper for Theorem 17-17.6-1: the chosen irreducible constituent `S̄` should be simple as an
owner `k[I]`-submodule of the restricted module. This is the precise intrinsic-to-owner transport
needed before invoking the owner-module isotypic decomposition API. -/
private theorem chosen_constituent_owner_simple
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra k I) Sbar.asSubmodule := by
  let ρS : Representation k I Sbar.toSubmodule := Sbar.toRepresentation
  letI : Module (MonoidAlgebra k I) ρS.asModule := ρS.instModuleMonoidAlgebraAsModule
  -- Move LinearRepresentations_Serre_1977's chosen constituent from the intrinsic carrier `S̄.toSubmodule` to the owner
  -- submodule `S̄.asSubmodule` using the canonical owner/intrinsic linear equivalence.
  exact
    @IsSimpleModule.congr (MonoidAlgebra k I) inferInstance Sbar.asSubmodule
      Sbar.asSubmodule.addCommGroup Sbar.asSubmodule.module
      ρS.asModule ρS.instAddCommGroupAsModule ρS.instModuleMonoidAlgebraAsModule
      (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρ.comp I.subtype) Sbar).symm
      ((Representation.irreducible_iff_isSimpleModule_asModule ρS).mp hSbar_irred)

/-- Helper for Theorem 17-17.6-1: once the chosen constituent `S̄` fills the whole isotypic
component of the restricted module, the owner `k[I]`-module `V` can already be rigidified onto a
finite coordinate model `Fin n → S̄`. This is LinearRepresentations_Serre_1977's first fixed-object checkpoint before the
projective-extension cover is introduced. -/
private theorem exists_linearEquiv_pi_of_isotypic_component_top
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∃ n : ℕ, Nonempty (V ≃ₗ[MonoidAlgebra k I] Fin n → Sbar.asSubmodule) := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k (MonoidAlgebra k I) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρI.asAlgebraHom (algebraMap k (MonoidAlgebra k I) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρI.asAlgebraHom.commutes a) x
  letI : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI : Module.Finite (MonoidAlgebra k I) V :=
    Module.Finite.of_restrictScalars_finite k (MonoidAlgebra k I) V
  letI : Nontrivial V := nontrivial_of_isIrreducible_local (ρ := ρ)
  letI : IsSimpleModule (MonoidAlgebra k I) Sbar.asSubmodule :=
    chosen_constituent_owner_simple (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred
  have hType : IsIsotypicOfType (MonoidAlgebra k I) V Sbar.asSubmodule := by
    -- The chosen constituent already controls the whole restricted module.
    exact (isotypicComponent_eq_top_iff (R := MonoidAlgebra k I) (M := V) (S := Sbar.asSubmodule)).mp
      hSbar_top
  rcases hType.linearEquiv_fun (R := MonoidAlgebra k I) (M := V) (S := Sbar.asSubmodule) with
    ⟨n, e⟩
  exact ⟨n, e⟩

/-- Helper for Theorem 17-17.6-1: since the Hall kernel `I` has order prime to `p`, the chosen
constituent `S̄` already admits an `A[I]`-lift. This supplies the lifted constituent that LinearRepresentations_Serre_1977
uses before constructing the finite projective cover `G₂`. -/
private theorem exists_residueFieldLift_of_fixed_constituent
    (hp : Nat.Prime p)
    (I : Subgroup G)
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    [Sbar.toRepresentation.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A I P)
      (red : P →ₗ[A] Sbar.toSubmodule),
        IsResidueFieldLift Sbar.toRepresentation ρA red := by
  have hIndvd : ¬ p ∣ Nat.card I := hp.coprime_iff_not_dvd.mp hIcop
  -- This is the prime-to-`p` lifting step for the fixed constituent itself.
  exact
    exists_residueFieldLift_of_non_dvd_card_witness
      (A := A) (p := p) (G' := I) (V' := Sbar.toSubmodule) hIndvd Sbar.toRepresentation

/-- Helper for Theorem 17-17.6-1: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
private theorem isIrreducible_comp_of_mulEquiv
    {K : Type*} [Field K]
    {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G₁ ≃* G₂) (σ : Representation K G₂ W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  let U' : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using U.apply_mem_toSubmodule (e.symm g) hx }
  have hU'_ne_bot : U' ≠ ⊥ := by
    intro hU'
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa [U'] using congrArg Subrepresentation.toSubmodule hU'
  have hU'_top : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [U'] using congrArg Subrepresentation.toSubmodule hU'_top

/-- Helper for Theorem 17-17.6-1: if the Hall-kernel restriction is isotypic of type `S̄`, then
every conjugate transport of `S̄` is equivariantly isomorphic to `S̄` itself. This is LinearRepresentations_Serre_1977's
`U_s ≠ ∅` checkpoint before the finite projective extension is built. -/
private theorem transported_constituent_equiv_of_isotypic_component_top
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤) :
    ∀ s : G,
      Nonempty (Sbar.toRepresentation.Equiv (transportedSubrepresentation ρ Sbar s).toRepresentation) := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  intro s
  let T : Subrepresentation ρI := transportedSubrepresentation ρ Sbar s
  let ρT : Representation k I T.toSubmodule := T.toRepresentation
  letI : Module (MonoidAlgebra k I) ρT.asModule := ρT.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k I) T.toRepresentation.asModule :=
    T.toRepresentation.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI : IsSimpleModule (MonoidAlgebra k I) Sbar.asSubmodule :=
    chosen_constituent_owner_simple (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred
  have hType : IsIsotypicOfType (MonoidAlgebra k I) V Sbar.asSubmodule := by
    -- The hypothesis says the entire restricted module lies in the `S̄`-isotypic block.
    exact
      (isotypicComponent_eq_top_iff
        (R := MonoidAlgebra k I) (M := V) (S := Sbar.asSubmodule)).mp hSbar_top
  have hT_irred : T.toRepresentation.IsIrreducible := by
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    letI :
        Representation.IsIrreducible
          (Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
      exact
        (conjugatedSubrepresentationOrderIso_local (σ := Sbar.toRepresentation) s).isSimpleOrder_iff.mpr
          inferInstance
    -- Transport identifies the conjugated constituent with the literal subrepresentation `sS̄`.
    exact
      isIrreducible_of_equiv_local
        (transportedSubrepresentation_rep_equiv_local ρ Sbar s)
  have hT_simple : IsSimpleModule (MonoidAlgebra k I) T.asSubmodule := by
    -- Convert irreducibility of the transported intrinsic constituent back to the owner module.
    exact
      @IsSimpleModule.congr (MonoidAlgebra k I) inferInstance T.asSubmodule
        T.asSubmodule.addCommGroup T.asSubmodule.module
        ρT.asModule ρT.instAddCommGroupAsModule ρT.instModuleMonoidAlgebraAsModule
        (subrepresentation_owner_intrinsic_linearEquiv_local (ρ := ρI) T).symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρT).mp hT_irred)
  have hOwnerEquiv : Nonempty (T.asSubmodule ≃ₗ[MonoidAlgebra k I] Sbar.asSubmodule) := by
    exact @hType T.asSubmodule hT_simple
  -- Upgrade the owner-module comparison back to a representation equivalence on the bundled
  -- subrepresentations.
  exact
    ⟨(subrepresentation_equiv_of_asSubmoduleLinearEquiv_local T Sbar hOwnerEquiv.some).symm⟩

/-- Helper for Theorem 17-17.6-1: once a quotient already has height `h`, LinearRepresentations_Serre_1977's bookkeeping can
always pad it to height `h + 1` by inserting the trivial normal subgroup. -/
private lemma isPSolvableOfHeight_succ_of_isPSolvableOfHeight
    {G' : Type*} [Group G'] [Finite G']
    (hG' : IsPSolvableOfHeight p h G') :
    IsPSolvableOfHeight p (Nat.succ h) G' := by
  -- Insert the trivial subgroup as a vacuous first step in the height tower.
  have hquotBot : IsPSolvableOfHeight p h (G' ⧸ (⊥ : Subgroup G')) := by
    exact IsPSolvableOfHeight.of_equiv (QuotientGroup.quotientBot (G := G')).symm hG'
  exact
    IsPSolvableOfHeight.succ_iff.mpr
      ⟨⊥, inferInstance, Or.inl (by simpa using Nat.coprime_one_right p), hquotBot⟩

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's transported constituent lift can be compared to the
conjugated fixed lift by Chapter `15` uniqueness, producing an actual `A`-linear automorphism on
the chosen lift carrier `P_S`. -/
private theorem conjugated_fixed_constituent_lift
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    ∀ s : G,
      IsResidueFieldLift
        (Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        red_S := by
  intro s
  let c_s : I →* I := (MulAut.conjNormal s⁻¹).toMonoidHom
  let ρS_conj : Representation k I Sbar.toSubmodule := Sbar.toRepresentation.comp c_s
  let ρA_conj : Representation A I P_S := ρA_I.comp c_s
  -- Restrict LinearRepresentations_Serre_1977's fixed lift along the conjugation hom before transporting the target.
  change IsResidueFieldLift ρS_conj ρA_conj red_S
  simpa [c_s, ρS_conj, ρA_conj] using
    (Representation.isResidueFieldLift_comp hLiftSbar c_s)

/-- Helper for Theorem 17-17.6-1: the conjugated fixed lift becomes a lift of the literal
transported constituent once we retarget along the canonical transport equivalence. -/
private theorem transported_fixed_constituent_lift_of_conjugation
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    ∀ s : G,
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar s).toRepresentation
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) := by
  intro s
  -- First restrict the fixed lift by conjugation, then transport the target to the literal `sS̄`.
  exact
    residueFieldLift_of_equiv_target_local
      (A := A)
      (hLift :=
        conjugated_fixed_constituent_lift
          (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar s)
      (transportedSubrepresentation_rep_equiv_local ρ Sbar s)

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's transported constituent lift can be compared to the
conjugated fixed lift by Chapter `15` uniqueness, producing an actual `A`-linear automorphism on
the chosen lift carrier `P_S`. -/
private theorem exists_fixed_constituent_transport_aut_of_lift
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ∀ s : G,
      ∃ u : Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I,
        (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
          ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
            red_S := by
  have hI_ndvd : ¬ p ∣ Nat.card I := hp.coprime_iff_not_dvd.mp hIcop
  intro s
  let T_s : Subrepresentation (ρ.comp I.subtype) := transportedSubrepresentation ρ Sbar s
  let ρT : Representation k I T_s.toSubmodule := T_s.toRepresentation
  let ρA_conj : Representation A I P_S := ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom
  let ρA_fixed : Representation A I P_S := ρA_I
  let red_conj : P_S →ₗ[A] T_s.toSubmodule :=
    ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
      red_S
  let red_transport : P_S →ₗ[A] T_s.toSubmodule :=
    (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)
  -- Build the first lift of the literal transported constituent by conjugating the fixed lift.
  have hConjLift_source :
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar s).toRepresentation
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom)
        (((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) :=
    transported_fixed_constituent_lift_of_conjugation
      (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar s
  have hConjLift :
      IsResidueFieldLift
        ρT
        ρA_conj
        red_conj := by
    simpa [T_s, ρT, ρA_conj, red_conj] using hConjLift_source
  have hLiteralTransport :
      IsResidueFieldLift ρT ρA_fixed red_transport := by
    simpa [T_s, ρT, ρA_fixed, red_transport] using hTransportLift s
  have hSmallI : Small.{u} I := by
    obtain ⟨n, ⟨efin⟩⟩ := Finite.exists_equiv_fin I
    exact Small.mk' (efin.trans Equiv.ulift.symm)
  letI : Small.{u} I := hSmallI
  let eShrink : Shrink.{u} I ≃* I := Shrink.mulEquiv
  have hShrink_ndvd : ¬ p ∣ Nat.card (Shrink.{u} I) := by
    simpa [Nat.card_congr eShrink.toEquiv] using hI_ndvd
  have hConjLift_shrink :
      IsResidueFieldLift
        (ρT.comp eShrink.toMonoidHom)
        (ρA_conj.comp eShrink.toMonoidHom)
        red_conj := by
    exact Representation.isResidueFieldLift_comp hConjLift eShrink.toMonoidHom
  have hLiteralTransport_shrink :
      IsResidueFieldLift
        (ρT.comp eShrink.toMonoidHom)
        (ρA_fixed.comp eShrink.toMonoidHom)
        red_transport := by
    exact Representation.isResidueFieldLift_comp hLiteralTransport eShrink.toMonoidHom
  -- Chapter `15` uniqueness now compares this explicit lift with the literal transported lift.
  obtain ⟨uShrink, hu⟩ :=
    residueFieldLift_unique_up_to_equivariant_iso
      (A := A) (p := p) (G := Shrink.{u} I) (V := T_s.toSubmodule)
      hShrink_ndvd
      (ρT.comp eShrink.toMonoidHom)
      (ρA_conj.comp eShrink.toMonoidHom)
      red_conj
      hConjLift_shrink
      (ρA_fixed.comp eShrink.toMonoidHom)
      red_transport
      hLiteralTransport_shrink
  let u : Representation.Equiv ρA_conj ρA_fixed :=
    Representation.Equiv.mk uShrink.toLinearEquiv fun g ↦ by
      -- The shrink comparison is equivariant for every `g' : Shrink I`, hence also for the
      -- original subgroup element `g` after rewriting along `eShrink`.
      simpa [ρA_conj, ρA_fixed] using uShrink.isIntertwining' (eShrink.symm g)
  -- Re-express the uniqueness conclusion in the original theorem statement.
  refine ⟨u, ?_⟩
  change red_transport.comp uShrink.toLinearMap = red_conj
  exact hu

/-- Helper for Theorem 17-17.6-1: choose the source-faithful lifted conjugation automorphism on
the fixed carrier `P_S`; later stages use this concrete carrier automorphism to define LinearRepresentations_Serre_1977's
finite projective cover. -/
private noncomputable def fixed_constituent_transport_aut_of_lift
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    Representation.Equiv
      (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I :=
  Classical.choose <|
    exists_fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's transport fiber `U_s` on the fixed lifted constituent
carrier is the type of `A[I]`-equivariant identifications between the conjugated fixed lift and
the fixed lift itself. Naming this owner restores the source proof's literal `U_s` language before
the later scalar-coset and determinant analysis. -/
private abbrev fixed_constituent_transport_fiber
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (s : G) : Type (max u v x) :=
  Representation.Equiv
    (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) ρA_I

/-- Helper for Theorem 17-17.6-1: the fixed transport fiber `U_s` is nonempty. This is exactly
LinearRepresentations_Serre_1977's source step asserting that every conjugate of the fixed constituent lift is identified
with the original lift on the same carrier. -/
private theorem fixed_constituent_transport_fiber_nonempty
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    Nonempty
      (fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) := by
  -- Reuse the chosen transport automorphism as LinearRepresentations_Serre_1977's witness that the fiber `U_s` is inhabited.
  exact
    ⟨fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s⟩

/-- Helper for Theorem 17-17.6-1: the chosen lifted conjugation automorphism reduces to the
comparison between the transported constituent `sS̄` and the fixed constituent `S̄`. -/
private theorem fixed_constituent_transport_aut_of_lift_reduction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).toLinearMap =
      ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
        red_S := by
  -- Unpack the chosen uniqueness witness once; this is the reduction identity used in the
  -- later determinant-normalized cover construction.
  exact
    Classical.choose_spec <|
      exists_fixed_constituent_transport_aut_of_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: the chosen transport family on the fixed lift already satisfies
LinearRepresentations_Serre_1977's projective cocycle relation up to a literal self-equivalence of `ρA_I`. This isolates the
remaining finite-cover frontier to classifying these self-equivalences and controlling their
determinants. -/
private noncomputable def fixed_constituent_transport_aut_discrepancy
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s t : G) :
    Representation.Equiv ρA_I ρA_I := by
  let u_s :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  let u_t :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t
  let u_st :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t)
  let u_t_over_s :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
    -- The same carrier automorphism `u_t` still intertwines after conjugating both source actions
    -- by `s`; this is the literal projective-cocycle step before LinearRepresentations_Serre_1977's scalar reduction.
    refine Representation.Equiv.mk u_t.toLinearEquiv ?_
    intro a
    ext x
    -- Normalize the double conjugation first: `t⁻¹ (s⁻¹ a s) t = (s * t)⁻¹ a (s * t)`.
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (u_t.isIntertwining' ((MulAut.conjNormal s⁻¹) a)) x
  let composed :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom) ρA_I :=
    u_t_over_s.trans u_s
  -- Compare the two literal lifts of the `(s * t)`-transport: the composed one and the chosen one.
  exact composed.symm.trans u_st

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal source object `G₁` is the total space of the
transport fibers `U_s`, i.e. pairs `(s, u)` with `u : U_s`. Naming the carrier now keeps the
remaining finite-cover work focused on the group law and determinant normalization. -/
private abbrev fixed_constituent_transport_total_space
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) : Type (max u v x) :=
  Σ s : G, fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s

/-- Helper for Theorem 17-17.6-1: the literal source projection `G₁ → G` forgets the transport
operator and remembers only the group element `s`. -/
private abbrev fixed_constituent_transport_total_space_proj
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I → G :=
  Sigma.fst

/-- Helper for Theorem 17-17.6-1: the chosen lifted transport automorphisms give a set-theoretic
section of LinearRepresentations_Serre_1977's projection `G₁ → G`. This is the exact source-faithful choice of one element
in each nonempty fiber `U_s`. -/
private noncomputable def fixed_constituent_transport_total_space_section
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G → fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
  fun s ↦
    ⟨s,
      fixed_constituent_transport_aut_of_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s⟩

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's projection `G₁ → G` is surjective because each fiber
`U_s` is inhabited by the chosen lifted transport automorphism. -/
private theorem fixed_constituent_transport_total_space_proj_surjective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Surjective
      (fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  intro s
  -- Use the chosen point of the fiber `U_s` as the preimage of `s`.
  refine
    ⟨fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s, rfl⟩

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's transport fibers compose directly on the literal lifted
constituent carrier. This is the source-faithful multiplication rule on the intermediate total
space `G₁ = Σ s, U_s` before any determinant normalization. -/
private noncomputable def fixed_constituent_transport_fiber_comp
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I t) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (s * t) := by
  let v_over_s :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
    -- Reuse the same linear transport operator `v`, but now view it after conjugating the source
    -- action by `s`; this is LinearRepresentations_Serre_1977's literal composition law on the transport fibers `U_s`.
    refine Representation.Equiv.mk v.toLinearEquiv ?_
    intro a
    ext x
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (v.isIntertwining' ((MulAut.conjNormal s⁻¹) a)) x
  -- Compose the `t`-transport over `s` with the `s`-transport to land in the `(s * t)`-fiber.
  exact v_over_s.trans u

/-- Helper for Theorem 17-17.6-1: the identity transport belongs to the fiber `U_1`. This gives
the neutral element on LinearRepresentations_Serre_1977's literal total space `G₁`. -/
private noncomputable def fixed_constituent_transport_fiber_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) := by
  refine Representation.Equiv.mk (LinearEquiv.refl A P_S) ?_
  intro a
  ext x
  simp

/-- Helper for Theorem 17-17.6-1: an element of the kernel fiber `U₁` is literally an
`A[I]`-equivariant endomorphism of the fixed lift `ρA_I`. This is the source-faithful bridge from
LinearRepresentations_Serre_1977's kernel notation to the owner endomorphism space used by the Chapter `14` reduction API. -/
private theorem fixed_constituent_transport_kernel_isIntertwiningMap
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ρA_I.IsIntertwiningMap ρA_I u.toLinearMap := by
  -- At `s = 1`, the conjugated source action is definitionally the original `I`-action.
  refine Representation.IsIntertwiningMap.mk ?_
  intro a x
  simpa [fixed_constituent_transport_fiber, MulAut.conjNormal_apply, mul_assoc] using
    LinearMap.congr_fun (u.isIntertwining' a) x

/-- Helper for Theorem 17-17.6-1: repackage a kernel element `u ∈ U₁` as an actual element of the
equivariant endomorphism module `End_{A[I]}(P_S)`. -/
private noncomputable def fixed_constituent_transport_kernel_intertwiningEnd
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ρA_I.IntertwiningMap ρA_I :=
  u.toLinearMap.intertwiningMap_of_isIntertwiningMap
    ρA_I ρA_I
    (fixed_constituent_transport_kernel_isIntertwiningMap
      (A := A) (G := G) (I := I) ρA_I u).isIntertwining

/-- Helper for Theorem 17-17.6-1: Schur's lemma on the reduced fixed constituent says that every
`k[I]`-equivariant endomorphism of `S̄` is scalar. This is LinearRepresentations_Serre_1977's reduced-side input before the
scalar line is lifted back across the fixed projective cover. -/
private theorem fixed_constituent_reduced_scalar_id_surjective
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (u : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :
    ∃ c : k, u = c • Representation.IntertwiningMap.id Sbar.toRepresentation := by
  have hfinrank :
      Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) = 1 := by
    -- LinearRepresentations_Serre_1977's reduced-side Schur lemma is exactly the one-dimensionality of
    -- `End_{k[I]}(S̄)`.
    simpa using
      Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := Sbar.toRepresentation)
  have hpos :
      0 < Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) := by
    omega
  letI :
      Nontrivial (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    FiniteDimensional.nontrivial_of_finrank_pos hpos
  have hId_ne :
      (Representation.IntertwiningMap.id Sbar.toRepresentation :
        Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0 := by
    -- Positive dimension makes the identity endomorphism a genuine nonzero vector.
    simpa using
      (one_ne_zero :
        (1 : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero'
      (Representation.IntertwiningMap.id Sbar.toRepresentation) hId_ne).mp hfinrank u
  exact ⟨c, hc.symm⟩

/-- Helper for Theorem 17-17.6-1: every `A[I]`-equivariant endomorphism of the fixed lift is a
scalar multiple of the identity. This is LinearRepresentations_Serre_1977's literal bridge from the kernel fiber `U₁` to the
scalar group `Aˣ`. -/
private theorem fixed_constituent_endAlgHom_scalar_id_transport
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (a : A) :
    hLiftSbar.endAlgHom (a • Representation.IntertwiningMap.id ρA_I) =
      (IsLocalRing.residue A a) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
  -- The reduction algebra hom carries LinearRepresentations_Serre_1977's scalar line `A · id` to the reduced scalar line
  -- `k · id` by compatibility with scalar multiplication and the identity.
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using
    hLiftSbar.endAlgHom.map_smul a (Representation.IntertwiningMap.id ρA_I)

/-- Helper for Theorem 17-17.6-1: the scalar line `A · id` in `End_{A[I]}(P_S)` already maps onto
the whole reduced endomorphism algebra `End_{k[I]}(S̄)`. This is the exact closed-fiber statement
LinearRepresentations_Serre_1977 uses before invoking Nakayama on the fixed lift. -/
private theorem fixed_constituent_scalar_line_closed_fiber_top
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
      Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
        Set (ρA_I.IntertwiningMap ρA_I))
    Submodule.map hLiftSbar.endAlgHom.toLinearMap N = ⊤ := by
  let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
    Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
      Set (ρA_I.IntertwiningMap ρA_I))
  rw [eq_top_iff]
  intro ubar hubar
  -- Route correction: the old route stalled on transport wrappers. The source-faithful object is
  -- the scalar line `A · id`, and LinearRepresentations_Serre_1977's reduced Schur lemma already shows its reduction is all
  -- of `End_{k[I]}(S̄)`.
  obtain ⟨c, hc⟩ :=
    fixed_constituent_reduced_scalar_id_surjective
      (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred ubar
  obtain ⟨a, ha⟩ : ∃ a : A, IsLocalRing.residue A a = c :=
    IsLocalRing.residue_surjective c
  refine Submodule.mem_map.mpr ?_
  refine ⟨a • Representation.IntertwiningMap.id ρA_I, ?_, ?_⟩
  · -- We now record that the chosen lift lies on the scalar line `A · id`.
    exact Submodule.mem_span_singleton.2 ⟨a, rfl⟩
  · -- Reducing the lifted scalar identity lands exactly on the prescribed reduced scalar.
    simpa [ha, hc] using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar a

/-- Helper for Theorem 17-17.6-1: every `A[I]`-equivariant endomorphism of the fixed lift is a
scalar multiple of the identity. This is LinearRepresentations_Serre_1977's literal bridge from the kernel fiber `U₁` to the
scalar group `Aˣ`. -/
private theorem fixed_constituent_lift_equivariant_endomorphism_scalar
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u : ρA_I.IntertwiningMap ρA_I) :
    ∃ a : A, u = a • Representation.IntertwiningMap.id ρA_I := by
  letI : Module (MonoidAlgebra A I) P_S := Module.compHom P_S ρA_I.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA_I.asAlgebraHom (algebraMap A (MonoidAlgebra A I) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_I.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    Module.compHom Sbar.toSubmodule Sbar.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change Sbar.toRepresentation.asAlgebraHom (algebraMap k (MonoidAlgebra k I) a) x = a • x
      simpa [Algebra.smul_def] using
        LinearMap.congr_fun (Sbar.toRepresentation.asAlgebraHom.commutes a) x
  letI : Module.Projective (MonoidAlgebra A I) P_S :=
    fixed_constituent_lift_projective_of_order_prime_to_p
      (A := A) (p := p) hp I hIcop
  let hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
    Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
      Set (ρA_I.IntertwiningMap ρA_I))
  have hmapRed : Submodule.map hLiftSbar.endAlgHom.toLinearMap N = ⊤ := by
    -- LinearRepresentations_Serre_1977's reduced Schur lemma says the reduction of the scalar line already fills
    -- `End_{k[I]}(S̄)`.
    simpa [N] using
      fixed_constituent_scalar_line_closed_fiber_top
        (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        ρA_I red_S hLiftSbar
  have hfree : Module.Free A (ρA_I.IntertwiningMap ρA_I) := by
    -- The endomorphism algebra of the fixed projective lift is free over the local base ring.
    simpa using (equivariantEndomorphismAlgebra_free (A := A) (G := I) P_S)
  letI := hfree
  have hbase := LinearMap.IsResidueFieldReduction.endAlgHom_isBaseChange
    (A := A) (G := I) hred
  have hmapTensor : N.map (TensorProduct.mk A k (ρA_I.IntertwiningMap ρA_I) 1) = ⊤ := by
    rw [eq_top_iff]
    intro t ht
    have htImage : hbase.equiv t ∈ N.map hLiftSbar.endAlgHom.toLinearMap := by
      -- Transport the tensor point through the endomorphism base-change equivalence and then use
      -- the already established reduced-side top statement.
      simpa [hmapRed] using
        (show hbase.equiv t ∈
          (⊤ : Submodule A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation)) from
            trivial)
    rcases Submodule.mem_map.mp htImage with ⟨x, hxN, hxred⟩
    refine Submodule.mem_map.mpr ⟨x, hxN, ?_⟩
    -- The base-change equivalence sends the pure tensor `1 ⊗ x` to the reduced endomorphism
    -- `hLiftSbar.endAlgHom x`, so equality in the reduced fiber lifts back to equality upstairs.
    apply hbase.equiv.injective
    calc
      hbase.equiv ((TensorProduct.mk A k (ρA_I.IntertwiningMap ρA_I) 1) x) =
          hLiftSbar.endAlgHom x := by
            simpa using hbase.equiv_tmul (1 : k) x
      _ = hbase.equiv t := hxred
  have hNtop : N = ⊤ := by
    -- Nakayama upgrades the fact that `k ⊗ N` is already all of the reduced endomorphism space.
    exact
      (IsLocalRing.map_tensorProduct_mk_eq_top
        (R := A) (M := ρA_I.IntertwiningMap ρA_I) (N := N)).1 hmapTensor
  have huN : u ∈ N := by
    -- Once the scalar line is all of `End_{A[I]}(P_S)`, the chosen endomorphism `u` lies on it.
    simpa [hNtop] using
      (show u ∈ (⊤ : Submodule A (ρA_I.IntertwiningMap ρA_I)) from trivial)
  rcases Submodule.mem_span_singleton.mp huN with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/-- Helper for Theorem 17-17.6-1: if an automorphism of a finite free `A`-module is a scalar
multiple of the identity map, then that scalar is automatically a unit. This is the exact linear
algebra step needed to turn a scalar classification of `End_{A[I]}(P_S)` into LinearRepresentations_Serre_1977's literal
kernel statement `U₁ = Aˣ`. -/
private theorem linearEquiv_eq_unit_smul_refl_of_linearMap_eq_smul_id
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M]
    (e : M ≃ₗ[A] M) {a : A}
    (h : (e : M →ₗ[A] M) = a • LinearMap.id) :
    ∃ u : Aˣ, e = u • LinearEquiv.refl A M := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    -- On the zero-rank carrier, every linear equivalence is already the identity homothety.
    refine ⟨1, ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · have hfinpos : 0 < Module.finrank A M := by
      -- Outside the degenerate case, the free finite carrier has positive rank.
      exact
        (Module.finrank_pos_iff_of_free (R := A) (M := M)).2
          (not_subsingleton_iff_nontrivial.mp hM)
    have hdetUnit : IsUnit (LinearMap.det ((e : M →ₗ[A] M))) := by
      -- An invertible linear map has unit determinant.
      refine LinearMap.isUnit_det (e : M →ₗ[A] M) ?_
      exact
        ⟨⟨(e : M →ₗ[A] M), (e.symm : M →ₗ[A] M),
          by
            ext x
            simp,
          by
            ext x
            simp⟩, rfl⟩
    have hpowUnit : IsUnit (a ^ Module.finrank A M) := by
      -- The determinant of a scalar endomorphism is the corresponding power of that scalar.
      simpa [h, LinearMap.det_smul, LinearMap.det_id] using hdetUnit
    have haUnit : IsUnit a := by
      exact (isUnit_pow_iff (Nat.ne_of_gt hfinpos)).1 hpowUnit
    refine ⟨haUnit.unit, ?_⟩
    ext x
    have h' : (e : M →ₗ[A] M) = (haUnit.unit : A) • LinearMap.id := by
      simpa [haUnit.unit_spec] using h
    -- Re-express the equality on underlying linear maps as an equality of linear equivalences.
    change
      ((e : M →ₗ[A] M) x) =
        ((((haUnit.unit : Aˣ) • LinearEquiv.refl A M : M ≃ₗ[A] M) : M →ₗ[A] M) x)
    simp [h']

/-- Helper for Theorem 17-17.6-1: once every equivariant endomorphism of the fixed lift `ρA_I`
is scalar, LinearRepresentations_Serre_1977's literal kernel fiber `U₁` is exactly the scalar unit group `Aˣ`. This isolates
the only remaining source-faithful gap before the determinant-normalized cover construction. -/
private theorem fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
  obtain ⟨a, ha⟩ :=
    hscalar
      (fixed_constituent_transport_kernel_intertwiningEnd
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u)
  -- First rewrite the kernel transport as a scalar endomorphism in `End_{A[I]}(P_S)`.
  refine
    linearEquiv_eq_unit_smul_refl_of_linearMap_eq_smul_id
      (A := A) (M := P_S) u.toLinearEquiv (a := a) ?_
  change
    (fixed_constituent_transport_kernel_intertwiningEnd
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u : P_S →ₗ[A] P_S) =
      a • LinearMap.id
  simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
    congrArg (fun f : ρA_I.IntertwiningMap ρA_I => (f : P_S →ₗ[A] P_S)) ha

/-- Helper for Theorem 17-17.6-1: inverting a transport operator moves from `U_s` to `U_{s⁻¹}`.
This is the literal inverse operation on LinearRepresentations_Serre_1977's total space `G₁`. -/
private noncomputable def fixed_constituent_transport_fiber_inv
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I s⁻¹ := by
  refine Representation.Equiv.mk u.symm.toLinearEquiv ?_
  intro a
  ext x
  -- Apply the original intertwining relation at the conjugated element `(s a s⁻¹)` and rewrite
  -- the source action on the nose to obtain the inverse transport law.
  have htransport0 :
      (ρA_I ((MulAut.conjNormal s) a)) (u (u.symm x)) =
        u ((ρA_I a) (u.symm x)) := by
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      (LinearMap.congr_fun (u.isIntertwining' ((MulAut.conjNormal s) a)) (u.symm x)).symm
  have htransport :
      ((MonoidHom.comp ρA_I (MulEquiv.toMonoidHom (MulAut.conjNormal s⁻¹⁻¹))) a) x =
        u.toLinearEquiv ((ρA_I a ∘ₗ u.symm.toLinearEquiv) x) := by
    rw [u.apply_symm_apply] at htransport0
    simpa [LinearMap.comp_apply] using htransport0
  exact u.toLinearEquiv.symm_apply_eq.mpr htransport

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal total space `G₁ = Σ s, U_s` already carries the
transport-composition multiplication before the scalar-kernel analysis that cuts out `G₂`. -/
private noncomputable def fixed_constituent_transport_total_space_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
  fun g h ↦
    ⟨g.1 * h.1,
      fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 h.2⟩

/-- Helper for Theorem 17-17.6-1: the chosen section of LinearRepresentations_Serre_1977's projection `G₁ → G` is a genuine
right inverse on the nose. This stabilizes the source-level surjectivity data before the later
determinant-normalized subgroup `G₂` is introduced. -/
private theorem fixed_constituent_transport_total_space_proj_section
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_total_space_section
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      s := rfl

/-- Helper for Theorem 17-17.6-1: the literal multiplication on LinearRepresentations_Serre_1977's total space `G₁`
projects to the ambient group multiplication in `G`. This isolates the first group-theoretic
compatibility needed before the determinant-normalized cover data can be packaged. -/
private theorem fixed_constituent_transport_total_space_proj_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h) =
      fixed_constituent_transport_total_space_proj
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g *
        fixed_constituent_transport_total_space_proj
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) h := by
  rfl

/-- Helper for Theorem 17-17.6-1: the literal inverse on LinearRepresentations_Serre_1977's total space `G₁` projects to the
inverse in the ambient group `G`. This keeps the group package on `G₁` aligned with the source
projection `G₁ → G`. -/
private theorem fixed_constituent_transport_total_space_proj_inv
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        ⟨g.1⁻¹,
          fixed_constituent_transport_fiber_inv
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2⟩ =
      (fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g)⁻¹ := by
  rfl

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal total space `G₁ = Σ s, U_s` already carries
the obvious group law coming from fiber composition, before the determinant normalization that
cuts out the finite subgroup `G₂`. -/
private noncomputable instance fixed_constituent_transport_total_space_group
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Group (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) where
  mul :=
    fixed_constituent_transport_total_space_mul
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  one :=
    ⟨1,
      fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)⟩
  inv := fun g ↦
    ⟨g.1⁻¹,
      fixed_constituent_transport_fiber_inv
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2⟩
  mul_assoc := by
    -- Both products act on the lifted constituent carrier by the same triple composition.
    rintro ⟨a, ua⟩ ⟨b, ub⟩ ⟨c, uc⟩
    apply Sigma.ext
    · simp [fixed_constituent_transport_total_space_mul, mul_assoc]
    · ext x
      rfl
  one_mul := by
    -- The neutral fiber element is the identity automorphism on the lift carrier.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · simp [fixed_constituent_transport_total_space_mul]
    · ext x
      rfl
  mul_one := by
    -- Right multiplication by the identity fiber also acts trivially on the lift carrier.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · simp [fixed_constituent_transport_total_space_mul]
    · ext x
      rfl
  inv_mul := by
    -- Composing a fiber element with its inverse is the identity transport in `U₁`.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · simp [fixed_constituent_transport_total_space_mul]
    · ext x
      simp
  mul_inv := by
    -- The same pointwise cancellation proves the right inverse law.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · simp [fixed_constituent_transport_total_space_mul]
    · ext x
      simp

/-- Helper for Theorem 17-17.6-1: once `G₁` carries its source-faithful group law, the forgetful
projection to `G` is a genuine group homomorphism. This is the exact owner map used before
cutting out the determinant-normalized subgroup `G₂`. -/
private noncomputable def fixed_constituent_transport_total_space_proj_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →* G where
  toFun :=
    fixed_constituent_transport_total_space_proj
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  map_one' := rfl
  map_mul' g h :=
    fixed_constituent_transport_total_space_proj_mul
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h

/-- Helper for Theorem 17-17.6-1: a Hall-kernel element `x ∈ I` acts on the fixed lift carrier by
`ρA_I x`, and this literal action already lies in the transport fiber over `(x : G)`. This is the
source-faithful embedding of LinearRepresentations_Serre_1977's subgroup `I` into the total-space cover `G₁`. -/
private noncomputable def fixed_constituent_transport_fiber_of_hall_kernel_element
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (x : G) := by
  let ex : P_S ≃ₗ[A] P_S :=
    LinearEquiv.ofBijective (ρA_I x) (ρA_I.apply_bijective x)
  refine Representation.Equiv.mk ex ?_
  intro a
  ext v
  -- Route correction: use LinearRepresentations_Serre_1977's literal `I`-action map `ρA_I x` itself as the transport
  -- operator. The only work is the conjugation rewrite
  -- `x * (x⁻¹ * a * x) = a * x` inside `I`.
  calc
    ex (((ρA_I.comp (MulAut.conjNormal ((x : G))⁻¹).toMonoidHom) a) v) =
        ρA_I (x * ((MulAut.conjNormal ((x : G))⁻¹) a)) v := by
          rfl
    _ = ρA_I (a * x) v := by
          congr 1
          apply Subtype.ext
          simp [MulAut.conjNormal_apply, mul_assoc]
    _ = ρA_I a (ρA_I x v) := by
          simpa using LinearMap.congr_fun (ρA_I.map_mul a x) v

/-- Helper for Theorem 17-17.6-1: the literal Hall-kernel copy `x ↦ (x, ρA_I x)` is a monoid
homomorphism from `I` into LinearRepresentations_Serre_1977's total-space cover `G₁`. This is the generator family used
later to define the source-faithful subgroup `G₂`. -/
private noncomputable def fixed_constituent_transport_total_space_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    I →*
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I where
  toFun x :=
    ⟨x,
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x⟩
  map_one' := by
    apply Sigma.ext
    · rfl
    · ext v
      -- At the identity, the embedded Hall-kernel point is the neutral fiber element of `G₁`.
      simp [fixed_constituent_transport_fiber_of_hall_kernel_element,
        fixed_constituent_transport_fiber_one]
  map_mul' x y := by
    apply Sigma.ext
    · rfl
    · ext v
      -- Multiplication in the embedded copy of `I` is the same as the total-space fiber
      -- composition because `ρA_I (x * y) = ρA_I x ∘ ρA_I y`.
      simp [fixed_constituent_transport_total_space_mul,
        fixed_constituent_transport_fiber_of_hall_kernel_element]
      simpa using LinearMap.congr_fun (ρA_I.map_mul x y) v

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's determinant subgroup `C` is generated by the
determinants of the lifted `I`-action on the fixed constituent lift. This isolates the later
determinant-normalization step defining the finite subgroup `G₂ ≤ G₁`. -/
private noncomputable def fixed_constituent_action_det
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
  (ρA_I : Representation A I P_S)
  (x : I) : Aˣ :=
  (LinearMap.isUnit_det (ρA_I x) <| by
      refine ⟨⟨ρA_I x, ρA_I x⁻¹, ?_, ?_⟩, rfl⟩
      · ext y
        simp
      · ext y
        simp).unit

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's determinant subgroup `C` is generated by the
determinants of the lifted `I`-action on the fixed constituent lift. This isolates the later
determinant-normalization step defining the finite subgroup `G₂ ≤ G₁`. -/
private noncomputable def fixed_constituent_determinant_subgroup
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) : Subgroup Aˣ :=
  Subgroup.closure
    (Set.range fun x : I ↦ fixed_constituent_action_det (A := A) (G := G) I ρA_I x)

/-- Helper for Theorem 17-17.6-1: the determinant of a transport-fiber element is the scalar data
that LinearRepresentations_Serre_1977 uses to cut the finite subgroup `G₂` out of `G₁`. -/
private noncomputable def fixed_constituent_transport_fiber_det
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) : Aˣ :=
  LinearEquiv.det u.toLinearEquiv

/-- Helper for Theorem 17-17.6-1: inverting a transport operator in `U_s` inverts its
determinant. This records the determinant behavior of LinearRepresentations_Serre_1977's literal inverse operation before
the scalar-kernel analysis of `U₁`. -/
private theorem fixed_constituent_transport_fiber_det_inv
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
      (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u)⁻¹ := by
  -- The inverse fiber operator is the literal inverse linear equivalence on the fixed lift
  -- carrier, so its determinant is the inverse determinant.
  change LinearEquiv.det (u.toLinearEquiv.symm) = (LinearEquiv.det u.toLinearEquiv)⁻¹
  simpa using (LinearEquiv.det_symm u.toLinearEquiv)

/-- Helper for Theorem 17-17.6-1: composing transport operators multiplies their determinants.
This is the determinant bookkeeping for LinearRepresentations_Serre_1977's literal multiplication on the total space
`G₁ = Σ s, U_s`. -/
private theorem fixed_constituent_transport_fiber_det_comp
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I t) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v) =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u := by
  -- The transported copy of `v` over `s` has the same underlying linear equivalence as `v`
  -- itself, so the determinant follows the usual multiplicative rule for composition.
  change LinearEquiv.det (v.toLinearEquiv.trans u.toLinearEquiv) =
      LinearEquiv.det v.toLinearEquiv * LinearEquiv.det u.toLinearEquiv
  rw [LinearEquiv.det_trans]
  ac_rfl

/-- Helper for Theorem 17-17.6-1: comparing two points in the same transport fiber `U_s`
produces a point in the kernel fiber `U₁`. This is LinearRepresentations_Serre_1977's literal reduction of same-fiber
comparison to the kernel before classifying `U₁ = Aˣ`. -/
private noncomputable def fixed_constituent_transport_fiber_reindex
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (h : s = t) :
    fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s →
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I t :=
  by
    cases h
    intro u
    exact u

/-- Helper for Theorem 17-17.6-1: reindexing a transport fiber along an equality of indices
does not change the underlying determinant. This gives a transport-stable bridge from the raw
fiber `U_{s s⁻¹}` to the kernel fiber `U₁`. -/
@[simp] private theorem fixed_constituent_transport_fiber_det_reindex
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (h : s = t)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_reindex
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) h u) =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u := by
  cases h
  rfl

/-- Helper for Theorem 17-17.6-1: comparing two points in the same transport fiber `U_s`
produces a point in the kernel fiber `U₁`. This is LinearRepresentations_Serre_1977's literal reduction of same-fiber
comparison to the kernel before classifying `U₁ = Aˣ`. -/
private noncomputable def fixed_constituent_transport_fiber_ratio
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) := by
  -- Compare two elements of the same fiber by multiplying one with the inverse of the other.
  exact
    fixed_constituent_transport_fiber_reindex
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (by simp)
      (fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v))

/-- Helper for Theorem 17-17.6-1: the kernel ratio `u / v` composed with `v` recovers `u` on the
lift carrier. This is the transport-stable comparison identity needed when an arbitrary fiber
element is reduced through the chosen section point in the same fiber. -/
private theorem fixed_constituent_transport_fiber_ratio_comp_right
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    (fixed_constituent_transport_fiber_ratio
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v).toLinearMap.comp
        v.toLinearMap =
      u.toLinearMap := by
  -- Unfold the ratio once: it is literally the product `u * v⁻¹` in the transport total space,
  -- so composing it with `v` cancels the inverse and returns `u`.
  ext x
  simp [fixed_constituent_transport_fiber_ratio, fixed_constituent_transport_fiber_reindex,
    fixed_constituent_transport_fiber_comp, fixed_constituent_transport_fiber_inv,
    LinearMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: determinants of two elements in the same fiber differ by the
determinant of their kernel ratio in `U₁`. This isolates the exact source-faithful bridge from
fiberwise determinant cosets to the still-missing kernel classification. -/
private theorem fixed_constituent_transport_fiber_det_eq_ratio_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v) := by
  have hraw :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) v)) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) v) *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u := by
    -- The raw ratio is the literal product `u * v⁻¹` in the transport total space.
    exact
      fixed_constituent_transport_fiber_det_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v)
  have hratio :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v) =
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) v)) := by
    -- Reindexing from `U_{s s⁻¹}` to `U₁` leaves the determinant unchanged.
    unfold fixed_constituent_transport_fiber_ratio
    exact
      fixed_constituent_transport_fiber_det_reindex
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (s := s * s⁻¹) (t := 1) (by simp)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
          (fixed_constituent_transport_fiber_inv
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) v))
  have hmul :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) v)) =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u := by
    rw [hraw, fixed_constituent_transport_fiber_det_inv]
    simp
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u
            (fixed_constituent_transport_fiber_inv
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) v)) := by
            exact hmul.symm
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) v *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v) := by
              rw [hratio]

/-- Helper for Theorem 17-17.6-1: once an element of the kernel fiber `U₁` is identified with a
unit scalar homothety on the fixed lift carrier, its determinant is the corresponding `d`-th
power. This is LinearRepresentations_Serre_1977's literal determinant computation inside the scalar kernel `Aˣ`. -/
private theorem linearEquiv_det_unit_smul_refl
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M]
    (a : Aˣ) :
    LinearEquiv.det (a • LinearEquiv.refl A M) = a ^ Module.finrank A M := by
  -- Reduce the determinant of the scalar linear equivalence to the determinant of the scalar
  -- identity linear map.
  apply Units.ext
  unfold LinearEquiv.det LinearMap.GeneralLinearGroup.generalLinearEquiv
  change
    LinearMap.det (((a • LinearEquiv.refl A M : M ≃ₗ[A] M) : M →ₗ[A] M)) =
      ((a ^ Module.finrank A M : Aˣ) : A)
  rw [show (((a • LinearEquiv.refl A M : M ≃ₗ[A] M) : M →ₗ[A] M)) =
      (a : A) • (LinearMap.id : M →ₗ[A] M) by rfl]
  rw [LinearMap.det_smul, LinearMap.det_id]
  simpa

/-- Helper for Theorem 17-17.6-1: once an element of the kernel fiber `U₁` is identified with a
unit scalar homothety on the fixed lift carrier, its determinant is the corresponding `d`-th
power. This is LinearRepresentations_Serre_1977's literal determinant computation inside the scalar kernel `Aˣ`. -/
private theorem fixed_constituent_transport_kernel_det_eq_unit_pow
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)}
    {a : Aˣ}
    (hu : u.toLinearEquiv = a • LinearEquiv.refl A P_S) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
      a ^ Module.finrank A P_S := by
  -- Replace the kernel transport by the scalar homothety given by the kernel classification.
  unfold fixed_constituent_transport_fiber_det
  rw [hu]
  -- Delegate the scalar determinant calculation to the generic homothety lemma above.
  exact linearEquiv_det_unit_smul_refl (A := A) (M := P_S) a

/-- Helper for Theorem 17-17.6-1: assuming LinearRepresentations_Serre_1977's kernel statement `U₁ = Aˣ`, every determinant
in a fiber `U_s` differs from the determinant of the chosen section element by a `d`-th power of
a unit. This isolates the determinant-coset step before the later normalization to `G₂`. -/
private theorem fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    ∃ a : Aˣ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) *
          a ^ Module.finrank A P_S := by
  let u0 :=
    (fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2
  -- Compare the arbitrary point in `U_s` with the chosen section point by the kernel ratio.
  obtain ⟨a, ha⟩ :=
    hkernel
      (fixed_constituent_transport_fiber_ratio
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0)
  refine ⟨a, ?_⟩
  have hratio :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u0 *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0) := by
    -- The ratio lemma is the literal source reduction from the fiber `U_s` to the kernel `U₁`.
    exact
      fixed_constituent_transport_fiber_det_eq_ratio_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0
  have hratio_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0) =
        a ^ Module.finrank A P_S := by
    -- The kernel classification converts the ratio determinant into a plain `d`-th power.
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha
  simpa [u0, hratio_det] using hratio

/-- Helper for Theorem 17-17.6-1: this structure isolates the finite central-extension stage in
LinearRepresentations_Serre_1977's source proof before the final lower-height recursion on the quotient module `τ`. -/
private structure ConstituentProjectiveExtensionQuotientData
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (P_S : Type (max u v x)) [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule) where
  G2 : Type v
  instGroupG2 : Group G2
  instFiniteG2 : Finite G2
  pi : G2 →* G
  I2 : Subgroup G2
  instNormalI2 : I2.Normal
  Nbar : Subgroup (G2 ⧸ I2)
  instNormalNbar : Nbar.Normal
  hNbar_central : Nbar ≤ Subgroup.center (G2 ⧸ I2)
  hNbar_cyclic : IsCyclic Nbar
  hNbar_coprime : Nat.Coprime p (Nat.card Nbar)
  tau : Representation k (G2 ⧸ I2) (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
  tau_irred : tau.IsIrreducible
  quotientEquiv : ((G2 ⧸ I2) ⧸ Nbar) ≃* (G ⧸ I)
  descendLift :
    ∀ {P_tau : Type (max u v x)} (_ : AddCommGroup P_tau) (_ : Module A P_tau)
      (_ : Module.Free A P_tau) (_ : Module.Finite A P_tau)
      (ρA_tau : Representation A (G2 ⧸ I2) P_tau)
      (red_tau :
        P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar),
        IsResidueFieldLift tau ρA_tau red_tau →
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G P)
            (red : P →ₗ[A] V),
              IsResidueFieldLift ρ ρA red

attribute [instance]
  ConstituentProjectiveExtensionQuotientData.instGroupG2
  ConstituentProjectiveExtensionQuotientData.instFiniteG2
  ConstituentProjectiveExtensionQuotientData.instNormalI2
  ConstituentProjectiveExtensionQuotientData.instNormalNbar

/-- Helper for Theorem 17-17.6-1: if a free `A[N]`-representation reduces to the trivial
`k[N]`-representation and `|N|` is prime to `p`, then the lifted `A[N]`-representation is already
trivial. This isolates the Chapter `15` descent step used after building LinearRepresentations_Serre_1977's finite projective
cover. -/
private theorem isTrivial_of_residueFieldLift_trivial_of_coprime_card
    (hp : Nat.Prime p)
    {N : Type u} [Group N] [Finite N]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A N P}
    {red : P →ₗ[A] W}
    (hLift : IsResidueFieldLift (Representation.trivial k N W) ρA red)
    (hNcop : Nat.Coprime p (Nat.card N)) :
    Representation.IsTrivial ρA := by
  have hNndvd : ¬ p ∣ Nat.card N := hp.coprime_iff_not_dvd.mp hNcop
  have hBaseChange : IsBaseChange k red := hLift.1
  have hTrivialLift :
      IsResidueFieldLift
        (Representation.trivial k N W)
        (Representation.trivial A N P)
        red := by
    let ρAtriv : Representation A N P := Representation.trivial A N P
    letI : Module (MonoidAlgebra A N) P := Module.compHom P ρAtriv.asAlgebraHom.toRingHom
    letI : IsScalarTower A (MonoidAlgebra A N) P :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρAtriv.asAlgebraHom (algebraMap A (MonoidAlgebra A N) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρAtriv.asAlgebraHom.commutes a) x
    let ρltriv : Representation k N W := Representation.trivial k N W
    letI : Module (MonoidAlgebra k N) W := Module.compHom W ρltriv.asAlgebraHom.toRingHom
    letI : IsScalarTower k (MonoidAlgebra k N) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρltriv.asAlgebraHom (algebraMap k (MonoidAlgebra k N) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρltriv.asAlgebraHom.commutes a) x
    letI : Module (MonoidAlgebra A N) W :=
      Module.compHom W (MonoidAlgebra.mapRingHom N (algebraMap A k))
    letI : IsScalarTower A (MonoidAlgebra A N) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change
          (MonoidAlgebra.mapRingHom N (algebraMap A k))
              (MonoidAlgebra.single (1 : N) a) • x =
            a • x
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : N) (IsLocalRing.residue A a) =
              algebraMap k (MonoidAlgebra k N) (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : N) (IsLocalRing.residue A a) • x
              = (IsLocalRing.residue A a) • x := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul (MonoidAlgebra k N)
                      (IsLocalRing.residue A a) x)
          _ = a • x := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k a x)
    change red.IsResidueFieldReduction N
    constructor
    · -- The base-change witness is unchanged when both source and target actions are trivial.
      exact hBaseChange
    · -- Equivariance becomes the tautological fixed-point relation for the trivial action.
      refine Representation.IsIntertwiningMap.mk ?_
      intro g x
      have hsrc : MonoidAlgebra.single g (1 : A) • x = x := by
        change (ρAtriv.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x = x
        rw [Representation.asAlgebraHom_single]
        simpa using Representation.isTrivial_apply ρAtriv g x
      have htgt : MonoidAlgebra.single g (1 : A) • red x = red x := by
        change
          (MonoidAlgebra.mapRingHom N (algebraMap A k) (MonoidAlgebra.single g (1 : A))) •
            red x =
            red x
        rw [MonoidAlgebra.mapRingHom_single]
        change (ρltriv.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red x) = red x
        rw [Representation.asAlgebraHom_single]
        simpa using Representation.isTrivial_apply ρltriv g (red x)
      simpa [Representation.ofModule'] using
        calc
          red (MonoidAlgebra.single g (1 : A) • x) = red x := by rw [hsrc]
          _ = MonoidAlgebra.single g (1 : A) • red x := by rw [htgt]
  obtain ⟨e, _⟩ :=
    residueFieldLift_unique_up_to_equivariant_iso
      (A := A) (p := p) (G := N) (V := W)
      hNndvd
      (Representation.trivial k N W)
      (Representation.trivial A N P) red hTrivialLift
      ρA red hLift
  refine Representation.IsTrivial.mk ?_
  intro g
  ext x
  -- Compare `ρA g` with the trivial action by conjugating through the unique lift equivalence.
  have hEq := LinearMap.congr_fun (e.isIntertwining' g) (e.symm x)
  have hEq' : (ρA g) (e (e.symm x)) = e (e.symm x) := by
    simpa [Representation.trivial] using hEq.symm
  simpa using hEq'

/-- Helper for Theorem 17-17.6-1: the determinant of the fixed lifted `I`-action is a genuine
group homomorphism `I → Aˣ`. This is the owner used to identify LinearRepresentations_Serre_1977's determinant subgroup `C`
with a finite image subgroup. -/
private noncomputable def fixed_constituent_action_det_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) : I →* Aˣ where
  toFun := fixed_constituent_action_det (A := A) (G := G) I ρA_I
  map_one' := by
    -- The identity element acts as the identity linear map, whose determinant is `1`.
    apply Units.ext
    change LinearMap.det (ρA_I 1) = 1
    simp
  map_mul' x y := by
    -- Determinant turns LinearRepresentations_Serre_1977's multiplicative `I`-action into multiplication in `Aˣ`.
    apply Units.ext
    change LinearMap.det (ρA_I (x * y)) = LinearMap.det (ρA_I x) * LinearMap.det (ρA_I y)
    rw [map_mul, LinearMap.det_mul]

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's determinant subgroup `C` is exactly the range of the
determinant homomorphism on the fixed lifted `I`-action. This packages the earlier closure
definition into a finite subgroup owner. -/
private theorem fixed_constituent_determinant_subgroup_eq_range
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I =
      (fixed_constituent_action_det_hom (A := A) (G := G) (I := I) ρA_I).range := by
  -- The defining generators of `C` already lie in the image subgroup, and conversely every image
  -- point is one of those generators.
  refine Subgroup.closure_eq_of_le ?_ ?_
  · intro a ha
    rcases ha with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, rfl⟩
    exact Subgroup.subset_closure ⟨x, rfl⟩

/-- Helper for Theorem 17-17.6-1: the determinant subgroup `C` of the fixed lifted Hall-kernel
action has order dividing `|I|`. This is the finite-group part of LinearRepresentations_Serre_1977's determinant
normalization stage. -/
private theorem fixed_constituent_determinant_subgroup_card_dvd
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Nat.card (fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) ∣
      Nat.card I := by
  -- Replace `C` by the determinant-image subgroup and apply the standard cardinal divisibility for
  -- the range of a homomorphism from a finite group.
  rw [fixed_constituent_determinant_subgroup_eq_range
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  exact Subgroup.card_range_dvd (fixed_constituent_action_det_hom
    (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: the determinant subgroup `C` has order prime to `p` because it
is a quotient of the Hall kernel `I`, whose order is already prime to `p`. -/
private theorem fixed_constituent_determinant_subgroup_coprime
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Nat.Coprime p
      (Nat.card (fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I)) := by
  -- Coprimality descends along the determinant-image divisibility just proved above.
  exact hIcop.of_dvd_right
    (fixed_constituent_determinant_subgroup_card_dvd
      (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: the fixed lifted constituent has the same finite rank over `A`
as its reduced constituent has over the residue field `k`. This is the rank comparison extracted
from the residue-field lift witness. -/
private theorem fixed_constituent_lift_finrank_eq
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    Module.finrank A P_S = Module.finrank k Sbar.toSubmodule := by
  letI : FiniteDimensional k Sbar.toSubmodule :=
    IsIrreducible.finiteDimensional_of_finite Sbar.toRepresentation
  let hred : red_S.IsResidueFieldReduction I := hLiftSbar
  -- The base-change equivalence in the reduction owner preserves finite rank exactly.
  simpa using hred.1.finrank_eq

/-- Helper for Theorem 17-17.6-1: the degree of the fixed lifted constituent is prime to `p`
because its reduction is irreducible over `I`, hence has degree dividing `|I|`. -/
private theorem fixed_constituent_lift_finrank_coprime
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    Nat.Coprime p (Module.finrank A P_S) := by
  letI : FiniteDimensional k Sbar.toSubmodule :=
    IsIrreducible.finiteDimensional_of_finite Sbar.toRepresentation
  have hdim_dvd : Module.finrank k Sbar.toSubmodule ∣ Nat.card I := by
    -- LinearRepresentations_Serre_1977's Chapter `6` divisibility theorem applies directly to the reduced irreducible
    -- constituent `S̄`.
    exact Representation.finrank_dvd_card (ρ := Sbar.toRepresentation)
  rw [fixed_constituent_lift_finrank_eq
    (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred ρA_I red_S hLiftSbar]
  exact hIcop.of_dvd_right hdim_dvd

/-- Helper for Theorem 17-17.6-1: a prime-to-`p` torsion unit in the coefficient ring that reduces
to `1` is already `1`. This is the uniqueness input behind the principal-unit correction in the
determinant-normalization step. -/
private theorem unit_eq_one_of_pow_eq_one_of_residue_eq_one
    (hp : Nat.Prime p)
    {u : Aˣ} {n : ℕ} (hn : Nat.Coprime p n)
    (hu : ((u : A) ^ n) = 1)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    u = 1 := by
  let s : A := ∑ i ∈ Finset.range n, (u : A) ^ i
  have hn_not_dvd : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp hn
  have hn_cast_ne : ((n : ℕ) : k) ≠ 0 :=
    (NeZero.of_not_dvd (R := k) hn_not_dvd).out
  have hs_res : IsLocalRing.residue A s = (n : k) := by
    -- Reducing the geometric sum termwise collapses every term to `1`.
    calc
      IsLocalRing.residue A s
          = ∑ i ∈ Finset.range n,
              IsLocalRing.residue A ((u : A) ^ i) := by
                simp [s]
      _ = ∑ i ∈ Finset.range n, (1 : k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_pow]
            simpa [hres]
      _ = (n : k) := by
            simp
  have hs_unit : IsUnit s := by
    have hs_res_ne : IsLocalRing.residue A s ≠ 0 := by
      simpa [hs_res] using hn_cast_ne
    have hs_not_mem : s ∉ IsLocalRing.maximalIdeal A := by
      intro hs_mem
      exact hs_res_ne ((IsLocalRing.residue_eq_zero_iff s).2 hs_mem)
    exact (IsLocalRing.notMem_maximalIdeal).1 hs_not_mem
  have hgeom : s * ((u : A) - 1) = 0 := by
    -- The geometric-series identity closes because the chosen power of `u` is `1`.
    simpa [s, hu] using (geom_sum_mul (u : A) n)
  have hsub : (u : A) - 1 = 0 := by
    exact (IsUnit.mul_right_eq_zero hs_unit).1 hgeom
  apply Units.ext
  exact sub_eq_zero.mp hsub

/-- Helper for Theorem 17-17.6-1: if a unit reduces to `1`, then it has a `d`-th root whenever
`d` is prime to `p`. This isolates the Hensel step needed to remove the principal-unit part of a
determinant class before constructing the finite cover `G₂`. -/
private theorem exists_dth_root_of_unit_of_residue_eq_one
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    ∃ a : Aˣ, a ^ d = u := by
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hp_one : p = 1 := by
      simpa [hd0] using hdcop
    exact hp.ne_one hp_one
  let f : Polynomial A := Polynomial.X ^ d - Polynomial.C (u : A)
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (u : A)) hd_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma packaged in mathlib's local-ring TFAE.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (1 : k) f = 0 := by
    -- The residue point `1` is a simple root of `X^d - u`.
    simpa [Polynomial.aeval_def, f, hres, sub_eq_zero] using (show (1 : k) ^ d = 1 by simp)
  have hderiv_ne : Polynomial.aeval (1 : k) (Polynomial.derivative f) ≠ 0 := by
    have hd_not_dvd : ¬ p ∣ d := hp.coprime_iff_not_dvd.mp hdcop
    have hd_cast_ne : ((d : ℕ) : k) ≠ 0 := (NeZero.of_not_dvd (R := k) hd_not_dvd).out
    -- The derivative of `X^d - u` at `1` is exactly `d`.
    rw [show Polynomial.aeval (1 : k) (Polynomial.derivative f) = ((d : ℕ) : k) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ d) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact hd_cast_ne
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (1 : k) hroot0 hderiv_ne
  have ha_pow : a ^ d = (u : A) := by
    -- Unfold the Hensel root back to the concrete power equation.
    have hroot_eq : a ^ d - (u : A) = 0 := by
      simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
    exact sub_eq_zero.mp hroot_eq
  have ha_unit : IsUnit a := by
    have hpow_unit : IsUnit (a ^ d) := ha_pow ▸ u.isUnit
    exact (isUnit_pow_iff hd_ne).1 hpow_unit
  refine ⟨ha_unit.unit, ?_⟩
  -- Repackage the scalar root as an equality in the unit group.
  apply Units.ext
  simpa [ha_unit.unit_spec] using ha_pow

/-- Helper for Theorem 17-17.6-1: the Hensel lift in the principal-unit case may be chosen with
residue equal to `1`. This is the version needed when a later scalar correction must preserve a
fixed residue-field root of unity. -/
private theorem exists_dth_root_of_unit_of_residue_eq_one_with_residue
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    ∃ a : Aˣ, a ^ d = u ∧ IsLocalRing.residue A (a : A) = 1 := by
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hp_one : p = 1 := by
      simpa [hd0] using hdcop
    exact hp.ne_one hp_one
  let f : Polynomial A := Polynomial.X ^ d - Polynomial.C (u : A)
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (u : A)) hd_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma exactly as in the principal-unit root
    -- lemma, but now keep the residue output because the later roots-of-unity lift uses it.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (1 : k) f = 0 := by
    -- The residue point `1` is again a simple root of `X^d - u`.
    simpa [Polynomial.aeval_def, f, hres, sub_eq_zero] using (show (1 : k) ^ d = 1 by simp)
  have hderiv_ne : Polynomial.aeval (1 : k) (Polynomial.derivative f) ≠ 0 := by
    have hd_not_dvd : ¬ p ∣ d := hp.coprime_iff_not_dvd.mp hdcop
    have hd_cast_ne : ((d : ℕ) : k) ≠ 0 := (NeZero.of_not_dvd (R := k) hd_not_dvd).out
    -- The derivative at the Hensel point is the nonzero scalar `d`.
    rw [show Polynomial.aeval (1 : k) (Polynomial.derivative f) = ((d : ℕ) : k) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ d) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact hd_cast_ne
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (1 : k) hroot0 hderiv_ne
  have ha_pow : a ^ d = (u : A) := by
    -- Unfold the Hensel root back to the concrete power equation.
    have hroot_eq : a ^ d - (u : A) = 0 := by
      simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
    exact sub_eq_zero.mp hroot_eq
  have ha_unit : IsUnit a := by
    have hpow_unit : IsUnit (a ^ d) := ha_pow ▸ u.isUnit
    exact (isUnit_pow_iff hd_ne).1 hpow_unit
  refine ⟨ha_unit.unit, ?_, ?_⟩
  · -- Repackage the scalar root as an equality in the unit group.
    apply Units.ext
    simpa [ha_unit.unit_spec] using ha_pow
  · -- The Hensel witness was chosen over the residue point `1`, so the unit lift keeps residue
    -- `1`.
    simpa [ha_unit.unit_spec] using ha_res

/-- Helper for Theorem 17-17.6-1: a residue-field root of unity of order prime to `p` lifts to an
actual unit root of unity in `A`. This is the algebraic input behind LinearRepresentations_Serre_1977's determinant
normalization after enlarging the coefficient field. -/
private theorem lift_roots_of_unity_unit_of_coprime_char
    (hp : Nat.Prime p)
    {n : ℕ} (hncop : Nat.Coprime p n)
    (ξ : rootsOfUnity n k) :
    ∃ ζ : Aˣ, ζ ^ n = 1 ∧ Units.map (IsLocalRing.residue A) ζ = ξ := by
  obtain ⟨ξLift, hξLift⟩ :=
    surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A))
      (by infer_instance) (ξ : kˣ)
  let u : Aˣ := ξLift ^ n
  have hu_res : IsLocalRing.residue A (u : A) = 1 := by
    -- The chosen lift has the same `n`-th residue power as `ξ`, which is already `1`.
    have hmap_u : Units.map (IsLocalRing.residue A) u = 1 := by
      calc
        Units.map (IsLocalRing.residue A) u =
            (Units.map (IsLocalRing.residue A) ξLift) ^ n := by
              simp [u, MonoidHom.map_pow]
        _ = (ξ : kˣ) ^ n := by rw [hξLift]
        _ = 1 := by
              exact Subtype.property ξ
    simpa using congrArg (fun z : kˣ ↦ (z : k)) hmap_u
  obtain ⟨a, ha_pow, ha_res⟩ :=
    exists_dth_root_of_unit_of_residue_eq_one_with_residue
      (A := A) (p := p) hp hncop hu_res
  refine ⟨ξLift * a⁻¹, ?_, ?_⟩
  · -- Divide the arbitrary lift by the principal-unit correction to get a literal `n`-torsion
    -- unit upstairs.
    calc
      (ξLift * a⁻¹) ^ n = ξLift ^ n * (a⁻¹) ^ n := by
        simp [mul_pow]
      _ = u * (u⁻¹) := by
        rw [ha_pow]
        simp [u]
      _ = 1 := by simp
  · -- The correction has residue `1`, so the final unit still reduces to the original root of
    -- unity `ξ`.
    have hmap_a : Units.map (IsLocalRing.residue A) a = 1 := by
      apply Units.ext
      simpa using ha_res
    calc
      Units.map (IsLocalRing.residue A) (ξLift * a⁻¹) =
          Units.map (IsLocalRing.residue A) ξLift *
            (Units.map (IsLocalRing.residue A) a)⁻¹ := by
              simp
      _ = (ξ : kˣ) * 1⁻¹ := by rw [hξLift, hmap_a]
      _ = ξ := by simp

/-- Helper for Theorem 17-17.6-1: if a unit has residue equal to a `d`-th power in `kˣ`, then it
is already a literal `d`-th power in `Aˣ`. This packages the source-faithful two-step upgrade:
first lift the residue root to `Aˣ`, then remove the remaining principal-unit error by Hensel. -/
private theorem exists_dth_root_of_unit_of_residue_eq_dth_power
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : ∃ b : kˣ, Units.map (IsLocalRing.residue A) u = b ^ d) :
    ∃ a : Aˣ, a ^ d = u := by
  obtain ⟨b, hb⟩ := hres
  obtain ⟨bLift, hbLift⟩ :=
    surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A))
      (by infer_instance) b
  let u₀ : Aˣ := u * bLift⁻¹ ^ d
  have hu₀_res : IsLocalRing.residue A (u₀ : A) = 1 := by
    -- After lifting the residue root `b`, the remaining quotient is a principal unit.
    have hmap :
        Units.map (IsLocalRing.residue A) u₀ =
          Units.map (IsLocalRing.residue A) u *
            (Units.map (IsLocalRing.residue A) bLift⁻¹) ^ d := by
      simp [u₀, map_mul, MonoidHom.map_pow]
    have hbLift_inv :
        Units.map (IsLocalRing.residue A) bLift⁻¹ = b⁻¹ := by
      simpa using congrArg Inv.inv hbLift
    have hunit_eq : Units.map (IsLocalRing.residue A) u₀ = 1 := by
      calc
        Units.map (IsLocalRing.residue A) u₀ =
            Units.map (IsLocalRing.residue A) u *
              (Units.map (IsLocalRing.residue A) bLift⁻¹) ^ d := hmap
        _ = b ^ d * (b⁻¹) ^ d := by rw [hb, hbLift_inv]
        _ = 1 := by simp [mul_comm]
    simpa using congrArg (fun z : kˣ ↦ (z : k)) hunit_eq
  obtain ⟨a₀, ha₀⟩ :=
    exists_dth_root_of_unit_of_residue_eq_one
      (A := A) (p := p) hp hdcop hu₀_res
  refine ⟨a₀ * bLift, ?_⟩
  -- Multiply the Hensel root of the principal-unit quotient by the lifted residue root.
  calc
    (a₀ * bLift) ^ d = a₀ ^ d * bLift ^ d := by simp [mul_pow]
    _ = u₀ * bLift ^ d := by rw [ha₀]
    _ = u * (bLift⁻¹ ^ d * bLift ^ d) := by
          simp [u₀, mul_assoc, mul_left_comm, mul_comm]
    _ = u := by simp

/-- Helper for Theorem 17-17.6-1: the determinants of the chosen section elements in LinearRepresentations_Serre_1977's
literal transport cover `G₁ → G` are multiplicative up to a `d`-th power, where
`d = finrank_A(P_S)`. This packages the cocycle discrepancy into the scalar kernel `Aˣ`. -/
private theorem fixed_constituent_section_det_mul_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s t : G) :
    ∃ a : Aˣ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t)).2) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t).2) *
          a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let ucomp :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (s * t) :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 (sec t).2
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (s * t) ucomp
  have hcomp :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ucomp =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2 := by
    -- The section product in `G₁` is just composition of transport operators, so determinants
    -- multiply in the usual way.
    simpa [ucomp, mul_comm, mul_left_comm, mul_assoc] using
      fixed_constituent_transport_fiber_det_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 (sec t).2
  refine ⟨a⁻¹, ?_⟩
  -- Cancel the scalar discrepancy on the right to rewrite the chosen section determinant.
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s * t)).2 =
      (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s * t)).2 *
        a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
          rw [← mul_assoc]
          simp
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ucomp *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [ha]
    _ =
      (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2) *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [hcomp]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2 *
        (a⁻¹) ^ Module.finrank A P_S := by
          ac_rfl

/-- Helper for Theorem 17-17.6-1: the determinant of the chosen section at `s ^ n` differs from
the `n`-th power of the determinant at `s` by a `d`-th power. This is the source-faithful
torsion statement modulo scalar determinants coming from the kernel `U₁ = Aˣ`. -/
private theorem fixed_constituent_section_det_pow_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∀ n : ℕ,
      ∃ a : Aˣ,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s ^ n)).2) =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              ((fixed_constituent_transport_total_space_section
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) ^ n *
            a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro n
  induction n with
  | zero =>
      obtain ⟨a, ha⟩ :=
        fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
          (1 : G) (fixed_constituent_transport_fiber_one
            (A := A) (G := G) (I := I) (ρA_I := ρA_I))
      refine ⟨a⁻¹, ?_⟩
      -- At `n = 0`, compare the chosen section at `1` with the literal identity in `U₁`.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ 0)).2 =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 := by
                simp [sec]
        _ =
          (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 *
            a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
              rw [← mul_assoc]
              simp
        _ =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_transport_fiber_one
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)) *
            (a⁻¹) ^ Module.finrank A P_S := by
              rw [ha]
        _ = (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ 0 *
            (a⁻¹) ^ Module.finrank A P_S := by
              simp [fixed_constituent_transport_fiber_det]
  | succ n ihn =>
      obtain ⟨a, ha⟩ := ihn
      obtain ⟨b, hb⟩ :=
        fixed_constituent_section_det_mul_eq_unit_pow
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
          (s ^ n) s
      refine ⟨a * b, ?_⟩
      -- The cocycle statement for `(s ^ n, s)` closes the induction after combining the two
      -- scalar discrepancies.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ n.succ)).2 =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ n)).2 *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            b ^ Module.finrank A P_S := by
              simpa [pow_succ, sec] using hb
        _ =
          ((fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n *
            a ^ Module.finrank A P_S) *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            b ^ Module.finrank A P_S := by
              rw [ha]
        _ =
          (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n.succ *
            (a * b) ^ Module.finrank A P_S := by
              rw [pow_succ, mul_pow]
              ac_rfl

/-- Helper for Theorem 17-17.6-1: every chosen section determinant has exponent dividing
`Nat.card G` modulo `d`-th powers. This is the uniform finite-torsion owner needed before the
remaining residue-subgroup construction. -/
private theorem fixed_constituent_section_det_pow_card_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∃ a : Aˣ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) ^
        Nat.card G =
      a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  obtain ⟨a, ha⟩ :=
    fixed_constituent_section_det_pow_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      s (Nat.card G)
  obtain ⟨b, hb⟩ :=
    fixed_constituent_section_det_pow_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      s 0
  have hcard :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 =
        (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G *
          a ^ Module.finrank A P_S := by
    -- Rewrite `s ^ |G|` to `1` in the general power-comparison lemma.
    simpa [sec, pow_card_eq_one'] using ha
  have hone :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 =
        b ^ Module.finrank A P_S := by
    -- The `n = 0` case shows that the determinant at `1` is itself already a `d`-th power.
    simpa [sec] using hb
  refine ⟨b * a⁻¹, ?_⟩
  -- Subtract the `d`-th power discrepancy contributed by the chosen section at `1`.
  calc
    (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G =
      ((fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G *
        a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
          rw [← mul_assoc]
          simp
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [← hcard]
    _ = b ^ Module.finrank A P_S * (a⁻¹) ^ Module.finrank A P_S := by
          rw [hone]
    _ = (b * a⁻¹) ^ Module.finrank A P_S := by
          rw [mul_pow]

/-- Helper for Theorem 17-17.6-1: after reducing a chosen section determinant to the residue
field and quotienting by `d`-th powers, the resulting class is killed by `Nat.card G`. This is
the quotient-level torsion statement available from the already proved determinant-power identity.
-/
private theorem section_determinant_class_pow_card_eq_one_mod_dth_powers
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (QuotientGroup.mk' Qd
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2))) ^
      Nat.card G = 1 := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  obtain ⟨a, ha⟩ :=
    fixed_constituent_section_det_pow_card_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  -- Rewrite the quotient power using the already proved `d`-th-power identity upstairs in `Aˣ`.
  rw [← MonoidHom.map_pow]
  have hres :
      Units.map (IsLocalRing.residue A)
        ((fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G) =
        (Units.map (IsLocalRing.residue A) a) ^ d := by
    simpa [d] using congrArg (Units.map (IsLocalRing.residue A)) ha
  rw [hres]
  -- The right-hand side is trivial in the quotient because it lies in the `d`-th-power subgroup.
  change QuotientGroup.mk' Qd ((powMonoidHom d : kˣ →* kˣ) (Units.map (IsLocalRing.residue A) a)) =
    1
  exact
    (QuotientGroup.eq_one_iff
      ((powMonoidHom d : kˣ →* kˣ) (Units.map (IsLocalRing.residue A) a))).2
      ⟨Units.map (IsLocalRing.residue A) a, rfl⟩

/-- Helper for Theorem 17-17.6-1: reduce the determinant of the chosen section element in LinearRepresentations_Serre_1977's
transport cover to its class modulo `d`-th powers in the residue-field units. This gives the
literal section-side generator family for the candidate subgroup that will later define `G₂`. -/
private noncomputable def fixed_constituent_section_determinant_class
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G → (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  fun s ↦
    QuotientGroup.mk'
      ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2)))

/-- Helper for Theorem 17-17.6-1: reduce an element of LinearRepresentations_Serre_1977's determinant subgroup `C` to the
same residue-field quotient modulo `d`-th powers. This is the second generator family for the
explicit candidate subgroup containing the determinant-normalization data. -/
private noncomputable def fixed_constituent_determinant_subgroup_residue_class
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I →
      (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  fun c ↦
    QuotientGroup.mk'
      ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
      (Units.map (IsLocalRing.residue A) c)

/-- Helper for Theorem 17-17.6-1: the first explicit approximation to LinearRepresentations_Serre_1977's finite subgroup is
the subgroup of the residue-field quotient generated by the chosen section determinant classes and
the image of the determinant subgroup `C`. The remaining blocker is to prove this candidate is
cyclic of order prime to `p`. -/
private noncomputable def fixed_constituent_projective_extension_candidate_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Subgroup (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  Subgroup.closure
    (Set.range
        (fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I))

/-- Helper for Theorem 17-17.6-1: each chosen section determinant class already lies in the
explicit candidate subgroup that precedes the final cyclicity/prime-to-`p` normalization. -/
private theorem fixed_constituent_section_determinant_class_mem_candidate
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The section classes are built in as generators of the candidate subgroup.
  exact Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)

/-- Helper for Theorem 17-17.6-1: the residue-field image of every element of LinearRepresentations_Serre_1977's determinant
subgroup `C` already lies in the same explicit candidate subgroup. This isolates the remaining
work to proving that the generated subgroup has the expected finite cyclic prime-to-`p` shape. -/
private theorem fixed_constituent_determinant_subgroup_residue_class_mem_candidate
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The determinant subgroup image is the second generator family of the candidate subgroup.
  exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

/-- Helper for Theorem 17-17.6-1: each chosen section determinant class is torsion in the
residue-field quotient, because its `|G|`-th power is already trivial modulo `d`-th powers. -/
private theorem fixed_constituent_section_determinant_class_isOfFinOrder
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    IsOfFinOrder
      (fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) := by
  -- Repackage the already proved quotient-power identity as finite order of the section class.
  refine isOfFinOrder_iff_pow_eq_one.mpr ?_
  refine ⟨Nat.card G, Nat.card_pos, ?_⟩
  simpa using
    section_determinant_class_pow_card_eq_one_mod_dth_powers
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I
        (fun f ↦
          fixed_constituent_lift_equivariant_endomorphism_scalar
            (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
            hSbar_irred
            ρA_I red_S hLiftSbar f))
      s

/-- Helper for Theorem 17-17.6-1: every residue-field image of the determinant subgroup `C`
remains torsion after passing to the quotient modulo `d`-th powers. -/
private theorem fixed_constituent_determinant_subgroup_residue_class_isOfFinOrder
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    IsOfFinOrder
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) := by
  -- The quotient class inherits the finite order of its source element in the finite subgroup `C`.
  refine isOfFinOrder_iff_pow_eq_one.mpr ?_
  refine ⟨Nat.card (fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I),
    Nat.card_pos, ?_⟩
  rw [← MonoidHom.map_pow]
  simp [fixed_constituent_determinant_subgroup_residue_class, pow_card_eq_one' (x := c)]

/-- Helper for Theorem 17-17.6-1: every explicit generator coming from LinearRepresentations_Serre_1977's determinant
subgroup `C` is already represented by an actual `(card C)`-th root of unity in the residue
field, not merely by an abstract torsion quotient class. -/
private theorem determinant_subgroup_residue_class_mem_card_rootsOfUnity_image
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  let ζ : kˣ := Units.map (IsLocalRing.residue A) c
  have hpow : ζ ^ Nat.card C = 1 := by
    -- The determinant subgroup is finite, so each of its residue images is killed by `|C|`.
    simpa [C, ζ] using congrArg (Units.map (IsLocalRing.residue A)) (pow_card_eq_one' (x := c))
  letI : NeZero (Nat.card C) := NeZero.of_gt Nat.card_pos
  let ξ : rootsOfUnity (Nat.card C) k := rootsOfUnity.mkOfPowEq (ζ : k) (by simpa using hpow)
  refine ⟨ξ, ?_⟩
  -- Route correction: package the source element of `C` itself as the required roots-of-unity
  -- representative before mapping into the quotient modulo `d`-th powers.
  change QuotientGroup.mk' Qd ((ξ : rootsOfUnity (Nat.card C) k : kˣ)) =
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) c)
  congr 1
  apply Units.ext
  simpa [ξ, ζ]

/-- Helper for Theorem 17-17.6-1: the same determinant-subgroup generator family already lands in
the common `lcm`-bounded roots-of-unity subgroup that will later host LinearRepresentations_Serre_1977's full candidate
subgroup `N̄`. -/
private theorem determinant_subgroup_residue_class_mem_lcm_rootsOfUnity_image
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c ∈
      (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  have hbase :
      fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c ∈
        (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) := by
    simpa [C, Qd] using
      determinant_subgroup_residue_class_mem_card_rootsOfUnity_image
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) c
  have hle :
      (rootsOfUnity (Nat.card C) k).map (QuotientGroup.mk' Qd) ≤
        (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
    -- Passing from `|C|` to the common `lcm` bound is a plain divisibility enlargement.
    exact
      Subgroup.map_mono
        (rootsOfUnity_le_of_dvd (Nat.dvd_lcm_right (Nat.card G) (Nat.card C)))
  exact hle hbase

/-- Helper for Theorem 17-17.6-1: transporting the fixed constituent first by `t` and then by `s`
is the same subrepresentation as transporting it once by `s * t`. This is the ambient carrier
identity underlying LinearRepresentations_Serre_1977's repeated section cycle. -/
private theorem transportedSubrepresentation_mul
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s t : G) :
    transportedSubrepresentation ρ (transportedSubrepresentation ρ Sbar t) s =
      transportedSubrepresentation ρ Sbar (s * t) := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    -- Unpack the two successive ambient images and collapse them with `ρ.map_mul`.
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    rcases Submodule.mem_map.mp hw with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
    simpa using LinearMap.congr_fun (ρ.map_mul s t) u
  · intro hv
    -- Factor the single `ρ (s * t)` image through the intermediate transported subrepresentation.
    rcases Submodule.mem_map.mp hv with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ t u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa using LinearMap.congr_fun (ρ.map_mul s t) u

/-- Helper for Theorem 17-17.6-1: in the cycle step, transporting the already moved constituent by
one more copy of `s` is the same as transport by `s ^ (n + 1)`. This isolates the exact carrier
rewrite needed before comparing the canonical reduced transport maps. -/
private theorem transportedSubrepresentation_pow_succ
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    transportedSubrepresentation ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s =
      transportedSubrepresentation ρ Sbar (s ^ (n + 1)) := by
  -- Rewrite the double transport with the literal `pow_succ` factorization.
  simpa [pow_succ] using
    transportedSubrepresentation_mul (I := I) (ρ := ρ) (Sbar := Sbar) s (s ^ n)

/-- Helper for Theorem 17-17.6-1: the canonical transport comparison is literally the restriction
of the ambient operator `ρ g` to the fixed constituent carrier. Recording this linear-map formula
avoids reopening the `equivMapOfInjective` term in the remaining cycle proof. -/
private theorem transportedSubrepresentation_rep_equiv_local_subtype
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (g : G) :
    (transportedSubrepresentation ρ Sbar g).toSubmodule.subtype.comp
        (transportedSubrepresentation_rep_equiv_local ρ Sbar g).toLinearMap =
      (ρ g).comp Sbar.toSubmodule.subtype := by
  -- Both sides are the same ambient vector `ρ g x` on the underlying carrier of `S̄`.
  ext x
  rfl

/-- Helper for Theorem 17-17.6-1: the canonical reduced-side transports compose in the ambient
representation exactly as the corresponding group elements do. This isolates the `pow_succ`
rewrite needed in the normalized section-cycle induction before the remaining endpoint comparison
against the chosen section family. -/
private theorem transportedSubrepresentation_rep_equiv_local_subtype_pow_succ
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) (n : ℕ) :
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype).comp
        (transportedSubrepresentation_rep_equiv_local
          ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap).comp
        (transportedSubrepresentation_rep_equiv_local ρ Sbar (s ^ n)).toLinearMap =
      ((ρ (s ^ (n + 1))).comp Sbar.toSubmodule.subtype) := by
  -- Rewrite the target carrier using `pow_succ`, then collapse the two canonical transports one
  -- ambient action at a time.
  calc
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype).comp
        (transportedSubrepresentation_rep_equiv_local
          ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap).comp
        (transportedSubrepresentation_rep_equiv_local ρ Sbar (s ^ n)).toLinearMap =
      (((transportedSubrepresentation ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toSubmodule.subtype).comp
          (transportedSubrepresentation_rep_equiv_local
            ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap).comp
          (transportedSubrepresentation_rep_equiv_local ρ Sbar (s ^ n)).toLinearMap := by
            rw [transportedSubrepresentation_pow_succ (I := I) (ρ := ρ) (Sbar := Sbar) s n]
    _ =
      (((ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype).comp
          (transportedSubrepresentation_rep_equiv_local ρ Sbar (s ^ n)).toLinearMap) := by
            simpa [LinearMap.comp_assoc] using
              congrArg
                (fun f :
                  (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule →ₗ[k] V =>
                    f.comp
                      (transportedSubrepresentation_rep_equiv_local ρ Sbar (s ^ n)).toLinearMap)
                (transportedSubrepresentation_rep_equiv_local_subtype
                  (I := I) (ρ := ρ)
                  (Sbar := transportedSubrepresentation ρ Sbar (s ^ n)) s)
    _ =
      ((ρ s).comp ((ρ (s ^ n)).comp Sbar.toSubmodule.subtype)) := by
            rw [← LinearMap.comp_assoc]
            rw [transportedSubrepresentation_rep_equiv_local_subtype
              (I := I) (ρ := ρ) (Sbar := Sbar) (g := s ^ n)]
    _ = ((ρ (s ^ (n + 1))).comp Sbar.toSubmodule.subtype) := by
            simpa [pow_succ, LinearMap.comp_assoc] using
              congrArg (fun f : V →ₗ[k] V => f.comp Sbar.toSubmodule.subtype) (ρ.map_mul s (s ^ n))

/-- Helper for Theorem 17-17.6-1: the literal `n`-fold section cycle in LinearRepresentations_Serre_1977's transport cover
`G₁` is obtained by repeatedly composing the chosen section value at `s` inside the transport
fiber over `s ^ n`. This is the source-faithful controlling object behind the remaining section
normalization step. -/
private noncomputable def fixed_constituent_section_cycle_fiber
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    (n : ℕ) →
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (s ^ n)
  | 0 =>
      fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  | n + 1 =>
      by
        -- Build the next cycle step by composing the current `s ^ n`-fiber point with the chosen
        -- section element in the `s`-fiber.
        simpa [pow_succ] using
          fixed_constituent_transport_fiber_comp
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_cycle_fiber
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2)

/-- Helper for Theorem 17-17.6-1: the determinant of the literal section cycle is the expected
power of the determinant of the chosen section element. This records the multiplicative part of
LinearRepresentations_Serre_1977's cycle argument before the reduced-action comparison is imposed. -/
private theorem fixed_constituent_section_cycle_fiber_det
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    ∀ n : ℕ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_cycle_fiber
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n) =
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2)) ^ n := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro n
  induction n with
  | zero =>
      -- The empty cycle is the identity element of `U₁`, whose determinant is `1`.
      simp [fixed_constituent_section_cycle_fiber, fixed_constituent_transport_fiber_det, sec]
  | succ n ihn =>
      -- One more cycle step composes with the chosen section value, so determinants multiply.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_cycle_fiber
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)) =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_section_cycle_fiber
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n) := by
              simpa [fixed_constituent_section_cycle_fiber, sec, pow_succ] using
                fixed_constituent_transport_fiber_det_comp
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                  (fixed_constituent_section_cycle_fiber
                    (p := p) (A := A) (G := G) (V := V)
                    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n)
                  ((sec s).2)
        _ =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n := by
                rw [ihn]
        _ =
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ (n + 1) := by
              rw [pow_succ]
              ac_rfl

/-- Helper for Theorem 17-17.6-1: specializing the literal section cycle at `n = |G|` produces an
actual point of the kernel fiber `U₁`. This is the concrete cycle element whose reduced action
must still be shown to be the identity in the remaining section-normalization blocker. -/
private noncomputable def fixed_constituent_section_card_cycle_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) := by
  -- Rewrite `s ^ |G| = 1` so the literal cycle lives in the kernel fiber `U₁`.
  simpa [pow_card_eq_one'] using
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (Nat.card G)

/-- Helper for Theorem 17-17.6-1: the literal `|G|`-cycle of the chosen section is already a
kernel scalar upstairs. The remaining source-faithful gap is only to prove that its reduction is
the identity, forcing the scalar residue to be `1`. -/
private theorem fixed_constituent_section_card_cycle_kernel_scalar
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∃ a : Aˣ,
      (fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
  -- Apply the kernel classification to the actual cycle element of `U₁`.
  exact
    hkernel
      (fixed_constituent_section_card_cycle_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)

/-- Helper for Theorem 17-17.6-1: at `s = 1`, the chosen lifted transport reduces to the inverse
of the chosen reduced-side comparison `hTransport 1`. This records the exact normalization gap:
with an arbitrary section of the nonempty fibers `U_s`, the reduced transport is not definitionally
the identity on `S̄`. -/
private theorem fixed_constituent_transport_aut_of_lift_reduction_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    red_S.comp
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
          (1 : G)).toLinearMap =
      (((hTransport (1 : G)).some.symm.toLinearMap.restrictScalars A).comp red_S) := by
  have hred :=
    fixed_constituent_transport_aut_of_lift_reduction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G)
  -- Cancel the chosen reduced-side comparison pointwise to isolate the actual reduction of the
  -- lifted transport operator.
  ext x
  have hred_apply :=
    LinearMap.congr_fun hred x
  have hcanon_apply :
      (((transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G)).toLinearMap.restrictScalars A).comp
          red_S) x =
        red_S x := by
    -- At `g = 1`, the canonical transport is literally the identity on the fixed constituent.
    simp [transportedSubrepresentation_rep_equiv_local, transportedSubrepresentation,
      LinearMap.comp_apply]
  have hcancel :=
    congrArg
      (((hTransport (1 : G)).some.symm.toLinearMap.restrictScalars A))
      (hred_apply.trans hcanon_apply)
  simpa [LinearMap.comp_apply] using hcancel

/-- Helper for Theorem 17-17.6-1: normalize the reduced-side transport family by composing every
chosen comparison with the inverse of the comparison at `1`. This keeps the transport fibers
`U_s` unchanged, makes the new comparison at `1` canonical, and preserves every determinant class
modulo `d`-th powers because changing section points inside one fiber only changes determinants by
such a power. -/
private theorem fixed_constituent_transport_family_normalization
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ∃ hTransport0 :
        ∀ s : G,
          Nonempty
            (Sbar.toRepresentation.Equiv
              (transportedSubrepresentation ρ Sbar s).toRepresentation),
      ∃ hTransportLift0 :
          ∀ s : G,
            IsResidueFieldLift
              (transportedSubrepresentation ρ Sbar s).toRepresentation
              ρA_I
              (((hTransport0 s).some.toLinearMap.restrictScalars A).comp red_S),
        (hTransport0 (1 : G)).some =
            transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G) ∧
          ∀ s : G,
            fixed_constituent_section_determinant_class
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s =
              fixed_constituent_section_determinant_class
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s := by
  let u1raw :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G)
  have u1 :
      Representation.Equiv ρA_I ρA_I := by
    -- At `s = 1`, the conjugated source action is definitionally the original `I`-action.
    simpa using u1raw
  let normalize : Sbar.toRepresentation.Equiv Sbar.toRepresentation :=
    (transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G)).trans
      ((hTransport (1 : G)).some.symm)
  let hTransport0 :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation) :=
    fun s ↦ ⟨normalize.trans (hTransport s).some⟩
  have hnormalize_red :
      ((normalize.toLinearMap.restrictScalars A).comp red_S) =
        red_S.comp u1.toLinearMap := by
    -- Compose the `s = 1` reduction identity with the inverse chosen comparison to isolate the
    -- fixed normalization automorphism on `S̄`.
    have hred1 :=
      fixed_constituent_transport_aut_of_lift_reduction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
    have hred1' :=
      congrArg
        (fun f : P_S →ₗ[A] (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule =>
          (((hTransport (1 : G)).some.symm.toLinearMap.restrictScalars A).comp f))
        hred1
    simpa [normalize, LinearMap.comp_assoc] using hred1'
  have hTransportLift0 :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport0 s).some.toLinearMap.restrictScalars A).comp red_S) := by
    intro s
    have hred0 :
        (((hTransport0 s).some.toLinearMap.restrictScalars A).comp red_S) =
          ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp u1.toLinearMap) := by
      -- The normalized comparison is obtained by precomposing every old reduction map with the
      -- fixed lifted automorphism `u1`.
      simpa [hTransport0, normalize, LinearMap.comp_assoc] using
        congrArg
          (fun f : P_S →ₗ[A] Sbar.toSubmodule =>
            (((hTransport s).some.toLinearMap.restrictScalars A).comp f))
          hnormalize_red
    simpa [hred0] using
      residueFieldLift_of_equiv_source_local
        (A := A)
        (ρ := (transportedSubrepresentation ρ Sbar s).toRepresentation)
        (ρA := ρA_I)
        (ρA' := ρA_I)
        (red := (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
        (hLift := hTransportLift s)
        u1
  refine ⟨hTransport0, hTransportLift0, ?_, ?_⟩
  · -- By construction the new comparison at `1` is the canonical transported comparison.
    ext x
    simp [hTransport0, normalize]
  · intro s
    let sec0 :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0
    have hscalar :
        ∀ f : ρA_I.IntertwiningMap ρA_I,
          ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
      -- The scalar classification of `End_{A[I]}(P_S)` is independent of the reduced-side
      -- section choice.
      intro f
      exact
        fixed_constituent_lift_equivariant_endomorphism_scalar
          (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
          hSbar_irred ρA_I red_S hLiftSbar f
    have hkernel :
        ∀ u :
          fixed_constituent_transport_fiber
            (A := A) (G := G) I ρA_I (1 : G),
          ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
      -- The kernel fiber `U₁` is still the scalar unit group `Aˣ`.
      intro u
      exact
        fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
          (A := A) (G := G) (I := I) ρA_I hscalar u
    obtain ⟨a, ha⟩ :=
      fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
        s (sec0 s).2
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    have hpow_one :
        QuotientGroup.mk' Qd ((Units.map (IsLocalRing.residue A) a) ^ d) = 1 := by
      -- Quotienting by `d`-th powers kills the scalar discrepancy between the two section
      -- determinants.
      exact
        (QuotientGroup.eq_one_iff
          ((Units.map (IsLocalRing.residue A) a) ^ d)).2 ⟨Units.map (IsLocalRing.residue A) a, rfl⟩
    -- Replace the normalized section point by the original one inside the same transport fiber.
    calc
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s =
        QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) ((sec0 s).2))) := by
            rfl
      _ =
        QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) ((sec s).2)) *
            (Units.map (IsLocalRing.residue A) a) ^ d) := by
              rw [ha, Units.map_mul, MonoidHom.map_pow]
      _ =
        QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) ((sec s).2))) := by
              rw [map_mul, hpow_one, mul_one]
      _ =
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s := by
            rfl

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is the canonical one, LinearRepresentations_Serre_1977's literal `|G|`-cycle in the kernel fiber
`U₁` should reduce to the identity endomorphism of the fixed constituent `S̄`. Isolating this
bridge keeps the remaining section-normalization blocker separate from the later roots-of-unity
packaging. -/
private theorem fixed_constituent_section_cycle_reduction_in_ambient_zero
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G))
    (s : G) :
    (((transportedSubrepresentation ρ Sbar (s ^ 0)).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport (s ^ 0)).some.toLinearMap.restrictScalars A).comp red_S).comp
          (fixed_constituent_section_cycle_fiber
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s 0).toLinearMap)) =
      ((((ρ (s ^ 0)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  -- At `n = 0`, the cycle is the identity and normalization at `1` makes the endpoint
  -- comparison literally the canonical transport.
  rw [pow_zero, hTransportOne]
  simpa [fixed_constituent_section_cycle_fiber, LinearMap.comp_assoc] using
    congrArg
      (fun f : Sbar.toSubmodule →ₗ[k] V => (f.restrictScalars A).comp red_S)
      (transportedSubrepresentation_rep_equiv_local_subtype
        (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G))

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_step_reduction_in_ambient
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
          (sec s).2.toLinearMap)) =
      ((((ρ s).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hred :=
    fixed_constituent_transport_aut_of_lift_reduction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  have hred' :=
    congrArg
      (fun f : P_S →ₗ[A] (transportedSubrepresentation ρ Sbar s).toSubmodule =>
        ((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp f)
      hred
  -- Compose the chosen section reduction into ambient `V`, then rewrite the canonical transport
  -- as the literal ambient action of `ρ s` on the fixed constituent.
  calc
    (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp
          (sec s).2.toLinearMap)) =
      (((transportedSubrepresentation ρ Sbar s).toSubmodule.subtype.restrictScalars A).comp
        (((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S)) := by
            simpa [sec, LinearMap.comp_assoc] using hred'
    _ =
      ((((ρ s).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
            simpa [LinearMap.comp_assoc] using
              congrArg
                (fun f : Sbar.toSubmodule →ₗ[k] V => (f.restrictScalars A).comp red_S)
                (transportedSubrepresentation_rep_equiv_local_subtype
                  (I := I) (ρ := ρ) (Sbar := Sbar) s)

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_cycle_fiber_succ_toLinearMap
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)).toLinearMap =
      cycle_n.toLinearMap.comp (sec s).2.toLinearMap := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  -- Expanding the recursive cycle definition exposes the literal composition with the chosen
  -- section value at `s`.
  rfl

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_cycle_source_lift
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    IsResidueFieldLift
      (transportedSubrepresentation ρ Sbar (s ^ n)).toRepresentation
      (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
      ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
        cycle_n.toLinearMap) := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  -- The cycle already is the required source equivalence from the conjugated lift to the fixed
  -- lift, so the shifted reduction map is obtained by the general source-transport lemma.
  simpa [cycle_n] using
    residueFieldLift_of_equiv_source_local
      (A := A)
      (ρ := (transportedSubrepresentation ρ Sbar (s ^ n)).toRepresentation)
      (ρA := ρA_I)
      (ρA' := ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
      (red := (((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S))
      (hLift := hTransportLift (s ^ n))
      cycle_n

/-- Helper for Theorem 17-17.6-1: after transporting the fixed constituent around the `n`-cycle,
the same reduced transport family reindexes along right multiplication by `s ^ n`, and the cycle
source equivalence transports the fixed lift to that shifted family. -/
private theorem shifted_cycle_transport_family
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s t : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    ∃ e : Tn.toRepresentation.Equiv (transportedSubrepresentation ρ Tn t).toRepresentation,
      IsResidueFieldLift
        (transportedSubrepresentation ρ Tn t).toRepresentation
        (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        (((e.toLinearMap.restrictScalars A).comp
            ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle_n.toLinearMap))) := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let eBase :
      Tn.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation :=
    (hTransport (s ^ n)).some.symm.trans (hTransport (t * s ^ n)).some
  let eShift :
      Tn.toRepresentation.Equiv (transportedSubrepresentation ρ Tn t).toRepresentation := by
    -- Reindex the old transport family along right multiplication by `s ^ n`.
    simpa [Tn, transportedSubrepresentation_mul (I := I) (ρ := ρ) (Sbar := Sbar) t (s ^ n)] using
      eBase
  refine ⟨eShift, ?_⟩
  have hbase :
      IsResidueFieldLift
        (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation
        (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        ((((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
          cycle_n.toLinearMap) := by
    -- The cycle source equivalence moves the original lift to the `n`-shifted source.
    simpa [cycle_n] using
      residueFieldLift_of_equiv_source_local
        (A := A)
        (ρ := (transportedSubrepresentation ρ Sbar (t * s ^ n)).toRepresentation)
        (ρA := ρA_I)
        (ρA' := ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom)
        (red := (((hTransport (t * s ^ n)).some.toLinearMap.restrictScalars A).comp red_S))
        (hLift := hTransportLift (t * s ^ n))
        cycle_n
  -- After expanding the reindexed comparison, the reduction map is exactly the shifted-family one.
  simpa [cycle_n, Tn, eBase, eShift, LinearMap.comp_assoc,
    transportedSubrepresentation_mul (I := I) (ρ := ρ) (Sbar := Sbar) t (s ^ n)] using hbase

/-- Helper for Theorem 17-17.6-1: the chosen section element `(sec s).2` can be re-read over the
shifted cycle source as a map from the `(s ^ (n + 1))`-twisted lift to the `(s ^ n)`-twisted
lift. This isolates the source-twist reindexing that remains before the endpoint comparison. -/
private noncomputable def fixed_constituent_section_step_over_shifted_cycle_source
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    Representation.Equiv
      (ρA_I.comp (MulAut.conjNormal (s ^ (n + 1))⁻¹).toMonoidHom)
      (ρA_I.comp (MulAut.conjNormal (s ^ n)⁻¹).toMonoidHom) := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  refine Representation.Equiv.mk (sec s).2.toLinearEquiv ?_
  intro a
  ext x
  -- Route correction: the same linear operator `(sec s).2` is reused, but now the source action
  -- is first reindexed by `(s ^ n)`. The only content is the conjugation identity
  -- `s⁻¹ * (s ^ n)⁻¹ * a * (s ^ n) * s = (s ^ (n + 1))⁻¹ * a * (s ^ (n + 1))`.
  simpa [sec, pow_succ, MulAut.conjNormal_apply, mul_assoc] using
    LinearMap.congr_fun ((sec s).2.isIntertwining' ((MulAut.conjNormal (s ^ n)⁻¹) a)) x

/-- Helper for Theorem 17-17.6-1: on the common carrier `P_S`, the shifted source-step map is
exactly the consecutive-cycle comparison from the `(n + 1)`-cycle back to the `n`-cycle. This is
the source-faithful object LinearRepresentations_Serre_1977 controls, so later proofs can avoid introducing a fresh shifted
transport witness. -/
private theorem fixed_constituent_section_step_over_shifted_cycle_source_toLinearMap
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let cycle_succ :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
    (fixed_constituent_section_step_over_shifted_cycle_source
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).toLinearMap =
      (cycle_succ.trans cycle_n.symm).toLinearMap := by
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  -- Both linear maps are the literal section operator `(sec s).2` on `P_S`; the right-hand side
  -- only needs the recursive formula for `cycle_{n + 1}`.
  ext x
  rw [fixed_constituent_section_cycle_fiber_succ_toLinearMap
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n]
  simp [cycle_n, cycle_succ, fixed_constituent_section_step_over_shifted_cycle_source,
    LinearMap.comp_assoc]

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_cycle_succ_reduction_in_ambient
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let cycle_succ :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
    let red_n :=
      ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
        cycle_n.toLinearMap)
    (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.restrictScalars A).comp
        ((((hTransport (s ^ (n + 1))).some.toLinearMap.restrictScalars A).comp red_S).comp
          cycle_succ.toLinearMap)) =
      ((((ρ s).comp Tn.toSubmodule.subtype).restrictScalars A).comp red_n) := by
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let cycle_n :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  let red_n :=
    ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp cycle_n.toLinearMap)
  -- Route correction: compare the successor step only after composing into the ambient carrier
  -- `V`, where the canonical transport is the literal action of `ρ s` on the moved constituent.
  ext x
  simp only [LinearMap.comp_apply]
  simp [Tn, cycle_n, cycle_succ, red_n, LinearMap.comp_assoc, pow_succ,
    transportedSubrepresentation_pow_succ,
    fixed_constituent_section_cycle_fiber_succ_toLinearMap,
    fixed_constituent_section_step_over_shifted_cycle_source_toLinearMap,
    transportedSubrepresentation_rep_equiv_local_subtype]

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_step_reduction_after_cycle_precompose
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) (n : ℕ) :
    let cycle_n :=
      fixed_constituent_section_cycle_fiber
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ((((hTransport (s ^ (n + 1))).some.toLinearMap.restrictScalars A).comp red_S).comp
        (cycle_n.toLinearMap.comp (sec s).2.toLinearMap)) =
      (((transportedSubrepresentation_rep_equiv_local
              ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap.restrictScalars
          A).comp
        ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
          cycle_n.toLinearMap)) := by
  let Tn := transportedSubrepresentation ρ Sbar (s ^ n)
  let cycle_succ :=
    fixed_constituent_section_cycle_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
  have hambient :=
    fixed_constituent_section_cycle_succ_reduction_in_ambient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
  -- Move the comparison into the ambient carrier `V`, then cancel the transported subtype map
  -- pointwise to recover the equality inside the moved constituent.
  ext x
  apply Subtype.ext
  have hx := LinearMap.congr_fun hambient x
  simpa [Tn, cycle_n, cycle_succ, sec, LinearMap.comp_assoc,
    fixed_constituent_section_step_over_shifted_cycle_source_toLinearMap]
    using hx

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is canonical, LinearRepresentations_Serre_1977's literal `n`-step section cycle reduces to the
canonical ambient transport over `s ^ n`. The normalization hypothesis is necessary already at
`n = 0`, where the empty cycle forces the endpoint comparison at `1` to be the canonical one. -/
private theorem fixed_constituent_section_cycle_reduction_in_ambient
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G))
    (s : G) :
    ∀ n : ℕ,
      (((transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype.restrictScalars A).comp
          ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
            (fixed_constituent_section_cycle_fiber
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n).toLinearMap)) =
        ((((ρ (s ^ n)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
  -- Route correction: the recurring coercion mismatch is isolated here, at the ambient `V`
  -- level, before we try to cancel subtype inclusions back inside `S̄`.
  intro n
  induction n with
  | zero =>
      -- The normalized base point at `1` closes the empty-cycle case directly.
      simpa using
        fixed_constituent_section_cycle_reduction_in_ambient_zero
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hTransportOne s
  | succ n ihn =>
      let cycle_n :=
        fixed_constituent_section_cycle_fiber
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
      let cycle_succ :=
        fixed_constituent_section_cycle_fiber
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s (n + 1)
      have hendpoint :
          ((((hTransport (s ^ (n + 1))).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle_succ.toLinearMap) =
            (((transportedSubrepresentation_rep_equiv_local
                    ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap.restrictScalars
                A).comp
              ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
                cycle_n.toLinearMap)) := by
        -- Expand the `n + 1` cycle once so the blocker is the explicit endpoint comparison after
        -- composing with the chosen section value at `s`.
        rw [fixed_constituent_section_cycle_fiber_succ_toLinearMap
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n]
        -- The recursive cycle has been eliminated, so the whole `succ` step now depends only on
        -- the named shifted-source bridge recorded above.
        simpa [cycle_n] using
          fixed_constituent_section_step_reduction_after_cycle_precompose
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s n
      -- Once the endpoint comparison is isolated, the ambient `pow_succ` transport and the
      -- induction hypothesis finish the `n + 1` step by plain reassociation.
      calc
        (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.restrictScalars
            A).comp
            ((((hTransport (s ^ (n + 1))).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle_succ.toLinearMap)) =
          (((transportedSubrepresentation ρ Sbar (s ^ (n + 1))).toSubmodule.subtype.restrictScalars
              A).comp
            (((transportedSubrepresentation_rep_equiv_local
                    ρ (transportedSubrepresentation ρ Sbar (s ^ n)) s).toLinearMap.restrictScalars
                A).comp
              ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
                cycle_n.toLinearMap))) := by
                  rw [hendpoint]
        _ =
          ((((ρ s).comp (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule.subtype)
              .restrictScalars A).comp
            ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle_n.toLinearMap)) := by
                simpa [LinearMap.comp_assoc] using
                  congrArg
                    (fun f :
                      (transportedSubrepresentation ρ Sbar (s ^ n)).toSubmodule →ₗ[k] V =>
                        (f.restrictScalars A).comp
                          ((((hTransport (s ^ n)).some.toLinearMap.restrictScalars A).comp red_S).comp
                            cycle_n.toLinearMap))
                    (transportedSubrepresentation_rep_equiv_local_subtype
                      (I := I) (ρ := ρ)
                      (Sbar := transportedSubrepresentation ρ Sbar (s ^ n)) s)
        _ =
          ((((ρ s).comp ((ρ (s ^ n)).comp Sbar.toSubmodule.subtype)).restrictScalars A).comp
            red_S) := by
              rw [← LinearMap.comp_assoc]
              simpa [cycle_n] using congrArg (fun f : P_S →ₗ[A] V => ((ρ s).restrictScalars A).comp f) ihn
        _ = ((((ρ (s ^ (n + 1))).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
              simpa [pow_succ, LinearMap.comp_assoc] using
                congrArg
                  (fun f : V →ₗ[k] V => (f.comp Sbar.toSubmodule.subtype).restrictScalars A |>.comp red_S)
                  (ρ.map_mul s (s ^ n))

/-- Helper for Theorem 17-17.6-1: once the reduced-side section has been normalized so that the
chosen comparison at `1` is the canonical one, LinearRepresentations_Serre_1977's literal `|G|`-cycle in the kernel fiber
`U₁` reduces to the identity after composing into the ambient representation. This is the ambient
specialization of the source cycle argument before canceling the subtype inclusion of `S̄`. -/
private theorem fixed_constituent_section_card_cycle_kernel_reduction_comp_eq
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G))
    (s : G) :
    red_S.comp
        (fixed_constituent_section_card_cycle_kernel
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).toLinearMap =
      red_S := by
  let cycle :=
    fixed_constituent_section_card_cycle_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  have hambient :=
    fixed_constituent_section_cycle_reduction_in_ambient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      hTransportOne s (Nat.card G)
  have hcanonOne :
      (((transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype.restrictScalars A).comp
          ((transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G)).toLinearMap.restrictScalars
            A)) =
        Sbar.toSubmodule.subtype.restrictScalars A := by
    -- At the endpoint `s ^ |G| = 1`, the canonical transported comparison is just the ambient
    -- inclusion of the fixed constituent.
    simpa using
      congrArg
        (fun f : Sbar.toSubmodule →ₗ[k] V => f.restrictScalars A)
        (transportedSubrepresentation_rep_equiv_local_subtype
          (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G))
  have hcard :
      ((Sbar.toSubmodule.subtype.restrictScalars A).comp (red_S.comp cycle.toLinearMap)) =
        (Sbar.toSubmodule.subtype.restrictScalars A).comp red_S := by
    have hambient_one :
        (((transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype.restrictScalars A).comp
            ((((hTransport (1 : G)).some.toLinearMap.restrictScalars A).comp red_S).comp
              cycle.toLinearMap)) =
          ((((ρ (1 : G)).comp Sbar.toSubmodule.subtype).restrictScalars A).comp red_S) := by
      -- Specialize the ambient cycle identity at `n = |G|`, where the source relation
      -- `s ^ |G| = 1` lands us back on the fixed constituent.
      simpa [cycle, pow_card_eq_one'] using hambient
    -- Rewrite the normalized endpoint comparison at `1` to the canonical transport, then
    -- collapse the latter to the ambient inclusion of `S̄`.
    rw [hTransportOne] at hambient_one
    rw [LinearMap.comp_assoc] at hambient_one
    rw [hcanonOne] at hambient_one
    simpa using hambient_one
  -- Cancel the ambient subtype inclusion pointwise to recover the desired equality in `S̄`.
  ext x
  exact Sbar.toSubmodule.subtype.injective (LinearMap.congr_fun hcard x)

/-- Helper for Theorem 17-17.6-1: once the `|G|`-cycle acts trivially after reduction on the
fixed lift carrier, the Chapter `14` endomorphism-transport map identifies the reduced kernel
element with the identity endomorphism of `S̄`. -/
private theorem fixed_constituent_section_card_cycle_kernel_reduction_eq_id
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hTransportOne :
      (hTransport (1 : G)).some =
        transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G))
    (s : G) :
    hLiftSbar.endAlgHom
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_card_cycle_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
      Representation.IntertwiningMap.id Sbar.toRepresentation := by
  let cycle :=
    fixed_constituent_section_card_cycle_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hcomp :
      red_S.comp cycle.toLinearMap = red_S := by
    -- This is the remaining literal cycle-reduction identity in LinearRepresentations_Serre_1977's source route.
    simpa [cycle] using
      fixed_constituent_section_card_cycle_kernel_reduction_comp_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        hTransportOne s
  have hsurj : Function.Surjective red_S := by
    -- The fixed constituent lift is a residue-field reduction, so the reduction map is
    -- surjective on the underlying carriers.
    exact fixed_constituent_reduction_surjective (A := A) (H := I) hred
  ext y
  rcases hsurj y with ⟨x, rfl⟩
  -- Compare both reduced endomorphisms on an arbitrary reduced vector coming from `x : P_S`.
  calc
    hLiftSbar.endAlgHom
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) cycle) (red_S x) =
      red_S (cycle x) := by
        simpa [cycle] using
          LinearMap.IsResidueFieldReduction.endAlgHom_comp_apply hred
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) cycle) x
    _ = red_S x := by
          simpa [LinearMap.comp_apply] using congrArg (fun f : P_S →ₗ[A] Sbar.toSubmodule => f x) hcomp
    _ = Representation.IntertwiningMap.id Sbar.toRepresentation (red_S x) := by
          rfl

/-- Helper for Theorem 17-17.6-1: a kernel-fiber element `u ∈ U₁` whose reduction fixes `S̄`
pointwise already reduces to the identity intertwining endomorphism. This is the generic
`U₁` version of the cycle-specific argument used earlier for LinearRepresentations_Serre_1977's section cycles. -/
private theorem fixed_constituent_transport_kernel_reduction_eq_id_of_comp_eq
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G))
    (hcomp : red_S.comp u.toLinearMap = red_S) :
    hLiftSbar.endAlgHom
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
      Representation.IntertwiningMap.id Sbar.toRepresentation := by
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hsurj : Function.Surjective red_S := by
    -- The fixed constituent lift is a residue-field reduction, so `red_S` is surjective.
    exact fixed_constituent_reduction_surjective (A := A) (H := I) hred
  ext y
  rcases hsurj y with ⟨x, rfl⟩
  -- Compare both reduced endomorphisms on an arbitrary reduced vector coming from `x : P_S`.
  calc
    hLiftSbar.endAlgHom
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) (red_S x) =
      red_S (u x) := by
        simpa using
          LinearMap.IsResidueFieldReduction.endAlgHom_comp_apply hred
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) x
    _ = red_S x := by
          simpa [LinearMap.comp_apply] using congrArg (fun f : P_S →ₗ[A] Sbar.toSubmodule => f x) hcomp
    _ = Representation.IntertwiningMap.id Sbar.toRepresentation (red_S x) := by
          rfl

/-- Helper for Theorem 17-17.6-1: if a kernel-fiber element `u ∈ U₁` reduces to the identity on
`S̄`, then its determinant has residue `1`. This packages the scalar-kernel argument in the exact
form needed for the remaining normalized-determinant upgrade. -/
private theorem fixed_constituent_transport_fiber_det_residue_eq_one_of_reduction_eq_id
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G))
    (hcomp : red_S.comp u.toLinearMap = red_S) :
    Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) = 1 := by
  let d : ℕ := Module.finrank A P_S
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- LinearRepresentations_Serre_1977's lifted fixed constituent still has only scalar equivariant endomorphisms.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V)
        hp I hIcop (ρ := ρ) (Sbar := Sbar) hSbar_irred ρA_I red_S hLiftSbar f
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
      (A := A) (G := G) (I := I) ρA_I hscalar u
  have hkernel_map :
      hLiftSbar.endAlgHom
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
    have hscalar_end :
        fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
          (a : A) • Representation.IntertwiningMap.id ρA_I := by
      -- The kernel element itself is the scalar homothety classified above.
      change
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u : P_S →ₗ[A] P_S) =
          (a : A) • LinearMap.id
      simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
        congrArg (fun e : P_S ≃ₗ[A] P_S => (e : P_S →ₗ[A] P_S)) ha
    rw [hscalar_end]
    simpa using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar (a : A)
  have hkernel_id :
      hLiftSbar.endAlgHom
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u) =
        Representation.IntertwiningMap.id Sbar.toRepresentation := by
    -- The hypothesis `red_S ∘ u = red_S` is exactly the generic identity-reduction input.
    exact
      fixed_constituent_transport_kernel_reduction_eq_id_of_comp_eq
        (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar) ρA_I red_S hLiftSbar u hcomp
  have hresidue_a_eq_one : IsLocalRing.residue A (a : A) = 1 := by
    have hscalar_eq :
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id Sbar.toRepresentation =
          (1 : k) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
      simpa [hkernel_id] using hkernel_map
    have hfinrank :
        Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) = 1 := by
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := Sbar.toRepresentation)
    have hpos :
        0 < Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) := by
      omega
    letI :
        Nontrivial (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
      FiniteDimensional.nontrivial_of_finrank_pos hpos
    have hId_ne :
        (Representation.IntertwiningMap.id Sbar.toRepresentation :
          Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0 := by
      simpa using
        (one_ne_zero :
          (1 : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0)
    exact smul_left_injective k hId_ne hscalar_eq
  have hdet :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
        a ^ d := by
    -- Once `u` is identified with the scalar homothety `a • id`, its determinant is `a ^ d`.
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha
  -- Reduce the determinant formula and use that the scalar residue itself is already `1`.
  rw [hdet, MonoidHom.map_pow]
  apply Units.ext
  simp [hresidue_a_eq_one, d]

/-- Helper for Theorem 17-17.6-1: if two elements of the same transport fiber induce the same
reduction map on the fixed constituent, then the determinant of their kernel ratio reduces to `1`.
This isolates the principal-unit conclusion from the still-open task of identifying the correct
same-fiber comparison in the normalized determinant branch. -/
private theorem fixed_constituent_transport_fiber_ratio_det_residue_eq_one_of_equal_reduction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    {s : G}
    (u v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (hred : red_S.comp u.toLinearMap = red_S.comp v.toLinearMap) :
    Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v)) = 1 := by
  let w :=
    fixed_constituent_transport_fiber_ratio
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v
  have hw_comp : red_S.comp w.toLinearMap = red_S := by
    -- Compare both sides after precomposing with `v`; surjectivity of the fiber equivalence `v`
    -- then cancels the common source.
    ext y
    obtain ⟨x, rfl⟩ := v.toLinearEquiv.surjective y
    have hred_apply :
        red_S (u x) = red_S (v x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hred x
    have hw_apply :
        red_S (w (v x)) = red_S (u x) := by
      simpa [w, LinearMap.comp_apply] using
        congrArg (fun f : P_S →ₗ[A] Sbar.toSubmodule => f x)
          (congrArg (fun f : P_S →ₗ[A] P_S => red_S.comp f)
            (fixed_constituent_transport_fiber_ratio_comp_right
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v))
    exact hw_apply.trans hred_apply
  -- The ratio now lies in the kernel fiber and reduces to the identity, so its determinant is a
  -- principal unit.
  simpa [w] using
    fixed_constituent_transport_fiber_det_residue_eq_one_of_reduction_eq_id
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar w hw_comp

/-- Helper for Theorem 17-17.6-1: once the normalized `|G|`-cycle in the kernel fiber reduces to
the identity on `S̄`, the chosen section determinant class is already represented by an actual
`|G|`-th root of unity in the residue field. This separates the scalar-to-roots-of-unity bridge
from the still-open cycle-reduction induction. -/
private theorem normalized_section_determinant_class_mem_card_rootsOfUnity_image
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (hcycle_id :
      hLiftSbar.endAlgHom
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_card_cycle_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
        Representation.IntertwiningMap.id Sbar.toRepresentation) :
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) := by
  let d : ℕ := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- LinearRepresentations_Serre_1977's fixed lift has only scalar equivariant endomorphisms.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V)
        hp I hIcop (ρ := ρ) (Sbar := Sbar) hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- The kernel fiber `U₁` is identified with the scalar unit group `Aˣ`.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  obtain ⟨a, ha⟩ :=
    fixed_constituent_section_card_cycle_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  have hkernel_map :
      hLiftSbar.endAlgHom
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_card_cycle_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
    -- Reduce the scalar kernel element through the endomorphism algebra map.
    have hscalar_end :
        fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_card_cycle_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
          (a : A) • Representation.IntertwiningMap.id ρA_I := by
      -- The cycle kernel element itself is the scalar homothety classified above.
      change
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_card_cycle_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) :
          P_S →ₗ[A] P_S) =
          (a : A) • LinearMap.id
      simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
        congrArg (fun e : P_S ≃ₗ[A] P_S => (e : P_S →ₗ[A] P_S)) ha
    rw [hscalar_end]
    simpa using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar (a : A)
  have hresidue_a_eq_one : IsLocalRing.residue A (a : A) = 1 := by
    -- Compare the reduced scalar line with the already-known identity endomorphism.
    have hscalar_eq :
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id Sbar.toRepresentation =
          (1 : k) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
      simpa [hcycle_id] using hkernel_map
    have hfinrank :
        Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) = 1 := by
      simpa using
        Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := Sbar.toRepresentation)
    have hpos :
        0 < Module.finrank k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) := by
      omega
    letI :
        Nontrivial (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
      FiniteDimensional.nontrivial_of_finrank_pos hpos
    have hId_ne :
        (Representation.IntertwiningMap.id Sbar.toRepresentation :
          Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0 := by
      simpa using
        (one_ne_zero :
          (1 : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) ≠ 0)
    exact smul_left_injective k hId_ne hscalar_eq
  have hdet_cycle :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_card_cycle_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
        a ^ d := by
    -- The scalar kernel description determines the determinant of the `|G|`-cycle upstairs.
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha
  have hpow_upstairs :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 ^ Nat.card G =
        a ^ d := by
    -- Reexpress the literal kernel cycle as the `|G|`-fold product of the chosen section value.
    calc
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 ^ Nat.card G =
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_section_card_cycle_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) := by
              symm
              simpa [sec, fixed_constituent_section_card_cycle_kernel] using
                fixed_constituent_section_cycle_fiber_det
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
                  (Nat.card G)
      _ = a ^ d := hdet_cycle
  let ζ : kˣ :=
    Units.map (IsLocalRing.residue A)
      (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2)
  have hpow :
      ζ ^ Nat.card G = 1 := by
    -- Reduce the upstairs determinant identity and use that the scalar residue is actually `1`.
    have hres :
        ζ ^ Nat.card G = (Units.map (IsLocalRing.residue A) a) ^ d := by
      simpa [ζ, d, MonoidHom.map_pow] using
        congrArg (Units.map (IsLocalRing.residue A)) hpow_upstairs
    rw [hres]
    have hunit_one : Units.map (IsLocalRing.residue A) a = 1 := by
      apply Units.ext
      simpa using hresidue_a_eq_one
    rw [hunit_one]
    simp
  letI : NeZero (Nat.card G) := NeZero.of_gt Nat.card_pos
  let ξ : rootsOfUnity (Nat.card G) k := rootsOfUnity.mkOfPowEq (ζ : k) (by simpa using hpow)
  refine ⟨ξ, ?_⟩
  -- Package the actual section determinant as the required roots-of-unity representative before
  -- passing to the quotient modulo `d`-th powers.
  change QuotientGroup.mk' Qd ((ξ : rootsOfUnity (Nat.card G) k : kˣ)) =
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2))
  congr 1
  apply Units.ext
  simpa [ξ, ζ]

/-- Helper for Theorem 17-17.6-1: the missing source-faithful bridge is that each chosen section
determinant class already lands in the common `lcm`-bounded roots-of-unity subgroup. This is the
section-family analogue of the already closed determinant-subgroup normalization above. -/
private theorem section_determinant_class_mem_lcm_rootsOfUnity_image
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
  obtain ⟨hTransport0, hTransportLift0, hTransportOne0, hclass_eq⟩ :=
    fixed_constituent_transport_family_normalization
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hmem0 :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s ∈
        (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
    -- Route correction: after the new normalization theorem, the roots-of-unity step only needs
    -- the normalized cycle reduction at `s = 1`; all comparison back to the original family is
    -- now closed by `hclass_eq`.
    have hcycle_id :
        hLiftSbar.endAlgHom
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_section_card_cycle_kernel
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s)) =
          Representation.IntertwiningMap.id Sbar.toRepresentation := by
      -- The open frontier is now exactly the normalized `|G|`-cycle reduction.
      simpa using
        fixed_constituent_section_card_cycle_kernel_reduction_eq_id
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0
          hTransportOne0 s
    have hmem_card :
        let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
        fixed_constituent_section_determinant_class
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s ∈
          (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) := by
      -- The only source-level input here is the normalized cycle identity at `U₁`.
      simpa using
        normalized_section_determinant_class_mem_card_rootsOfUnity_image
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport0 hTransportLift0 s
          hcycle_id
    have hle :
        (rootsOfUnity (Nat.card G) k).map
            (QuotientGroup.mk'
              ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) ≤
          (rootsOfUnity
              (Nat.lcm
                (Nat.card G)
                (Nat.card
                  (fixed_constituent_determinant_subgroup
                    (A := A) (G := G) (I := I) ρA_I))) k).map
            (QuotientGroup.mk'
              ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) := by
      -- Enlarging the exponent from `|G|` to the common `lcm` preserves roots of unity.
      exact
        Subgroup.map_mono
          (rootsOfUnity_le_of_dvd
            (Nat.dvd_lcm_left
              (Nat.card G)
              (Nat.card
                (fixed_constituent_determinant_subgroup
                  (A := A) (G := G) (I := I) ρA_I))))
    exact hle hmem_card
  -- Transport the normalized roots-of-unity conclusion back to the original arbitrary family.
  simpa [hclass_eq s] using hmem0

/-- Helper for Theorem 17-17.6-1: once both explicit generator families are known to lie in the
same bounded roots-of-unity subgroup, the candidate subgroup `N̄` is contained in that subgroup
by a single closure argument. This isolates the closure step from the remaining section-side
normalization and final projective-cover packaging. -/
private theorem candidate_subgroup_le_rootsOfUnity_lcm_image
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
    fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
      Dbar := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
  -- The candidate subgroup is generated by the section family and the determinant subgroup image,
  -- so once each generator family is known to lie in `Dbar`, closure finishes the argument.
  refine Subgroup.closure_le.2 ?_
  intro y hy
  rcases hy with hy | hy
  · rcases hy with ⟨s, rfl⟩
    simpa [C, Qd, Dbar] using
      section_determinant_class_mem_lcm_rootsOfUnity_image
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
  · rcases hy with ⟨c, rfl⟩
    simpa [C, Qd, Dbar] using
      determinant_subgroup_residue_class_mem_lcm_rootsOfUnity_image
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) c

/-- Helper for Theorem 17-17.6-1: the explicit residue-quotient candidate subgroup is already a
torsion group, because it is generated by the torsion section classes and the torsion image of the
determinant subgroup `C`. -/
private theorem fixed_constituent_projective_extension_candidate_isTorsion
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Monoid.IsTorsion
      (fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  let S :
      Set (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
    Set.range
        (fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I)
  intro x
  -- Work in the ambient commutative quotient group and close under multiplication and inversion.
  refine Submonoid.isOfFinOrder_coe.2 ?_
  have hx :
      ((x : fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :
        kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) ∈
        Subgroup.closure S := by
    simpa [S, fixed_constituent_projective_extension_candidate_subgroup] using x.property
  refine Subgroup.closure_induction (k := S) ?_ IsOfFinOrder.one ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨s, rfl⟩
      exact
        fixed_constituent_section_determinant_class_isOfFinOrder
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
    · rcases hy with ⟨c, rfl⟩
      exact
        fixed_constituent_determinant_subgroup_residue_class_isOfFinOrder
          (A := A) (G := G) (I := I) ρA_I c
  · intro y z _ _ hy hz
    -- The ambient quotient is commutative, so the product of torsion elements is torsion.
    exact hy.mul hz
  · intro y _ hy
    -- Inverting a torsion element keeps the same finite order.
    simpa using hy.inv

/-- Helper for Theorem 17-17.6-1: the explicit candidate subgroup in the residue-field quotient is
already finite, because it is a finitely generated torsion subgroup of a commutative group. This
closes the finiteness half of LinearRepresentations_Serre_1977's determinant-normalization stage before cyclicity is imposed.
-/
private theorem fixed_constituent_projective_extension_candidate_finite
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Finite
      (fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  let S :
      Set (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
    Set.range
        (fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I)
  have hSfinite : S.Finite := by
    -- Both generator families are finite because their source types `G` and `C` are finite.
    refine Set.Finite.union ?_ ?_
    · exact Set.finite_range
    · exact Set.finite_range
  letI : Finite S := Finite.to_subtype hSfinite
  letI : Group.FG (Subgroup.closure S) := Group.closure_finite_fg S
  -- A finitely generated torsion subgroup of an abelian group is finite.
  simpa [S, fixed_constituent_projective_extension_candidate_subgroup] using
    CommGroup.finite_of_fg_torsion
      (G :=
        fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
      (fixed_constituent_projective_extension_candidate_isTorsion
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: once LinearRepresentations_Serre_1977's determinant normalization produces an actual
finite subgroup `D ≤ kˣ`, cyclicity is automatic because `D` embeds in the multiplicative group of
the residue field. This isolates the later cyclicity step from the current quotient-to-upstairs
lifting blocker. -/
private theorem finite_subgroup_of_residue_units_isCyclic
    (D : Subgroup kˣ) [Finite D] :
    IsCyclic D := by
  let φ : D →* k where
    toFun z := ((z : kˣ) : k)
    map_one' := rfl
    map_mul' _ _ := rfl
  have hφ_injective : Function.Injective φ := by
    -- Equality in the residue field determines equality of the corresponding units.
    intro x y hxy
    apply Subtype.ext
    exact Units.ext hxy
  -- Any finite subgroup of the multiplicative group of a domain is cyclic.
  exact isCyclic_of_injective_ringHom φ hφ_injective

/-- Helper for Theorem 17-17.6-1: in characteristic `p`, the only `p`-th root of unity in the
residue field is `1`. This is the local reduced-ring input behind the prime-to-`p` cardinal bound
for LinearRepresentations_Serre_1977's canonical bounded-exponent subgroup `D`. -/
private theorem roots_of_unity_prime_eq_bot
    (hp : Nat.Prime p) :
    rootsOfUnity p k = ⊥ := by
  ext ζ
  constructor
  · intro hζ
    -- In characteristic `p`, `ζ ^ p = 1` is equivalent to `ζ ^ 1 = 1`.
    have hζ_one : ζ ∈ rootsOfUnity 1 k := by
      simpa using
        (mem_rootsOfUnity_prime_pow_mul_iff (R := k) p 1 1 (ζ := ζ)).1 (by simpa using hζ)
    simpa [rootsOfUnity_one] using hζ_one
  · intro hζ
    simpa [Subgroup.mem_bot] using hζ

/-- Helper for Theorem 17-17.6-1: the canonical subgroup of `n`-th roots of unity in the residue
field has order prime to `p`. This is LinearRepresentations_Serre_1977's closing prime-to-`p` control once the determinant
classes are placed inside a bounded-exponent subgroup `D := rootsOfUnity n k`. -/
private theorem roots_of_unity_card_coprime_charP
    (hp : Nat.Prime p)
    (n : ℕ) :
    Nat.Coprime p (Nat.card (rootsOfUnity n k)) := by
  by_contra hcop
  have hdiv :
      p ∣ Nat.card (rootsOfUnity n k) := by
    rcases hp.not_coprime_iff_dvd.mp hcop with ⟨q, hqprime, hqp, hqcard⟩
    have hq_eq : q = p := hp.dvd_iff_eq.mp hqp
    simpa [hq_eq] using hqcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPcard⟩ :=
    exists_subgroup_card_pow_prime (G := rootsOfUnity n k) p (n := 1) (by simpa using hdiv)
  have hP_bot : P = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.2
      apply Subtype.ext
      -- Any element of a subgroup of order `p` is a `p`-th root of unity, hence trivial.
      have hxpow :
          (((x : rootsOfUnity n k) : kˣ) ^ Nat.card P) = 1 := by
        simpa using
          congrArg (fun y : P => (((y : rootsOfUnity n k) : kˣ)))
            (pow_card_eq_one' (x := (⟨x, hx⟩ : P)))
      have hxroot :
          ((x : rootsOfUnity n k) : kˣ) ∈ rootsOfUnity p k := by
        exact (mem_rootsOfUnity p ((x : rootsOfUnity n k : kˣ))).2 (by simpa [hPcard] using hxpow)
      exact Subgroup.mem_bot.mp (by simpa [roots_of_unity_prime_eq_bot (A := A) hp] using hxroot)
    · exact bot_le
  have hcard_bot' : Nat.card P = 1 := by
    simpa [hP_bot] using (Subgroup.card_bot : Nat.card (⊥ : Subgroup (rootsOfUnity n k)) = 1)
  exact hp.ne_one (hPcard.trans hcard_bot')

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's finite-cover subgroup `G₂` is the closure of the chosen
section image together with the embedded Hall kernel inside the total-space cover `G₁`. Naming
this subgroup isolates the literal source generators before quotienting by `I₂`. -/
private noncomputable def fixed_constituent_generated_cover_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Subgroup
      (fixed_constituent_transport_total_space
        (A := A) (G := G) I ρA_I) :=
  Subgroup.closure
    (Set.range
        (fixed_constituent_transport_total_space_section
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_transport_total_space_embed_hall_kernel
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)))

/-- Helper for Theorem 17-17.6-1: every chosen section value lies in the generated-cover subgroup
`G₂`. This is the source-faithful surjectivity witness for the later quotient map `G₂ → G`. -/
private theorem fixed_constituent_section_mem_generated_cover
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The chosen section image is one of the literal generators used to define `G₂`.
  exact
    Subgroup.subset_closure <|
      Or.inl
        ⟨s, rfl⟩

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel copy lies in the generated-cover
subgroup `G₂`. This is the second source generator family in LinearRepresentations_Serre_1977's definition of `G₂`. -/
private theorem fixed_constituent_embed_hall_kernel_mem_generated_cover
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (x : I) :
    fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x ∈
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift := by
  -- The embedded Hall kernel is the other generator family in the defining closure of `G₂`.
  exact
    Subgroup.subset_closure <|
      Or.inr
        ⟨x, rfl⟩

/-- Helper for Theorem 17-17.6-1: restricting the total-space projection `G₁ → G` to the
generated-cover subgroup `G₂` is still surjective, because the chosen section values already lie
in `G₂`. This is the first structural fact needed before passing to `G₂ / I₂`. -/
private theorem fixed_constituent_generated_cover_proj_surjective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Surjective
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) := by
  intro s
  refine ⟨⟨_, ?_⟩, rfl⟩
  -- LinearRepresentations_Serre_1977's chosen section already lands in the generating family of `G₂`.
  exact
    fixed_constituent_section_mem_generated_cover
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: the literal Hall-kernel embedding `I → G₁` restricts to the
generated-cover subgroup `G₂`. This is the canonical source-faithful map used to define LinearRepresentations_Serre_1977's
subgroup `I₂ ≤ G₂`. -/
private noncomputable def fixed_constituent_generated_cover_embed_hall_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    I →*
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift :=
  MonoidHom.codRestrict
    (fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I))
    (fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fun x ↦
      fixed_constituent_embed_hall_kernel_mem_generated_cover
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel point inside `G₂` still projects to
the original Hall-kernel element in `G`. This fixes the projection formula before quotienting by
`I₂`. -/
@[simp] private theorem fixed_constituent_generated_cover_proj_apply_embed_hall_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (x : I) :
    ((fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      (fixed_constituent_generated_cover_embed_hall_kernel
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
      x := by
  -- The codomain restriction to `G₂` leaves the original Hall-kernel embedding unchanged.
  rfl

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's subgroup `I₂ ≤ G₂` is the range of the embedded
Hall-kernel copy. Naming it now isolates the first quotient object in the finite-cover package. -/
private noncomputable def fixed_constituent_generated_cover_hall_kernel_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Subgroup
      (fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :=
  (fixed_constituent_generated_cover_embed_hall_kernel
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).range

/-- Helper for Theorem 17-17.6-1: after restricting LinearRepresentations_Serre_1977's total-space projection to `G₂`,
quotienting by `I` on the `G`-side yields the source map `G₂ → G ⧸ I` used before introducing
the kernel `N̄`. -/
private noncomputable def fixed_constituent_generated_cover_proj_to_quotient
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift →*
      G ⧸ I :=
  (QuotientGroup.mk' I).comp
    ((fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))

/-- Helper for Theorem 17-17.6-1: the restricted projection `G₂ → G` is still surjective after
passing to `G ⧸ I`, so LinearRepresentations_Serre_1977's literal map `G₂ → G ⧸ I` already hits every quotient class. -/
private theorem fixed_constituent_generated_cover_proj_to_quotient_surjective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Surjective
      (fixed_constituent_generated_cover_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective I q
  obtain ⟨g2, rfl⟩ :=
    fixed_constituent_generated_cover_proj_surjective
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift g
  -- Surjectivity survives after composing with the quotient map `G → G ⧸ I`.
  rfl

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel copy `I₂` lies in the kernel of the
literal quotient projection `G₂ → G ⧸ I`. This is the first concrete kernel containment in the
`G₂ / I₂ / N̄` package. -/
private theorem fixed_constituent_generated_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
      (fixed_constituent_generated_cover_proj_to_quotient
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker := by
  intro g hg
  rcases hg with ⟨x, rfl⟩
  -- An embedded Hall-kernel element projects to the trivial class in `G ⧸ I`.
  simp [fixed_constituent_generated_cover_hall_kernel_subgroup,
    fixed_constituent_generated_cover_proj_to_quotient]

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal quotient map `G₂ → G ⧸ I` descends through the
embedded Hall-kernel subgroup `I₂`, yielding the source-faithful map `pi₂ : G₂ ⧸ I₂ → G ⧸ I`
that defines the later kernel `N̄`. -/
private noncomputable def generated_cover_proj_to_quotient_descends
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ⧸
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) →*
      G ⧸ I :=
  -- Route correction: freeze the first quotient object exactly as in LinearRepresentations_Serre_1977's source before any
  -- determinant normalization. The only input here is the already proved containment
  -- `I₂ ≤ ker(G₂ → G ⧸ I)`.
  QuotientGroup.lift
    (fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fixed_constituent_generated_cover_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (fixed_constituent_generated_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)

/-- Helper for Theorem 17-17.6-1: the descended quotient map `pi₂ : G₂ ⧸ I₂ → G ⧸ I` is
surjective, because the unreduced map `G₂ → G ⧸ I` was already surjective before quotienting by
`I₂`. -/
private theorem generated_cover_proj_to_quotient_descends_surjective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Surjective
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  intro q
  obtain ⟨g2, hg2⟩ :=
    fixed_constituent_generated_cover_proj_to_quotient_surjective
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  -- Choose any preimage in `G₂`; its class in `G₂ ⧸ I₂` maps to the same quotient element.
  refine
    ⟨QuotientGroup.mk'
        (fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        g2, ?_⟩
  simpa [generated_cover_proj_to_quotient_descends] using hg2

/-- Helper for Theorem 17-17.6-1: once the first quotient map `pi₂ : G₂ ⧸ I₂ → G ⧸ I` is fixed,
the quotient by its kernel is formally identified with `G ⧸ I`. This closes the purely
quotient-theoretic half of LinearRepresentations_Serre_1977's `G₂ / I₂ / N̄` package before any kernel normalization. -/
private noncomputable def generated_cover_kernel_quotient_equiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (((fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ⧸
        fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ⧸
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) ≃*
      (G ⧸ I) := by
  let pi2 :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hpi2_surj : Function.Surjective pi2 := by
    -- The descended map inherits surjectivity from the source map `G₂ → G ⧸ I`.
    exact
      generated_cover_proj_to_quotient_descends_surjective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hrange : pi2.range = ⊤ := by
    -- Surjectivity rewrites the range to `⊤`, so the standard quotient-kernel theorem applies.
    exact MonoidHom.range_eq_top.2 hpi2_surj
  -- This is the formal quotient step `((G₂ / I₂) / ker pi₂) ≃ G / I`.
  exact
    (QuotientGroup.quotientKerEquivRange pi2).trans
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv)

/-- Helper for Theorem 17-17.6-1: the actual kernel of `pi : G₂ → G` is identified with
LinearRepresentations_Serre_1977's quotient kernel `N̄ = ker(pi₂)` by sending a quotient-kernel class to its unique
normalized representative over `1 ∈ G`. This is the exact interface bridge needed later when the
tensor lift is descended from `G₂` back to `G`. -/
private noncomputable def generated_cover_kernel_equiv_nbar
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    pi.ker ≃* Nbar := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let toNbar : pi.ker →* Nbar :=
    { toFun := fun g ↦
        ⟨QuotientGroup.mk' I2 g.1, by
          -- Passing to `G ⧸ I` kills elements of `ker(pi)` on the nose.
          change
            generated_cover_proj_to_quotient_descends
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
                (QuotientGroup.mk' I2 g.1) = 1
          simpa [G2, I2, pi2, pi, generated_cover_proj_to_quotient_descends,
            fixed_constituent_generated_cover_proj_to_quotient] using
            congrArg (QuotientGroup.mk' I) g.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        simp }
  let fromNbar : Nbar →* pi.ker :=
    { toFun := fun q ↦
        ⟨normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q,
          normalized_kernel_representative_proj_eq_one
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
      map_one' := by
        apply Subtype.ext
        simpa [G2, I2, pi2, Nbar, pi] using
          normalized_kernel_representative_one
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      map_mul' := by
        intro q₁ q₂
        apply Subtype.ext
        simpa [G2, I2, pi2, Nbar, pi] using
          normalized_kernel_representative_mul
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ q₂ }
  refine
    { toFun := toNbar
      invFun := fromNbar
      left_inv := ?_
      right_inv := ?_
      map_mul' := toNbar.map_mul }
  · intro g
    apply Subtype.ext
    -- The normalized representative of the class of an actual kernel element is that element
    -- itself, by uniqueness in the literal `pi = 1` fiber.
    simpa [G2, I2, pi2, Nbar, pi] using
      normalized_kernel_representative_unique
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (toNbar g)
        (normalized_kernel_representative_mk_eq
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (toNbar g))
        rfl
        (normalized_kernel_representative_proj_eq_one
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (toNbar g))
        g.2
  · intro q
    apply Subtype.ext
    -- Quotienting the normalized representative recovers the original class in `N̄`.
    simpa [G2, I2, pi2, Nbar, pi] using
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: every element of `N̄ = ker(pi₂)` admits a representative in
`G₂` whose projection to `G` lies in `I`, and dividing by that embedded Hall-kernel point
produces a representative lying over `1`. This isolates the source-faithful normalization step
before defining any scalar-class invariant on `N̄`. -/
private theorem generated_cover_kernel_normalized_representative_exists
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
    (g :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    (hg :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g =
        q.1) :
    ∃ x : I,
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g =
        x ∧
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
        1 ∧
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
        q.1 := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  have hpi_mem :
      QuotientGroup.mk' I (pi g) = 1 := by
    -- Rewrite the kernel condition through the explicit descended map `pi₂`.
    simpa [G2, I2, pi, generated_cover_proj_to_quotient_descends,
      fixed_constituent_generated_cover_proj_to_quotient, hg] using q.2
  let x : I := ⟨pi g, (QuotientGroup.eq_one_iff (pi g)).mp hpi_mem⟩
  refine ⟨x, rfl, ?_⟩
  constructor
  · -- After dividing by the embedded Hall-kernel point over `pi g`, the corrected
    -- representative lands in the fiber over `1`.
    dsimp [pi, x]
    simp [map_mul]
  · -- The Hall-kernel correction does not change the class in `G₂ ⧸ I₂`.
    have hmk_embed :
        QuotientGroup.mk' I2
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) =
          1 := by
      exact (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
    calc
      QuotientGroup.mk' I2
          (g *
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
        QuotientGroup.mk' I2 g *
          (QuotientGroup.mk' I2
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x))⁻¹ := by
            simp
      _ = QuotientGroup.mk' I2 g := by simp [hmk_embed]
      _ = q.1 := hg

/-- Helper for Theorem 17-17.6-1: once the candidate determinant subgroup is placed inside the
bounded roots-of-unity owner `D̄`, the remaining work is the literal LinearRepresentations_Serre_1977 package
`G₂`, `I₂`, `N̄`, `τ`, and tensor descent. This keeps the final blocker separate from the already
formalized closure step. -/
private theorem generated_cover_kernel_has_normalized_representative
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∀ g :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift,
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g =
        q.1 →
        ∃ x : I,
          ((fixed_constituent_transport_total_space_proj_hom
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
            (Subgroup.subtype
              (fixed_constituent_generated_cover_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g =
            x ∧
          ((fixed_constituent_transport_total_space_proj_hom
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
            (Subgroup.subtype
              (fixed_constituent_generated_cover_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
              (g *
                (fixed_constituent_generated_cover_embed_hall_kernel
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
            1 ∧
          QuotientGroup.mk'
              (fixed_constituent_generated_cover_hall_kernel_subgroup
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
              (g *
                (fixed_constituent_generated_cover_embed_hall_kernel
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x)⁻¹) =
            q.1 := by
  intro g hg
  -- Delegate the normalization to the explicit representative-level lemma above.
  exact
    generated_cover_kernel_normalized_representative_exists
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q g hg

/-- Helper for Theorem 17-17.6-1: for a fixed class `q ∈ N̄ = ker(pi₂)`, the representative in
`G₂` lying over `1 ∈ G` is unique. This is the structural step in LinearRepresentations_Serre_1977's source route that makes
the later scalar unit attached to `q` independent of choices. -/
private theorem normalized_kernel_representative_unique
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
    {g₁ g₂ :
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift}
    (hg₁ :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g₁ =
        q.1)
    (hg₂ :
      QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
          g₂ =
        q.1)
    (hg₁_one :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g₁ =
        1)
    (hg₂_one :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))) g₂ =
        1) :
    g₁ = g₂ := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  have hclass :
      QuotientGroup.mk' I2 g₂ = QuotientGroup.mk' I2 g₁ := by
    exact hg₂.trans hg₁.symm
  have hdiv_mem : g₂ / g₁ ∈ I2 := by
    -- Equal quotient classes differ by an element of the embedded Hall kernel.
    exact (QuotientGroup.eq_iff_div_mem).mp hclass
  rcases
      (show g₂ / g₁ ∈
          (fixed_constituent_generated_cover_embed_hall_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).range by
        simpa [I2] using hdiv_mem) with ⟨x, hx⟩
  have hx_one : x = 1 := by
    apply Subtype.ext
    -- Applying `pi` identifies the Hall-kernel witness with the trivial element of `I`.
    have hpi_div : pi (g₂ / g₁) = 1 := by
      simp [pi, hg₁_one, hg₂_one]
    calc
      (x : G) =
          pi
            (fixed_constituent_generated_cover_embed_hall_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x) := by
            simp [pi]
      _ = pi (g₂ / g₁) := by simpa [hx]
      _ = 1 := hpi_div
  have hdiv_one : g₂ / g₁ = 1 := by
    -- Once that Hall-kernel witness is trivial, the two normalized representatives coincide.
    calc
      g₂ / g₁ =
          fixed_constituent_generated_cover_embed_hall_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x := by
              simpa using hx.symm
      _ =
          fixed_constituent_generated_cover_embed_hall_kernel
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift 1 := by
              rw [hx_one]
      _ = 1 := by simp
  exact (div_eq_one.mp hdiv_one).symm

/-- Helper for Theorem 17-17.6-1: the quotient-out representative of a kernel class in `N̄`
already represents that class in `G₂ ⧸ I₂`. This lets the later normalized representative be
defined as literal data rather than by carrying witnesses through the main package proof. -/
private theorem normalized_kernel_out_represents_class
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        (fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        q.1.out =
      q.1 := by
  -- This is the canonical quotient representative used in the normalized kernel package.
  simpa using QuotientGroup.out_eq' q.1

/-- Helper for Theorem 17-17.6-1: choose the Hall-kernel correction that moves the quotient-out
representative of `q ∈ N̄` into the fiber over `1 ∈ G`. -/
private noncomputable def normalized_kernel_representative_correction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    I :=
  Classical.choose <|
    generated_cover_kernel_has_normalized_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
      (normalized_kernel_out_represents_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)

/-- Helper for Theorem 17-17.6-1: the Hall-kernel correction chosen to normalize `q.1.out`
is exactly the projection of that quotient-out representative to `I`. This isolates the
source-faithful same-fiber comparison used later when the raw representative is divided by its
Hall-kernel correction. -/
private theorem normalized_kernel_representative_correction_val_eq_out_proj
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    (normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q : G) =
      pi q.1.out := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- Read off the first component of the chosen normalization witness.
  simpa [G2, pi, normalized_kernel_representative_correction] using hspec.1.symm

/-- Helper for Theorem 17-17.6-1: choose the unique normalized representative of a kernel class
`q ∈ N̄`, i.e. the literal element of `G₂` representing `q` whose projection to `G` is `1`. -/
private noncomputable def normalized_kernel_representative
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift :=
  q.1.out *
    (fixed_constituent_generated_cover_embed_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      (normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))⁻¹

/-- Helper for Theorem 17-17.6-1: the chosen normalized representative lies over `1 ∈ G`. This
is the exact source normalization needed before extracting a scalar from the `U₁ = Aˣ` fiber. -/
private theorem normalized_kernel_representative_proj_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ((fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype
        (fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
      1 := by
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- Read off the second component of the normalization witness for the chosen correction.
  simpa [normalized_kernel_representative, normalized_kernel_representative_correction] using
    hspec.2.1

/-- Helper for Theorem 17-17.6-1: the chosen normalized representative still represents the
original class `q ∈ N̄` in `G₂ ⧸ I₂`. -/
private theorem normalized_kernel_representative_mk_eq
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        (fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
      q.1 := by
  have hspec :=
    Classical.choose_spec <|
      generated_cover_kernel_has_normalized_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q q.1.out
        (normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
  -- The Hall-kernel correction does not change the quotient class.
  simpa [normalized_kernel_representative, normalized_kernel_representative_correction] using
    hspec.2.2

/-- Helper for Theorem 17-17.6-1: the fiber coordinate of the normalized representative lies in
LinearRepresentations_Serre_1977's kernel fiber `U₁ = Aˣ`, so the existing scalar-classification theorem already produces a
unit homothety for it. This is the first scalar bridge needed for the later kernel package on
`N̄`. -/
private theorem normalized_kernel_scalar_exists
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ a : Aˣ,
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The fixed lifted constituent already satisfies the scalar endomorphism theorem.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar f
  have hrep_one :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.1 =
      1 := by
    -- Rewrite the normalized projection statement as an equality of the first coordinates.
    change
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
        1
    exact
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let u1 :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G) := by
    -- The chosen normalized representative now lives in the literal kernel fiber `U₁`.
    simpa [hrep_one] using
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  -- Apply the existing `U₁ = Aˣ` theorem to this normalized representative.
  simpa [u1] using
    fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
      (A := A) (G := G) (I := I) ρA_I hscalar u1

/-- Helper for Theorem 17-17.6-1: on a nontrivial free finite module, a scalar homothety is
determined by its underlying linear equivalence. This is the uniqueness bridge needed when the
normalized kernel representative is rewritten as a scalar unit. -/
private theorem unit_smul_linearEquiv_refl_injective
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] [Nontrivial M]
    {a b : Aˣ}
    (h : (a • LinearEquiv.refl A M : M ≃ₗ[A] M) = b • LinearEquiv.refl A M) :
    a = b := by
  let basis := Module.finBasis A M
  have hfinrank_pos : 0 < Module.finrank A M :=
    (Module.finrank_pos_iff_of_free (R := A) (M := M)).2 inferInstance
  have hidx : Nonempty (Fin (Module.finrank A M)) :=
    Fin.pos_iff_nonempty.mp hfinrank_pos
  let i : Fin (Module.finrank A M) := Classical.choice hidx
  -- Evaluate the two homotheties on one basis vector and read off its `i`-th coordinate.
  have hcoord :
      basis.repr (((a • LinearEquiv.refl A M : M ≃ₗ[A] M) (basis i))) i =
        basis.repr (((b • LinearEquiv.refl A M : M ≃ₗ[A] M) (basis i))) i := by
    exact congrArg (fun x ↦ basis.repr x i) (LinearEquiv.congr_fun h (basis i))
  have hab : (a : A) = (b : A) := by
    simpa [basis, smul_eq_mul] using hcoord
  exact Units.ext hab

/-- Helper for Theorem 17-17.6-1: the normalized representative of the identity kernel class is
the identity element of `G₂`. This pins down the base point before the scalar map is assembled. -/
private theorem normalized_kernel_representative_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift 1 =
      1 := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 :
      G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let q : pi2.ker := 1
  have hclass_one : QuotientGroup.mk' I2 (1 : G2) = q.1 := by
    simp [q]
  have hproj_one :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)) (1 : G2) = 1 := by
    simp [G2]
  -- Both elements represent the same quotient class and lie in the normalized `pi = 1` fiber.
  simpa [G2, I2, pi2, q] using
    normalized_kernel_representative_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
      (normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
      hclass_one
      (normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)
      hproj_one

/-- Helper for Theorem 17-17.6-1: normalized representatives multiply exactly as their classes in
`N̄ = ker(pi₂)`. This is the structural pivot that makes the later scalar assignment multiplicative
without reopening the Hall-kernel correction bookkeeping. -/
private theorem normalized_kernel_representative_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q₁ q₂ :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂) =
      normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
        normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂ := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hclass_mul :
      QuotientGroup.mk' I2
          (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
            normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂) =
        (q₁ * q₂).1 := by
    -- Pass to `G₂ ⧸ I₂`; there the normalized representatives already agree with their classes.
    calc
      QuotientGroup.mk' I2
          (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
            normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂) =
          QuotientGroup.mk' I2
              (normalized_kernel_representative
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁) *
            QuotientGroup.mk' I2
              (normalized_kernel_representative
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂) := by
            simp
      _ = q₁.1 * q₂.1 := by
            rw [normalized_kernel_representative_mk_eq
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁,
              normalized_kernel_representative_mk_eq
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂]
      _ = (q₁ * q₂).1 := rfl
  have hproj_mul :
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2))
        (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ *
          normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂) =
        1 := by
    -- The normalized representatives already lie in the `pi = 1` fiber, so their product does as
    -- well.
    simp [G2,
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁,
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂]
  -- Uniqueness in the normalized fiber identifies the representative of `q₁ * q₂` with that
  -- product.
  simpa [G2, I2] using
    normalized_kernel_representative_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)
      (normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂))
      hclass_mul
      (normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂))
      hproj_mul

/-- Helper for Theorem 17-17.6-1: after normalizing representatives inside `N̄ = ker(pi₂)`,
their second coordinates compose exactly as LinearRepresentations_Serre_1977's total-space multiplication says they should.
This is the transport-stable bridge from representative multiplication to scalar multiplication on
the fixed lifted constituent carrier. -/
private theorem normalized_kernel_second_coordinate_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q₁ q₂ :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)).1.2
        .toLinearEquiv =
      ((normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2
          .toLinearEquiv).trans
        ((normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2
          .toLinearEquiv) := by
  -- Read off the second coordinate from representative multiplication, then unfold LinearRepresentations_Serre_1977's
  -- total-space product only once so the composition order stays source-faithful.
  have hmul :=
    congrArg
      (fun g ↦ g.1.2.toLinearEquiv)
      (normalized_kernel_representative_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ q₂)
  simpa [fixed_constituent_transport_total_space_mul, fixed_constituent_transport_fiber_comp] using
    hmul

/-- Helper for Theorem 17-17.6-1: the scalar unit attached to a normalized kernel representative
is unique once the lift carrier is known to have positive rank. This is the bridge from
representative-level uniqueness to the later monoid-hom construction on `N̄`. -/
private theorem normalized_kernel_scalar_unique
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker)
    {a b : Aˣ}
    (ha :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        a • LinearEquiv.refl A P_S)
    (hb :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
        b • LinearEquiv.refl A P_S) :
    a = b := by
  have hdimcop :
      Nat.Coprime p (Module.finrank A P_S) :=
    fixed_constituent_lift_finrank_coprime
      (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hfinrank_ne_zero : Module.finrank A P_S ≠ 0 := by
    intro hzero
    have hdvd : p ∣ Module.finrank A P_S := by
      simpa [hzero] using dvd_zero p
    exact (hp.coprime_iff_not_dvd.mp hdimcop) hdvd
  have hfinrank_pos : 0 < Module.finrank A P_S :=
    Nat.pos_of_ne_zero hfinrank_ne_zero
  letI : Nontrivial P_S := Module.nontrivial_of_finrank_pos (R := A) hfinrank_pos
  -- Once the two scalar homotheties are identified as the same transport operator, the unit is
  -- forced.
  exact
    unit_smul_linearEquiv_refl_injective
      (A := A) (M := P_S) (ha.symm.trans hb)

/-- Helper for Theorem 17-17.6-1: scalar homotheties on a free module compose by multiplying the
underlying units. This is the linear-algebra normalization needed when LinearRepresentations_Serre_1977's kernel
representatives are multiplied upstairs in `G₂`. -/
private theorem unit_smul_linearEquiv_refl_trans
    {M : Type*} [AddCommGroup M] [Module A M]
    (a b : Aˣ) :
    (a • LinearEquiv.refl A M).trans (b • LinearEquiv.refl A M) =
      (a * b) • LinearEquiv.refl A M := by
  -- Both sides act on each vector by the same scalar multiplication.
  ext x
  simp [smul_smul, mul_assoc]

/-- Helper for Theorem 17-17.6-1: the scalar extracted from the normalized representative of
`q ∈ N̄` is multiplicative. This packages LinearRepresentations_Serre_1977's kernel object `U₁ = Aˣ` as an actual monoid
homomorphism on `N̄`, ready for the later residue-class comparison. -/
private noncomputable def kernel_scalar_unit
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker →* Aˣ where
  toFun q :=
    Classical.choose
      (normalized_kernel_scalar_exists
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)
  map_one' := by
    let q_one :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker := 1
    let a_one : Aˣ :=
      Classical.choose
        (normalized_kernel_scalar_exists
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q_one)
    change a_one = 1
    have ha_one :
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q_one).1.2
          .toLinearEquiv =
        a_one • LinearEquiv.refl A P_S := by
      -- The chosen scalar for the identity class is read directly from the normalization witness.
      simpa [a_one] using
        (Classical.choose_spec
          (normalized_kernel_scalar_exists
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q_one))
    have h_one_repr :
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q_one).1.2
          .toLinearEquiv =
        (1 : Aˣ) • LinearEquiv.refl A P_S := by
      -- The normalized representative of `1 ∈ N̄` is literally the identity element of `G₂`.
      simpa using
        congrArg
          (fun g ↦ g.1.2.toLinearEquiv)
          (normalized_kernel_representative_one
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
    exact
      normalized_kernel_scalar_unique
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q_one
        ha_one h_one_repr
  map_mul' q₁ q₂ := by
    let a₁ : Aˣ :=
      Classical.choose
        (normalized_kernel_scalar_exists
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁)
    let a₂ : Aˣ :=
      Classical.choose
        (normalized_kernel_scalar_exists
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂)
    let a₁₂ : Aˣ :=
      Classical.choose
        (normalized_kernel_scalar_exists
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (q₁ * q₂))
    change a₁₂ = a₁ * a₂
    have ha₁ :
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2
          .toLinearEquiv =
        a₁ • LinearEquiv.refl A P_S := by
      -- The chosen scalar for `q₁` is read directly from its normalized representative.
      simpa [a₁] using
        (Classical.choose_spec
          (normalized_kernel_scalar_exists
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁))
    have ha₂ :
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2
          .toLinearEquiv =
        a₂ • LinearEquiv.refl A P_S := by
      -- The same scalar extraction is used for `q₂`.
      simpa [a₂] using
        (Classical.choose_spec
          (normalized_kernel_scalar_exists
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂))
    have ha₁₂ :
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)).1.2
          .toLinearEquiv =
        a₁₂ • LinearEquiv.refl A P_S := by
      -- This is the chosen scalar on the product class.
      simpa [a₁₂] using
        (Classical.choose_spec
          (normalized_kernel_scalar_exists
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            (q₁ * q₂)))
    exact
      normalized_kernel_scalar_unique
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)
        ha₁₂
        (by
          -- Route correction: normalize the second coordinate first, then compare two scalar
          -- homotheties on `P_S`; this avoids reopening the quotient transport bookkeeping.
          calc
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (q₁ * q₂)).1.2
                .toLinearEquiv =
              ((normalized_kernel_representative
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2
                  .toLinearEquiv).trans
                ((normalized_kernel_representative
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2
                  .toLinearEquiv) := by
                    exact
                      normalized_kernel_second_coordinate_mul
                        (p := p) (A := A) (G := G) (V := V)
                        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ q₂
            _ = (a₂ • LinearEquiv.refl A P_S).trans (a₁ • LinearEquiv.refl A P_S) := by
                  rw [ha₂, ha₁]
            _ = (a₂ * a₁) • LinearEquiv.refl A P_S := by
                  exact unit_smul_linearEquiv_refl_trans (A := A) (M := P_S) a₂ a₁
            _ = (a₁ * a₂) • LinearEquiv.refl A P_S := by
                  simp [mul_comm])

/-- Helper for Theorem 17-17.6-1: the monoid hom `kernel_scalar_unit` records the actual scalar
chosen for each normalized representative of `q ∈ N̄`. This keeps later residue-class arguments
from reopening the underlying `Classical.choose` witness. -/
private theorem kernel_scalar_unit_spec
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2.toLinearEquiv =
      kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q •
        LinearEquiv.refl A P_S := by
  -- The chosen scalar is definitionally the witness returned by `normalized_kernel_scalar_exists`.
  simpa [kernel_scalar_unit] using
    (Classical.choose_spec
      (normalized_kernel_scalar_exists
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q))

/-- Helper for Theorem 17-17.6-1: once the candidate determinant subgroup is placed inside the
bounded roots-of-unity owner `D̄`, the remaining work is the literal LinearRepresentations_Serre_1977 package
`G₂`, `I₂`, `N̄`, `τ`, and tensor descent. This keeps the final blocker separate from the already
formalized closure step. -/
private theorem candidate_subgroup_cyclic_and_coprime_of_bounded_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    IsCyclic
        (fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∧
      Nat.Coprime p
        (Nat.card
          (fixed_constituent_projective_extension_candidate_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hroots_cyclic : IsCyclic (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k) := by
    -- The bounded roots-of-unity group sits inside the residue-field units, so it is cyclic.
    exact finite_subgroup_of_residue_units_isCyclic (A := A)
      (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k)
  have hDbar_cyclic : IsCyclic Dbar := by
    -- LinearRepresentations_Serre_1977's bounded owner `D̄` is a quotient image of that cyclic roots-of-unity group.
    dsimp [Dbar]
    exact
      isCyclic_of_surjective
        ((QuotientGroup.mk' Qd).subgroupMap (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k))
        ((QuotientGroup.mk' Qd).subgroupMap_surjective
          (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k))
  have hDbar_coprime :
      Nat.Coprime p (Nat.card Dbar) := by
    -- The image `D̄` still has prime-to-`p` cardinal because its size divides the roots-of-unity
    -- owner cardinal.
    exact
      (roots_of_unity_card_coprime_charP (A := A) hp (Nat.lcm (Nat.card G) (Nat.card C))).of_dvd_right
        (Subgroup.card_map_dvd
          (QuotientGroup.mk' Qd)
          (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k))
  constructor
  · -- Once the determinant candidate subgroup is known to sit inside the cyclic owner `D̄`,
    -- cyclicity descends to this subgroup.
    exact Subgroup.isCyclic_of_le (show Candidate ≤ Dbar by simpa [Candidate, C, Qd, Dbar] using hcandidate_le)
  · -- The same containment gives a cardinal divisibility, hence the same prime-to-`p` bound.
    exact hDbar_coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (show Candidate ≤ Dbar by simpa [Candidate, C, Qd, Dbar] using hcandidate_le))

/-- Helper for Theorem 17-17.6-1: every residue class coming from LinearRepresentations_Serre_1977's determinant subgroup
`C` has order dividing the cardinal of the explicit candidate subgroup. This freezes the
finite-order input needed before converting quotient-level determinant identities into literal
upstairs statements. -/
private theorem fixed_constituent_determinant_subgroup_residue_class_pow_card_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    (fixed_constituent_determinant_subgroup_residue_class
      (A := A) (G := G) (I := I) ρA_I c) ^ n = 1 := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Finite Candidate :=
    fixed_constituent_projective_extension_candidate_finite
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let z : Candidate :=
    ⟨fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c,
      fixed_constituent_determinant_subgroup_residue_class_mem_candidate
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift c⟩
  -- The determinant-subgroup image already lives in the finite candidate subgroup, so its
  -- `|Candidate|`-power is trivial.
  simpa [n, z] using congrArg Subtype.val (pow_card_eq_one' (x := z))

/-- Helper for Theorem 17-17.6-1: the raw determinant class of the quotient-out representative of
`q ∈ N̄` also has order dividing the cardinal of the candidate subgroup, because it agrees with
the literal Hall-kernel correction class in LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem kernel_out_representative_det_residue_class_pow_card_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    (QuotientGroup.mk' Qd
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2))) ^ n = 1 := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Finite Candidate :=
    fixed_constituent_projective_extension_candidate_finite
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨corrDet,
      normalized_kernel_representative_correction_det_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
  have hclass :
      QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c := by
    -- Replace the raw quotient-out determinant class by the literal Hall-kernel correction class.
    simpa [Qd, corrDet, c] using
      kernel_out_representative_det_residue_class_eq_correction_residue_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  -- Once the raw class is rewritten to a literal element of `C`, the same finite-order relation
  -- follows from the previous candidate-subgroup power lemma.
  calc
    (QuotientGroup.mk' Qd
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2))) ^ n =
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) ^ n := by
          exact congrArg (fun z ↦ z ^ n) hclass
    _ = 1 := by
          simpa [Candidate, n, c] using
            fixed_constituent_determinant_subgroup_residue_class_pow_card_eq_one
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift c

/-- Helper for Theorem 17-17.6-1: the normalized scalar attached to `q ∈ N̄` determines `q`
itself. This packages the already normalized representative-level uniqueness into an injective
map `N̄ → Aˣ`, leaving only the bounded-image step before LinearRepresentations_Serre_1977's cyclic prime-to-`p` kernel
package closes. -/
private theorem kernel_scalar_unit_injective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Injective
      (kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  intro q₁ q₂ hq
  have hscalar_eq :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2.toLinearEquiv =
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2.toLinearEquiv := by
    -- Compare the second coordinates after rewriting both normalized representatives by the same
    -- scalar homothety.
    calc
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.2.toLinearEquiv =
          kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₁ •
            LinearEquiv.refl A P_S := by
              simpa using
                kernel_scalar_unit_spec
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                  hTransportLift q₁
      _ =
          kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q₂ •
            LinearEquiv.refl A P_S := by
              rw [hq]
      _ =
          (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.2
              .toLinearEquiv := by
                simpa using
                  (kernel_scalar_unit_spec
                    (p := p) (A := A) (G := G) (V := V)
                    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                    hTransportLift q₂).symm
  have hproj₁ :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁).1.1 = 1 := by
    -- The normalized representative of each kernel class lies in the fiber over `1 ∈ G`.
    change
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁) =
        1
    exact
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁
  have hproj₂ :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂).1.1 = 1 := by
    -- The same normalization condition holds for `q₂`.
    change
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂) =
        1
    exact
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂
  have hrepr :
      normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁ =
      normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂ := by
    -- Once both first coordinates are normalized to `1`, equality of the transport operators
    -- forces equality in the total space.
    cases hproj₁
    cases hproj₂
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · exact Representation.Equiv.toLinearEquiv_injective hscalar_eq
  have hclass :
      q₁.1 = q₂.1 := by
    -- Pass the equality of normalized representatives back to the quotient `G₂ ⧸ I₂`.
    simpa [normalized_kernel_representative_mk_eq
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₁,
      normalized_kernel_representative_mk_eq
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q₂] using
      congrArg
        (QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift))
        hrepr
  exact Subtype.ext hclass

/-- Helper for Theorem 17-17.6-1: a scalar homothety on the fixed lifted constituent is an
element of LinearRepresentations_Serre_1977's kernel fiber `U₁`. This keeps the later centrality argument at the literal
total-space level instead of reopening the transport normalization data each time. -/
private theorem scalar_transport_fiber_one_isIntertwining
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ) :
    (ρA_I.comp (MulAut.conjNormal (1 : G)⁻¹).toMonoidHom).IsIntertwiningMap
      ρA_I
      (((a • LinearEquiv.refl A P_S : P_S ≃ₗ[A] P_S) : P_S →ₗ[A] P_S)) := by
  -- At `s = 1`, conjugation is trivial, so the scalar homothety commutes with the `I`-action.
  refine Representation.IsIntertwiningMap.mk ?_
  intro x
  ext v
  simp [MulAut.conjNormal_apply, mul_assoc]

/-- Helper for Theorem 17-17.6-1: package a scalar unit as the corresponding element of the
kernel fiber `U₁` in LinearRepresentations_Serre_1977's transport total space. -/
private noncomputable def scalar_transport_fiber_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) :=
  Representation.Equiv.mk
    (a • LinearEquiv.refl A P_S)
    (scalar_transport_fiber_one_isIntertwining
      (A := A) (G := G) (I := I) ρA_I a)

/-- Helper for Theorem 17-17.6-1: scalar elements in LinearRepresentations_Serre_1977's kernel fiber commute with every
element of the transport total space. This is the literal source-level reason that the later
kernel subgroup is central after quotienting by the embedded Hall kernel. -/
private theorem scalar_transport_total_space_commutes
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    fixed_constituent_transport_total_space_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ g =
      fixed_constituent_transport_total_space_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        g ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ := by
  rcases g with ⟨s, u⟩
  apply Sigma.ext
  · -- Both products have first coordinate `s`, because the scalar element lies over `1`.
    simp [fixed_constituent_transport_total_space_mul]
  · -- On the second coordinate, both composites act by `v ↦ a • u v`.
    apply Representation.Equiv.toLinearEquiv_injective
    ext v
    simp [fixed_constituent_transport_total_space_mul,
      fixed_constituent_transport_fiber_comp,
      scalar_transport_fiber_one,
      MulAut.conjNormal_apply, mul_assoc]

/-- Helper for Theorem 17-17.6-1: every normalized representative of a class in `N̄` is literally
the scalar point `(1, a • id)` in LinearRepresentations_Serre_1977's transport total space. This is the transport-stable
form of the scalar extraction used in the centrality argument. -/
private theorem normalized_kernel_representative_eq_scalar_total_space
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1 =
      ⟨1,
        scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I
          (kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)⟩ := by
  have hproj :
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.1 = 1 := by
    -- The chosen normalized representative already lies over `1 ∈ G`.
    change
      ((fixed_constituent_transport_total_space_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) =
        1
    exact
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  cases hproj
  apply Sigma.ext
  · rfl
  · -- The second coordinate is exactly the scalar fiber element attached to `kernelScalar q`.
    exact Representation.Equiv.toLinearEquiv_injective <| by
      simpa [scalar_transport_fiber_one] using
        kernel_scalar_unit_spec
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the second coordinate of the normalized representative is
already the scalar kernel-fiber element classified by `kernel_scalar_unit`. This keeps later
kernel calculations at the fiber level instead of reopening the total-space first coordinate. -/
private theorem normalized_kernel_representative_eq_scalar_fiber
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I
        (kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) := by
  -- Read the second coordinate directly from the scalar total-space normal form.
  exact congrArg Sigma.snd <|
    normalized_kernel_representative_eq_scalar_total_space
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: after rewriting a normalized kernel representative as the
literal scalar point `(1, a • id)`, its determinant is exactly `a^d`. This isolates the scalar
determinant computation before the remaining comparison with LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem normalized_kernel_representative_det_eq_kernel_scalar_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      kernel_scalar_unit
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q ^
        Module.finrank A P_S := by
  -- Route correction: the source kernel element over `1` is controlled by its literal scalar
  -- fiber coordinate, not by a separate principal-unit normalization.
  have hscalar_fiber :=
    normalized_kernel_representative_eq_scalar_fiber
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  rw [hscalar_fiber]
  -- The determinant of the scalar point in `U₁` is the expected `d`-th power.
  exact
    fixed_constituent_transport_kernel_det_eq_unit_pow
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) rfl

/-- Helper for Theorem 17-17.6-1: the determinant-membership goal for a normalized kernel
representative is exactly the source statement that the attached scalar `kernelScalar(q)` has
`d`-th power in LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem normalized_kernel_representative_det_mem_determinant_subgroup_iff_kernel_scalar_pow_mem
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I ↔
    kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q ^
      Module.finrank A P_S ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- Rewrite the normalized determinant to the literal scalar `d`-th power and stop there.
  rw [normalized_kernel_representative_det_eq_kernel_scalar_pow
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]

/-- Helper for Theorem 17-17.6-1: the determinant of the embedded Hall-kernel element attached to
`x ∈ I` is exactly the determinant generator used to define LinearRepresentations_Serre_1977's subgroup `C`. -/
private theorem fixed_constituent_transport_fiber_det_of_hall_kernel_element
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
      fixed_constituent_action_det (A := A) (G := G) I ρA_I x := rfl

/-- Helper for Theorem 17-17.6-1: the determinant contributed by the Hall-kernel correction used
to normalize a class `q ∈ N̄` already lies in LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem normalized_kernel_representative_correction_det_mem_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)) ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- The correction element is literally an element of `I`, and `C` is generated by these
  -- Hall-kernel action determinants.
  rw [fixed_constituent_transport_fiber_det_of_hall_kernel_element
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  exact
    Subgroup.subset_closure
      ⟨normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q, rfl⟩

/-- Helper for Theorem 17-17.6-1: when LinearRepresentations_Serre_1977's chosen section is evaluated on an element of the
Hall kernel `I`, its determinant class already agrees modulo `d`-th powers with the corresponding
generator from the determinant subgroup `C`. -/
private theorem section_determinant_class_eq_determinant_subgroup_residue_class_of_mem_I
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (x : I) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
          Subgroup.subset_closure ⟨x, rfl⟩⟩ := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The fixed lifted constituent still satisfies the scalar endomorphism property.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- LinearRepresentations_Serre_1977's kernel fiber `U₁` is exactly the scalar unit group.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (x : G)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)
  have hpow_one :
      QuotientGroup.mk' Qd ((Units.map (IsLocalRing.residue A) a) ^ d) = 1 := by
    -- Modding out by `d`-th powers kills the scalar discrepancy over the same `x ∈ I`.
    exact
      (QuotientGroup.eq_one_iff
        ((Units.map (IsLocalRing.residue A) a) ^ d)).2
        ⟨Units.map (IsLocalRing.residue A) a, rfl⟩
  -- Replace the chosen section point by the canonical Hall-kernel point in the same fiber.
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x =
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x).2))) := by
          rfl
    _ =
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) x))) := by
          rw [ha, Units.map_mul, MonoidHom.map_pow, map_mul, hpow_one, mul_one]
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
          Subgroup.subset_closure ⟨x, rfl⟩⟩ := by
          -- The Hall-kernel determinant is literally one of the generators of `C`.
          rw [fixed_constituent_determinant_subgroup_residue_class,
            fixed_constituent_transport_fiber_det_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)]

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's section determinant classes multiply in the quotient
`kˣ / (kˣ)^d`. This is the algebraic source-side owner behind the later quotient-by-`C` route:
the discrepancy between `sec (s * t)` and `sec s * sec t` lies in `U₁`, hence contributes only a
`d`-th power to the determinant class. -/
private theorem fixed_constituent_section_determinant_class_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s t : G) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t) =
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s *
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The scalar endomorphism theorem is the source input that identifies `U₁` with scalar
    -- homotheties.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- This upgrades the kernel fiber comparison `U₁` to literal scalar units.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  let secMul :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (s * t) :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 (sec t).2
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (s * t) secMul
  have hpow_one :
      QuotientGroup.mk' Qd ((Units.map (IsLocalRing.residue A) a) ^ d) = 1 := by
    -- Passing to the quotient by `d`-th powers kills the scalar correction between the two
    -- section choices in the fiber over `s * t`.
    exact
      (QuotientGroup.eq_one_iff
        ((Units.map (IsLocalRing.residue A) a) ^ d)).2
        ⟨Units.map (IsLocalRing.residue A) a, rfl⟩
  have hsecMul_class :
      QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) secMul)) =
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t) := by
    -- Replace the product section point by the chosen section at `s * t`; the discrepancy is the
    -- scalar `d`-th power from `ha`.
    rw [ha, Units.map_mul, MonoidHom.map_pow, map_mul, hpow_one, mul_one]
  -- Route correction: the section classes are now handled at the source level as a multiplicative
  -- determinant-class map, rather than only through later kernel representatives.
  calc
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t) =
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) secMul)) := by
          exact hsecMul_class.symm
    _ =
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t *
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s := by
            rw [fixed_constituent_transport_fiber_det_comp]
            simp [fixed_constituent_section_determinant_class, sec, map_mul]
    _ =
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s *
        fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t := by
            rw [mul_comm]

/-- Helper for Theorem 17-17.6-1: the section determinant class at `1` is the neutral element of
`kˣ / (kˣ)^d`. Together with multiplicativity, this packages LinearRepresentations_Serre_1977's chosen section determinants
as a genuine monoid morphism before quotienting by the determinant subgroup image. -/
private theorem fixed_constituent_section_determinant_class_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (1 : G) =
      1 := by
  let c :=
    fixed_constituent_section_determinant_class
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (1 : G)
  have hmul :
      c = c * c := by
    simpa [c] using
      fixed_constituent_section_determinant_class_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G) (1 : G)
  have hcancel := congrArg (fun z ↦ z * c⁻¹) hmul
  simpa [mul_assoc] using hcancel

/-- Helper for Theorem 17-17.6-1: the chosen section determinants define a multiplicative map
`G → kˣ / (kˣ)^d`. This freezes the source-side algebra needed for the literal-cover pivot before
passing to the quotient by the determinant subgroup image. -/
private noncomputable def fixed_constituent_section_determinant_class_hom
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G →* (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) where
  toFun :=
    fixed_constituent_section_determinant_class
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  map_one' := by
    -- The source-faithful section is normalized to a genuine unit-valued class map at `1`.
    exact
      fixed_constituent_section_determinant_class_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  map_mul' s t := by
    -- Multiplicativity is exactly the determinant comparison between `sec (s * t)` and
    -- `sec s * sec t` modulo `d`-th powers.
    exact
      fixed_constituent_section_determinant_class_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s t

/-- Helper for Theorem 17-17.6-1: the quotient-out representative `q.1.out` of a class
`q ∈ N̄ = ker(pi₂)` already contributes no new determinant class modulo `d`-th powers; its class
comes from LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem kernel_out_representative_det_residue_class_mem_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ c :
        fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I,
      QuotientGroup.mk'
          ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  have hpi_mem :
      QuotientGroup.mk' I (pi q.1.out) = 1 := by
    -- The quotient-out representative still lies in `ker(pi₂)`, so its image in `G / I` is
    -- trivial.
    simpa [G2, I2, pi, generated_cover_proj_to_quotient_descends,
      fixed_constituent_generated_cover_proj_to_quotient,
      normalized_kernel_out_represents_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q] using q.2
  let x : I := ⟨pi q.1.out, (QuotientGroup.eq_one_iff (pi q.1.out)).mp hpi_mem⟩
  let c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
      Subgroup.subset_closure ⟨x, rfl⟩⟩
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The scalar endomorphism theorem controls all fiber discrepancies through `U₁ = Aˣ`.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- This re-exposes the scalar description of the kernel fiber for the raw representative
    -- comparison.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (x : G) q.1.out.1.2
  have hpow_one :
      QuotientGroup.mk' Qd ((Units.map (IsLocalRing.residue A) a) ^ d) = 1 := by
    -- Passing to the quotient by `d`-th powers removes the residual scalar ambiguity.
    exact
      (QuotientGroup.eq_one_iff
        ((Units.map (IsLocalRing.residue A) a) ^ d)).2
        ⟨Units.map (IsLocalRing.residue A) a, rfl⟩
  refine ⟨c, ?_⟩
  calc
    QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
      fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x := by
          -- Compare the raw representative to the chosen section over the same `x ∈ I`.
          rw [fixed_constituent_section_determinant_class, ha, Units.map_mul, MonoidHom.map_pow,
            map_mul, hpow_one, mul_one]
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c := by
          -- Section determinants over `I` were reduced to the determinant subgroup in the
          -- previous helper.
          simpa [c] using
            section_determinant_class_eq_determinant_subgroup_residue_class_of_mem_I
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift x

/-- Helper for Theorem 17-17.6-1: for `q ∈ N̄`, the raw quotient-out representative `q.1.out`
and the chosen Hall-kernel correction contribute the same determinant class modulo `d`-th powers.
This is the correction-specific replacement for the earlier existential class statement. -/
private theorem kernel_out_representative_det_residue_class_eq_correction_residue_class
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative_correction
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)),
          normalized_kernel_representative_correction_det_mem_determinant_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩ := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let x : I := by
    refine ⟨pi q.1.out, ?_⟩
    have hpi_mem :
        QuotientGroup.mk' I (pi q.1.out) = 1 := by
      -- The quotient-out representative still lies in `ker(pi₂)`, so its image in `G / I`
      -- is trivial.
      simpa [G2, I2, pi, generated_cover_proj_to_quotient_descends,
        fixed_constituent_generated_cover_proj_to_quotient,
        normalized_kernel_out_represents_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q] using q.2
    exact (QuotientGroup.eq_one_iff (pi q.1.out)).mp hpi_mem
  let c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)),
      normalized_kernel_representative_correction_det_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
  have hx :
      x =
        normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q := by
    apply Subtype.ext
    -- Reuse the extracted source-level bridge instead of reopening the normalization witness.
    simpa [x, pi] using
      (normalized_kernel_representative_correction_val_eq_out_proj
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).symm
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The scalar-endomorphism route is the same as in the existential class lemma; only the
    -- final witness is now frozen to the chosen correction.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- This exposes the same scalar-kernel owner `U₁ = Aˣ` used in the source determinant
    -- comparison.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (x : G) q.1.out.1.2
  have hpow_one :
      QuotientGroup.mk' Qd ((Units.map (IsLocalRing.residue A) a) ^ d) = 1 := by
    -- Passing to the quotient by `d`-th powers kills the residual scalar ambiguity.
    exact
      (QuotientGroup.eq_one_iff
        ((Units.map (IsLocalRing.residue A) a) ^ d)).2
        ⟨Units.map (IsLocalRing.residue A) a, rfl⟩
  have hc_eq :
      ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
        Subgroup.subset_closure ⟨x, rfl⟩⟩ = c := by
    -- After identifying the raw correction witness with the chosen correction, both subgroup
    -- elements have the same underlying determinant generator.
    apply Subtype.ext
    simpa [c, hx] using
      fixed_constituent_transport_fiber_det_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  calc
    QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
      fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x := by
          -- Compare the raw representative to the chosen section over the correction `x ∈ I`.
          rw [fixed_constituent_section_determinant_class, ha, Units.map_mul, MonoidHom.map_pow,
            map_mul, hpow_one, mul_one]
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I
        ⟨fixed_constituent_action_det (A := A) (G := G) I ρA_I x,
          Subgroup.subset_closure ⟨x, rfl⟩⟩ := by
            -- Over the Hall kernel, section determinants already match the determinant subgroup
            -- modulo `d`-th powers.
            simpa [x] using
              section_determinant_class_eq_determinant_subgroup_residue_class_of_mem_I
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                hTransportLift x
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c := by
          rw [hc_eq]

/-- Helper for Theorem 17-17.6-1: the determinant of LinearRepresentations_Serre_1977's normalized representative is the
determinant of the raw quotient-out representative multiplied by the inverse determinant of the
chosen Hall-kernel correction. This keeps the later kernel calculation transport-stable. -/
private theorem normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2 *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_of_hall_kernel_element
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative_correction
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)))⁻¹ := by
  -- Route correction: unfold the normalized representative once, then compute the determinant
  -- through the transport-fiber composition and inverse formulas.
  change
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          q.1.out.1.2
          (fixed_constituent_transport_fiber_inv
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative_correction
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)))) =
      _
  rw [fixed_constituent_transport_fiber_det_comp, fixed_constituent_transport_fiber_det_inv,
    fixed_constituent_transport_fiber_det_of_hall_kernel_element]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 17-17.6-1: after cancelling the raw quotient-out determinant against the
literal Hall-kernel correction chosen in the normalized representative, the residual determinant
class in `kˣ / (kˣ)^d` is trivial. This isolates the quotient-level cancellation before the later
upstairs subgroup argument. -/
private theorem normalized_kernel_determinant_class_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
      1 := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨corrDet,
      normalized_kernel_representative_correction_det_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
  have hraw :
      QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c := by
    -- Freeze the correction as an actual element of `C`; the raw determinant class is exactly
    -- that correction class by the previously established quotient comparison.
    simpa [Qd, corrDet, c] using
      kernel_out_representative_det_residue_class_eq_correction_residue_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  calc
    QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2 *
            corrDet⁻¹)) := by
          -- First flatten the normalized determinant into raw determinant times correction.
          simp only [Qd, corrDet]
          rw [normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q]
    _ =
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) *
        (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) corrDet))⁻¹ := by
          -- The quotient map and the residue map are homomorphisms, so the correction peels off
          -- multiplicatively.
          simp [map_mul]
    _ =
      fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c *
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c)⁻¹ := by
          -- Replace both quotient factors by the same literal correction class in `C`.
          rw [hraw]
          rw [fixed_constituent_determinant_subgroup_residue_class]
    _ = 1 := by simp

/-- Helper for Theorem 17-17.6-1: the quotient-trivial determinant class of LinearRepresentations_Serre_1977's normalized
representative is already witnessed by an explicit `d`-th power in the residue-field units. This
freezes the quotient-level endpoint in a rewrite-friendly form before the remaining literal
determinant-subgroup upgrade. -/
private theorem normalized_kernel_representative_det_residue_eq_dth_power
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ b : kˣ,
      Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2) =
        b ^ Module.finrank A P_S := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  have hclass :
      QuotientGroup.mk'
          Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
        1 := by
    -- Reuse the already closed quotient-level cancellation for the normalized determinant class.
    simpa [Qd] using
      normalized_kernel_determinant_class_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  rcases (QuotientGroup.eq_one_iff
      (Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2))).mp
      hclass with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  -- Unpack membership in the `d`-th-power subgroup into the explicit witness equality.
  simpa [Qd, d] using hb.symm

/-- Helper for Theorem 17-17.6-1: the determinant of the scalar-normalized representative gives a
trivial class in `kˣ / (kˣ)^d` even after rewriting that determinant as `kernelScalar(q)^d`. This
records the exact verified endpoint of the current quotient-level calculation. -/
private theorem kernel_scalar_pow_residue_class_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          ((kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) ^
            Module.finrank A P_S)) =
      1 := by
  -- Rewrite LinearRepresentations_Serre_1977's scalar determinant as the determinant of the normalized representative, then
  -- apply the quotient-level cancellation already proved above.
  calc
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          ((kernel_scalar_unit
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) ^
            Module.finrank A P_S)) =
      QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) := by
          -- This is exactly the scalar determinant formula for the normalized representative.
          rw [← normalized_kernel_representative_det_eq_kernel_scalar_pow
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
    _ = 1 := by
          exact
            normalized_kernel_determinant_class_eq_one
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: in the notation of LinearRepresentations_Serre_1977's finite kernel package, every
`q ∈ N̄ = ker(pi₂)` already satisfies the quotient-side scalar identity
`res((kernelScalar q)^d) = 1` in `kˣ / (kˣ)^d`. This repackages the scalar rewrite theorem at the
actual kernel object used later in the projective-extension package. -/
private theorem kernel_scalar_pow_residue_class_eq_one_on_kernel_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let kernelScalar : Nbar →* Aˣ :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ q : Nbar,
      QuotientGroup.mk'
          ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
          (Units.map (IsLocalRing.residue A)
            (kernelScalar q ^ Module.finrank A P_S)) =
        1 := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let kernelScalar : Nbar →* Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  intro q
  -- This is exactly the already proved scalar rewrite theorem, restated on the kernel subgroup
  -- notation used by the later finite-extension package.
  simpa [G2, I2, pi2, Nbar, kernelScalar] using
    kernel_scalar_pow_residue_class_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the normalized determinant of a kernel representative is already
an actual `d`-th power in `Aˣ`. This packages the Hensel-lifting step separately from the later
literal-membership argument in LinearRepresentations_Serre_1977's determinant subgroup `C`. -/
private theorem normalized_kernel_representative_det_exists_dth_root
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    ∃ a : Aˣ,
      a ^ Module.finrank A P_S =
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 := by
  -- First freeze the quotient-level endpoint as an explicit residue-field `d`-th power.
  have hres_dth_power :
      ∃ b : kˣ,
        Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2) =
          b ^ Module.finrank A P_S := by
    exact
      normalized_kernel_representative_det_residue_eq_dth_power
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  -- Then apply the already isolated Hensel step to lift that residue root to an actual unit root.
  exact
    exists_dth_root_of_unit_of_residue_eq_dth_power
      (A := A) (p := p)
      (u := fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)
      (d := Module.finrank A P_S)
      hp
      (fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar)
      hres_dth_power

/-- Helper for Theorem 17-17.6-1: once the normalized representatives of `N̄ = ker(pi₂)` are
rewritten as literal scalar points `(1, a • id)`, their classes commute with the whole quotient
`G₂ ⧸ I₂`. This closes the centrality half of LinearRepresentations_Serre_1977's finite kernel package. -/
private theorem kernel_subgroup_central_of_normalized_representatives
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker ≤
      Subgroup.center
        ((fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ⧸
          fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro q
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk'_surjective I2 g
  have hcomm :
      normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q * g0 =
        g0 *
          normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q := by
    apply Subtype.ext
    -- Rewrite the normalized representative as the scalar point `(1, a • id)` and commute it in
    -- the ambient total space before returning to the generated cover subtype.
    calc
      ((normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q * g0) : G2).1 =
        fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1)
          g0.1 := rfl
      _ =
        fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ⟨1,
            scalar_transport_fiber_one
              (A := A) (G := G) (I := I) ρA_I
              (kernel_scalar_unit
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)⟩
          g0.1 := by
            rw [normalized_kernel_representative_eq_scalar_total_space
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
      _ =
        fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          g0.1
          ⟨1,
            scalar_transport_fiber_one
              (A := A) (G := G) (I := I) ρA_I
              (kernel_scalar_unit
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)⟩ := by
            exact
              scalar_transport_total_space_commutes
                (A := A) (G := G) (I := I) ρA_I
                (kernel_scalar_unit
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q)
                g0.1
      _ =
        fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          g0.1
          ((normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1) := by
            rw [normalized_kernel_representative_eq_scalar_total_space
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
      _ =
        ((g0 *
          normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q) : G2).1 := rfl
  -- Pass the ambient commutation relation down to the quotient `G₂ ⧸ I₂`.
  simpa [map_mul, normalized_kernel_representative_mk_eq
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q] using
    congrArg (QuotientGroup.mk' I2) hcomm

/-- Helper for Theorem 17-17.6-1: any element of the transport fiber `U_s` determines a reduced
comparison from the fixed constituent `S̄` to the transported constituent `sS̄`; the difference
from the chosen section point in the same fiber is a scalar automorphism coming from the kernel
ratio in `U₁`. -/
private theorem exists_fixed_constituent_transport_fiber_reduction_equiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    ∃ e : Sbar.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar s).toRepresentation,
      (((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S) := by
  let u0 :=
    fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  let w :=
    fixed_constituent_transport_fiber_ratio
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The fixed lifted constituent still has only scalar equivariant endomorphisms.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
      (A := A) (G := G) (I := I) ρA_I hscalar w
  let abar : kˣ := Units.map (IsLocalRing.residue A) a
  let eScalar : Sbar.toRepresentation.Equiv Sbar.toRepresentation :=
    scalar_representation_self_equiv Sbar.toRepresentation abar
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hkernel_map :
      hLiftSbar.endAlgHom
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) w) =
        (IsLocalRing.residue A (a : A)) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
    have hw_scalar :
        fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) w =
          (a : A) • Representation.IntertwiningMap.id ρA_I := by
      -- The kernel ratio is literally the scalar homothety classified above.
      change
        (fixed_constituent_transport_kernel_intertwiningEnd
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) w : P_S →ₗ[A] P_S) =
          (a : A) • LinearMap.id
      simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
        congrArg (fun e : P_S ≃ₗ[A] P_S => (e : P_S →ₗ[A] P_S)) ha
    rw [hw_scalar]
    simpa using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar (a : A)
  have hw_red :
      red_S.comp w.toLinearMap =
        ((eScalar.toLinearMap.restrictScalars A).comp red_S) := by
    -- Reducing the kernel ratio gives exactly the scalar automorphism induced by `a`.
    ext x
    calc
      red_S (w x) =
        hLiftSbar.endAlgHom
            (fixed_constituent_transport_kernel_intertwiningEnd
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) w) (red_S x) := by
                symm
                simpa using
                  LinearMap.IsResidueFieldReduction.endAlgHom_comp_apply hred
                    (fixed_constituent_transport_kernel_intertwiningEnd
                      (A := A) (G := G) (I := I) (ρA_I := ρA_I) w) x
      _ = (IsLocalRing.residue A (a : A)) • red_S x := by
            simpa [hkernel_map]
      _ = eScalar (red_S x) := by
            simp [eScalar, scalar_representation_self_equiv, abar]
  have hw_comp :
      w.toLinearMap.comp u0.toLinearMap = u.toLinearMap := by
    -- The kernel ratio is the literal operator `u * u0⁻¹`, so composing it with `u0` returns `u`.
    simpa [w, u0] using
      fixed_constituent_transport_fiber_ratio_comp_right
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u u0
  have hu_red :
      (((eScalar.symm.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap) =
        red_S.comp u0.toLinearMap := by
    -- Cancel the scalar kernel correction before comparing `u` with the chosen section point.
    calc
      (((eScalar.symm.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap) =
        (((eScalar.symm.toLinearMap.restrictScalars A).comp red_S).comp
          (w.toLinearMap.comp u0.toLinearMap)) := by
            rw [← hw_comp]
      _ =
        ((((eScalar.symm.toLinearMap.restrictScalars A).comp red_S).comp w.toLinearMap).comp
          u0.toLinearMap) := by
            simp [LinearMap.comp_assoc]
      _ =
        ((((eScalar.symm.toLinearMap.restrictScalars A).comp
            ((eScalar.toLinearMap.restrictScalars A).comp red_S))).comp
          u0.toLinearMap) := by
            rw [hw_red]
      _ = red_S.comp u0.toLinearMap := by
            simp [LinearMap.comp_assoc]
  refine ⟨eScalar.symm.trans (hTransport s).some, ?_⟩
  -- Compose the chosen reduced comparison with the inverse scalar correction on `S̄`.
  calc
    ((((eScalar.symm.trans (hTransport s).some).toLinearMap.restrictScalars A).comp red_S).comp
        u.toLinearMap) =
      (((hTransport s).some.toLinearMap.restrictScalars A).comp
        ((((eScalar.symm.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap))) := by
          simp [LinearMap.comp_assoc]
    _ =
      (((hTransport s).some.toLinearMap.restrictScalars A).comp (red_S.comp u0.toLinearMap)) := by
          rw [hu_red]
    _ =
      ((((hTransport s).some.toLinearMap.restrictScalars A).comp red_S).comp u0.toLinearMap) := by
          simp [LinearMap.comp_assoc]
    _ =
      ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
        red_S := by
          exact
            fixed_constituent_transport_aut_of_lift_reduction
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: choose the reduced comparison attached to an arbitrary element
of the transport fiber `U_s`. This is the reusable reduction-side interface needed for the later
`G₂`-action on the multiplicity space. -/
private noncomputable def fixed_constituent_transport_fiber_reduction_equiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    Sbar.toRepresentation.Equiv
      (transportedSubrepresentation ρ Sbar s).toRepresentation :=
  Classical.choose <|
    exists_fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u

/-- Helper for Theorem 17-17.6-1: the chosen reduced comparison for an arbitrary fiber element
intertwines its action on the lift carrier with the canonical transported constituent map in the
ambient representation. -/
private theorem fixed_constituent_transport_fiber_reduction_equiv_spec
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    ((((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u).toLinearMap
          .restrictScalars A).comp red_S).comp u.toLinearMap =
      ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
        red_S := by
  -- Unpack the chosen reduction bridge once so later quotient-action constructions can rewrite
  -- through it directly.
  exact
    Classical.choose_spec <|
      exists_fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u

/-- Helper for Theorem 17-17.6-1: the chosen reduced comparison attached to a fixed transport
fiber element is uniquely determined by its reduction identity after composing with `red_S`.
This packages the exact source-side uniqueness needed before enforcing group-law coherence. -/
private theorem fixed_constituent_transport_fiber_reduction_equiv_unique
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    {e e' :
      Sbar.toRepresentation.Equiv
        (transportedSubrepresentation ρ Sbar s).toRepresentation}
    (he :
      (((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S))
    (he' :
      (((e'.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap =
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).toLinearMap.restrictScalars A).comp
          red_S)) :
    e = e' := by
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hred_surj : Function.Surjective red_S := by
    -- Reuse the canonical fixed-constituent surjectivity owner instead of reproving it locally.
    exact fixed_constituent_reduction_surjective (A := A) (H := I) hred
  have hu_surj : Function.Surjective (red_S.comp u.toLinearMap) := by
    intro x
    obtain ⟨y, hy⟩ := hred_surj x
    refine ⟨u.symm y, ?_⟩
    simpa [LinearMap.comp_apply, hy]
  apply Representation.Equiv.ext
  funext x
  obtain ⟨y, hy⟩ := hu_surj x
  have hcomp :
      (((e.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap) y =
        (((e'.toLinearMap.restrictScalars A).comp red_S).comp u.toLinearMap) y := by
    rw [he, he']
  -- Surjectivity of `red_S ∘ u` lets us compare the two reduced operators pointwise.
  simpa [LinearMap.comp_apply, hy] using hcomp

/-- Helper for Theorem 17-17.6-1: when the transport fiber element is the distinguished lift-side
automorphism `fixed_constituent_transport_aut_of_lift s`, the chosen reduction equivalence on
`S̄` is exactly LinearRepresentations_Serre_1977's fixed comparison `hTransport s`. This freezes the cover-side source
transport before the later `G₂`-action on the multiplicity space. -/
private theorem fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      (hTransport s).some := by
  -- Both candidates satisfy the same defining reduction identity for the distinguished lift-side
  -- transport automorphism, so uniqueness forces them to agree.
  apply fixed_constituent_transport_fiber_reduction_equiv_unique
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    (u := fixed_constituent_transport_aut_of_lift
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)
  · exact
      fixed_constituent_transport_fiber_reduction_equiv_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)
  · exact
      fixed_constituent_transport_aut_of_lift_reduction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: for the literal identity element of the lift-side fiber `U₁`,
the chosen reduced comparison is the canonical transport at `1`. This isolates the precise
`g = 1` source normalization before the future cover action on `Hom^I(S̄, V)` is checked. -/
private theorem fixed_constituent_transport_fiber_reduction_equiv_eq_identity_transport
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I) =
      transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G) := by
  -- The identity fiber element already satisfies the defining reduction equation for the
  -- canonical transport at `1`, so uniqueness fixes the chosen comparison.
  apply fixed_constituent_transport_fiber_reduction_equiv_unique
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    (u := fixed_constituent_transport_fiber_one
      (A := A) (G := G) (I := I) ρA_I)
  · exact
      fixed_constituent_transport_fiber_reduction_equiv_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I)
  · -- For the literal identity fiber, composition with the fiber automorphism does nothing.
    ext x
    simp [fixed_constituent_transport_fiber_one, LinearMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: precomposing LinearRepresentations_Serre_1977's multiplicity space by the reduction
equivalence attached to the distinguished lift-side transport automorphism agrees with the
earlier transported-constituent linear equivalence. This packages the exact source-side
identification needed before defining the upstairs `G₂`-action on `Hom^I(S̄, V)`. -/
private theorem
    chosen_transport_fixed_isotypic_multiplicity_space_linearEquiv_eq_transport
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_isotypic_multiplicity_space_precompose_linearEquiv
        (I := I) (ρ := ρ)
        (fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
          (fixed_constituent_transport_aut_of_lift
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
      transported_fixed_isotypic_multiplicity_space_linearEquiv
        (I := I) (ρ := ρ) Sbar s := by
  ext f x
  -- After identifying the chosen reduction equivalence with the canonical transported
  -- constituent comparison, both precomposition operators act pointwise by the same formula.
  simp [transported_fixed_isotypic_multiplicity_space_linearEquiv,
    fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport]

/-- Helper for Theorem 17-17.6-1: comparing the reduction equivalence attached to an arbitrary
cover fiber element with the fixed chosen transport over the same `s : G` gives an honest
`I`-equivariant automorphism of the fixed constituent `S̄`. This isolates the source-side
correction term that must be inserted before defining the `G₂`-action on `Hom^I(S̄, V)`. -/
private noncomputable def fixed_isotypic_cover_source_correction_equiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    Sbar.toRepresentation.Equiv Sbar.toRepresentation :=
  (fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u).trans
    ((hTransport s).some.symm)

/-- Helper for Theorem 17-17.6-1: for the distinguished lift-side transport element over `s`,
the source-correction automorphism is the identity. This records that only non-section fiber
choices contribute a genuine correction term. -/
private theorem fixed_isotypic_cover_source_correction_equiv_section_eq_refl
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_isotypic_cover_source_correction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      Representation.Equiv.mk (LinearEquiv.refl k Sbar.toSubmodule) (by
        intro a
        ext x
        rfl) := by
  -- Replace the arbitrary fiber reduction by the distinguished chosen transport; the correction
  -- then collapses to the identity by direct cancellation.
  ext x
  simp [fixed_isotypic_cover_source_correction_equiv,
    fixed_constituent_transport_fiber_reduction_equiv_eq_chosen_transport]

/-- Helper for Theorem 17-17.6-1: precomposing multiplicity maps by the source-correction
automorphism attached to a cover fiber element yields a canonical linear self-equivalence of
`Hom^I(S̄, V)`. This is the exact source-side factor that remains after freezing the chosen
transport. -/
private noncomputable def fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fixed_isotypic_multiplicity_space_precompose_linearEquiv
    (I := I) (ρ := ρ)
    (fixed_isotypic_cover_source_correction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u)

/-- Helper for Theorem 17-17.6-1: the multiplicity-space source correction is trivial on the
distinguished chosen lift-side transport. This is the exact normalization needed when the future
`G₂`-action is checked first on the section generators of the generated cover. -/
private theorem fixed_isotypic_cover_source_correction_multiplicity_linearEquiv_section_eq_refl
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
        (fixed_constituent_transport_aut_of_lift
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      LinearEquiv.refl k
        (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
  -- Once the source correction on `S̄` is the identity, the induced precomposition operator on
  -- `Hom^I(S̄, V)` is also the identity map.
  ext f x
  simp [fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv_section_eq_refl,
    fixed_isotypic_multiplicity_space_precompose_linearEquiv,
    Representation.IntertwiningMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: for the literal identity cover element, the multiplicity-space
source correction is exactly the precomposition operator induced by the canonical comparison
between the chosen reduced transport at `1` and the user-supplied comparison `hTransport 1`.
This records the entire `g = 1` source-side discrepancy in one reusable linear equivalence. -/
private theorem fixed_isotypic_cover_source_correction_multiplicity_linearEquiv_identity_fiber
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I) =
      fixed_isotypic_multiplicity_space_precompose_linearEquiv
        (I := I) (ρ := ρ)
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar (1 : G)).trans
          ((hTransport (1 : G)).some.symm)) := by
  -- Unfold the source-correction operator at the literal identity cover point and rewrite the
  -- reduction comparison by the preceding identity-fiber lemma.
  rw [fixed_isotypic_cover_source_correction_multiplicity_linearEquiv]
  congr 1
  rw [fixed_constituent_transport_fiber_reduction_equiv_eq_identity_transport
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift]

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal determinant-normalized cover is the subgroup of
the total transport space cut out by the source condition `det(t) ∈ C`. This names the source
object that the later finite cover should use, instead of rebuilding it ad hoc inside the kernel
proof. -/
private noncomputable def fixed_constituent_literal_determinant_cover_local
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Subgroup (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :=
  { carrier := { g |
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I }
    one_mem' := by
      -- The identity transport has determinant `1`, and `1` lies in the determinant subgroup.
      simpa using
        (fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I).one_mem
    mul_mem' := by
      intro g h hg hh
      -- Literal determinant membership is stable under multiplication in the total space.
      simpa [fixed_constituent_transport_fiber_det_comp] using
        (fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I).mul_mem hg hh
    inv_mem' := by
      intro g hg
      -- The same subgroup condition is stable under inversion.
      simpa [fixed_constituent_transport_fiber_det_inv] using
        (fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I).inv_mem hg }

/-- Helper for Theorem 17-17.6-1: every Hall-kernel generator already lies in the literal
determinant cover, because its determinant is one of the defining generators of `C`. -/
private theorem fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    (⟨(x : G),
        fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x⟩ :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) ∈
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I := by
  -- The determinant of the embedded Hall-kernel point is literally a generator of `C`.
  change
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  rw [fixed_constituent_transport_fiber_det_of_hall_kernel_element
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  exact Subgroup.subset_closure ⟨x, rfl⟩

/-- Helper for Theorem 17-17.6-1: the quotienting subgroup `I₂ ≤ G₂` is already contained in the
literal determinant cover. This closes the Hall-kernel branch of the future source-faithful
replacement `G₂(det)` before the normalized-section branch is added. -/
private theorem fixed_constituent_generated_cover_hall_kernel_subgroup_mem_literal_determinant_cover_local
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (y :
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :
    (((y : fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) ∈
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I) := by
  -- Unpack `y ∈ I₂` as an embedded Hall-kernel element and use the previous literal-membership
  -- computation.
  rcases y.property with ⟨x, rfl⟩
  exact
    fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I x

/-- Helper for Theorem 17-17.6-1: restricting the total-space projection `G₁ → G` to LinearRepresentations_Serre_1977's
literal determinant cover gives the source-faithful projection `G₂(det) → G`. This packages the
literal owner before quotienting by the Hall-kernel image. -/
private noncomputable def fixed_constituent_literal_determinant_cover_proj_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I →* G :=
  (fixed_constituent_transport_total_space_proj_hom
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
    (Subgroup.subtype
      (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I))

/-- Helper for Theorem 17-17.6-1: if the chosen section determinant class at `s` already matches
one class coming from LinearRepresentations_Serre_1977's determinant subgroup `C`, then a single scalar kernel correction
moves the chosen section value into the literal determinant cover over `s`. This isolates the
exact adjustment step needed before proving surjectivity of `G₂(det) → G`. -/
private theorem section_value_mem_literal_determinant_cover_of_section_class_eq
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G)
    (c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I)
    (hclass :
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c) :
    ∃ g :
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I,
      fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g = s := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let secDet : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2
  have hratio_class_one :
      QuotientGroup.mk'
          Qd
          (Units.map (IsLocalRing.residue A) (secDet⁻¹ * c)) = 1 := by
    -- Compare the section determinant class with the chosen class in `C`; their ratio is
    -- quotient-trivial modulo `d`-th powers.
    calc
      QuotientGroup.mk'
          Qd
          (Units.map (IsLocalRing.residue A) (secDet⁻¹ * c)) =
        (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) secDet))⁻¹ *
          QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) c) := by
            simp [map_mul]
      _ =
        (fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c)⁻¹ *
          fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c := by
              rw [← hclass]
              simp [Qd, sec, secDet, fixed_constituent_section_determinant_class]
      _ = 1 := by simp
  have hroot_residue :
      ∃ b : kˣ,
        Units.map (IsLocalRing.residue A) (secDet⁻¹ * c) = b ^ d := by
    rcases (QuotientGroup.eq_one_iff
        (Units.map (IsLocalRing.residue A) (secDet⁻¹ * c))).mp hratio_class_one with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simpa [Qd, d] using hb.symm
  have hdimcop : Nat.Coprime p d := by
    -- The degree of the fixed lifted constituent is prime to `p`, so the Hensel root step
    -- applies to the scalar ratio `secDet⁻¹ * c`.
    simpa [d] using
      fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  obtain ⟨a, ha_pow⟩ :=
    exists_dth_root_of_unit_of_residue_eq_dth_power
      (A := A) (p := p) (u := secDet⁻¹ * c) (d := d) hp hdimcop hroot_residue
  let adjustedFiber :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (sec s).2
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a)
  have hscalar_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I a) =
        a ^ d := by
    -- The scalar correction sits in the kernel fiber `U₁`, so its determinant is the literal
    -- `d`-th power of the chosen unit.
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) rfl
  have hadjusted_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) adjustedFiber ∈
        fixed_constituent_determinant_subgroup
          (A := A) (G := G) (I := I) ρA_I := by
    -- Route correction: rather than identifying the section determinant directly, adjust it by
    -- the explicit scalar root so the resulting determinant is literally the chosen element of
    -- `C`.
    have hdet_eq :
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) adjustedFiber =
          c := by
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) adjustedFiber =
          secDet *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (scalar_transport_fiber_one
                (A := A) (G := G) (I := I) ρA_I a) := by
                  simpa [adjustedFiber, secDet] using
                    fixed_constituent_transport_fiber_det_comp
                      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                      (sec s).2
                      (scalar_transport_fiber_one
                        (A := A) (G := G) (I := I) ρA_I a)
        _ = secDet * a ^ d := by rw [hscalar_det]
        _ = c := by
              rw [ha_pow]
              simp [secDet, mul_assoc, mul_left_comm, mul_comm]
    exact hdet_eq ▸ c.property
  refine ⟨⟨⟨s, adjustedFiber⟩, hadjusted_det⟩, rfl⟩

/-- Helper for Theorem 17-17.6-1: once every chosen section determinant class is known to come
from LinearRepresentations_Serre_1977's determinant subgroup `C`, the literal determinant-cover projection `G₂(det) → G` is
surjective by applying the previous scalar-adjustment step fiberwise. This leaves the remaining
literal-cover pivot blocked only on proving the section-class equality itself. -/
private theorem
    fixed_constituent_literal_determinant_cover_proj_surjective_of_section_class_lands_in_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hsection :
      ∀ s : G,
        ∃ c :
          fixed_constituent_determinant_subgroup
            (A := A) (G := G) (I := I) ρA_I,
          fixed_constituent_section_determinant_class
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
            fixed_constituent_determinant_subgroup_residue_class
              (A := A) (G := G) (I := I) ρA_I c) :
    Function.Surjective
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  intro s
  rcases hsection s with ⟨c, hc⟩
  -- Apply the explicit scalar adjustment in the fiber over `s` using the prescribed class in `C`.
  exact
    section_value_mem_literal_determinant_cover_of_section_class_eq
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s c hc

/-- Helper for Theorem 17-17.6-1: the literal Hall-kernel embedding `I → G₁` already lands in
the determinant-normalized cover, so it cod-restricts to LinearRepresentations_Serre_1977's literal owner `G₂(det)`. -/
private noncomputable def fixed_constituent_literal_determinant_cover_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    I →*
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I :=
  MonoidHom.codRestrict
    (fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I))
    (fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I)
    (fun x ↦
      fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I x)

/-- Helper for Theorem 17-17.6-1: after cod-restricting to the literal determinant cover, the
embedded Hall-kernel point still projects to the original Hall-kernel element in `G`. -/
@[simp] private theorem fixed_constituent_literal_determinant_cover_proj_apply_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_literal_determinant_cover_embed_hall_kernel
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
      x := by
  -- Both codomain restrictions are definitional, so the literal cover still remembers the same
  -- Hall-kernel element in `G`.
  rfl

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal subgroup `I₂(det) ≤ G₂(det)` is the range of
the Hall-kernel embedding into the determinant-normalized cover. This isolates the literal owner
that the remaining quotient package should use. -/
private noncomputable def fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Subgroup
      (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I) :=
  (fixed_constituent_literal_determinant_cover_embed_hall_kernel
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)).range

/-- Helper for Theorem 17-17.6-1: the literal determinant-cover projection to `G` descends to
`G / I` and kills the embedded Hall-kernel range on the nose. This is the quotient-side owner
map that the remaining source-faithful package should descend through. -/
private theorem fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I ≤
      ((QuotientGroup.mk' I).comp
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))).ker := by
  intro g hg
  rcases hg with ⟨x, rfl⟩
  -- The literal Hall-kernel image still projects to the trivial class in `G / I`.
  simp [fixed_constituent_literal_determinant_cover_hall_kernel_subgroup]

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's literal projection `G₂(det) → G` descends through the
embedded Hall-kernel range to a quotient map `G₂(det) / I₂(det) → G / I`. This isolates the
formal quotient owner used in the literal-cover pivot before any finite-kernel analysis. -/
private noncomputable def fixed_constituent_literal_determinant_cover_proj_to_quotient
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I ⧸
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I) →* G ⧸ I :=
  QuotientGroup.lift
    (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I)
    (((QuotientGroup.mk' I).comp
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I))))
    (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
      (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: if the literal determinant cover already surjects onto `G`,
then the descended quotient map `G₂(det) / I₂(det) → G / I` is surjective as well. This closes
the purely formal descent step of the literal-cover pivot independently of the harder kernel
analysis. -/
private theorem fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_proj_surjective
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)) ) :
    Function.Surjective
      (fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  intro q
  rcases QuotientGroup.mk'_surjective I q with ⟨g, rfl⟩
  rcases hproj_surj g with ⟨x, rfl⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  -- Once the representative is chosen upstairs, the descended map is definitionally the quotient
  -- projection of the same point in `G₂(det)`.
  simp [fixed_constituent_literal_determinant_cover_proj_to_quotient]

/-- Helper for Theorem 17-17.6-1: surjectivity of the literal determinant-cover projection gives
the first-isomorphism equivalence `((G₂(det) / I₂(det)) / ker(pi₂(det))) ≃ G / I`. This packages
the quotient-kernel part of LinearRepresentations_Serre_1977's literal finite cover independently of the later cyclicity and
coprimality analysis on the kernel. -/
private noncomputable def fixed_constituent_literal_determinant_cover_kernel_quotient_equiv_of_proj_surjective
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)) ) :
    (((fixed_constituent_literal_determinant_cover_local
          (A := A) (G := G) (I := I) ρA_I ⧸
        fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
          (A := A) (G := G) (I := I) ρA_I) ⧸
      (fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker) ≃* G ⧸ I := by
  let pi2 :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  have hpi2_surj : Function.Surjective pi2 := by
    -- Surjectivity descends directly from the literal-cover projection to `G`.
    exact
      fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_proj_surjective
        (A := A) (G := G) (I := I) ρA_I hproj_surj
  -- Apply the first isomorphism theorem to the descended quotient map.
  simpa [pi2] using QuotientGroup.quotientKerEquivOfSurjective pi2 hpi2_surj

/-- Helper for Theorem 17-17.6-1: after the determinant-normalized kernel scalar has been
extracted, the remaining Hall-kernel package is to prove that `N̄ = ker(pi₂)` is cyclic of order
prime to `p`. This isolates the exact upstairs finite-subgroup step still missing from the main
projective-extension assembly. -/
private theorem determinant_root_subgroup_cyclic_and_coprime
    (hp : Nat.Prime p)
    (C : Subgroup Aˣ)
    [Finite C]
    (hCcop : Nat.Coprime p (Nat.card C))
    {d : ℕ}
    (hdcop : Nat.Coprime p d) :
    let S : Subgroup Aˣ :=
      { carrier := { a | a ^ d ∈ C }
        one_mem' := by
          simpa using C.one_mem
        mul_mem' := by
          intro a b ha hb
          simpa [mul_pow] using C.mul_mem ha hb
        inv_mem' := by
          intro a ha
          simpa [inv_pow] using C.inv_mem ha }
    IsCyclic S ∧ Nat.Coprime p (Nat.card S) := by
  let n := d * Nat.card C
  let S : Subgroup Aˣ :=
    { carrier := { a | a ^ d ∈ C }
      one_mem' := by
        simpa using C.one_mem
      mul_mem' := by
        intro a b ha hb
        simpa [mul_pow] using C.mul_mem ha hb
      inv_mem' := by
        intro a ha
        simpa [inv_pow] using C.inv_mem ha }
  have hncop : Nat.Coprime p n := Nat.Coprime.mul_right hdcop hCcop
  have hpow_card :
      ∀ a : S, ((a : Aˣ) ^ n) = 1 := by
    intro a
    let c : C := ⟨(a : Aˣ) ^ d, a.2⟩
    -- Every element of the root subgroup has order dividing `d * |C|`.
    simpa [n, c, pow_mul] using congrArg Subtype.val (pow_card_eq_one' (x := c))
  let resS : S →* rootsOfUnity n k :=
    MonoidHom.codRestrict
      ((Units.map (IsLocalRing.residue A)).comp (Subgroup.subtype S))
      (rootsOfUnity n k)
      (fun a ↦ by
        -- Reducing preserves the bounded exponent `d * |C|`, so the image lands in roots of unity.
        exact
          (mem_rootsOfUnity n
            (((Units.map (IsLocalRing.residue A)).comp (Subgroup.subtype S)) a)).2 <| by
              simpa [n, map_pow] using congrArg (Units.map (IsLocalRing.residue A)) (hpow_card a))
  have hresS_injective : Function.Injective resS := by
    intro a b hab
    apply Subtype.ext
    have hres_div :
        Units.map (IsLocalRing.residue A) ((a : Aˣ) / (b : Aˣ)) = 1 := by
      -- Equality after reduction forces the reduced quotient to be the identity.
      have hab_val : ((resS a : rootsOfUnity n k) : kˣ) = (resS b : rootsOfUnity n k) := by
        exact congrArg Subtype.val hab
      rw [show Units.map (IsLocalRing.residue A) ((a : Aˣ) / (b : Aˣ)) =
          Units.map (IsLocalRing.residue A) (a : Aˣ) /
            Units.map (IsLocalRing.residue A) (b : Aˣ) by
            simp]
      simpa [div_eq_one_iff_eq] using hab_val
    have hpow_div :
        (((a : Aˣ) / (b : Aˣ)) ^ n) = 1 := by
      -- The quotient still lies in the same root subgroup, hence has the same bounded order.
      simpa using hpow_card (a / b)
    have hdiv_one :
        ((a : Aˣ) / (b : Aˣ)) = 1 := by
      apply unit_eq_one_of_pow_eq_one_of_residue_eq_one (A := A) (p := p) hp hncop hpow_div
      simpa using congrArg (fun z : kˣ ↦ (z : k)) hres_div
    exact div_eq_one.mp hdiv_one
  letI : Finite S := Finite.of_injective resS hresS_injective
  have hroots_cyclic : IsCyclic (rootsOfUnity n k) := by
    -- Finite subgroups of the residue-field unit group are cyclic.
    exact finite_subgroup_of_residue_units_isCyclic (A := A) (rootsOfUnity n k)
  have hrange_coprime :
      Nat.Coprime p (Nat.card resS.range) := by
    -- The range is a subgroup of the bounded roots-of-unity group, so its cardinal stays prime to
    -- `p`.
    exact
      (roots_of_unity_card_coprime_charP (A := A) hp n).of_dvd_right
        resS.range.card_subgroup_dvd_card
  have hcard_eq : Nat.card S = Nat.card resS.range := by
    -- Injectivity identifies the root subgroup with the range of the residue map.
    exact Nat.card_congr (MonoidHom.ofInjective resS hresS_injective).toEquiv
  constructor
  · -- Cyclicity is transported through the injective reduction map.
    exact isCyclic_of_injective resS hresS_injective
  · -- The same injective identification transfers the prime-to-`p` cardinal bound.
    rw [hcard_eq]
    exact hrange_coprime

/-- Helper for Theorem 17-17.6-1: once the literal inclusion
`kernelScalar(q) ^ d ∈ C` is available, the rest of LinearRepresentations_Serre_1977's finite-kernel package is a formal
transport along the injective scalar map `N̄ → Aˣ`. This keeps the remaining blocker confined to
the single upstairs membership step. -/
private theorem principal_unit_eq_one_of_power_mem_fixed_constituent_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {u : Aˣ} {n : ℕ}
    (hncop : Nat.Coprime p n)
    (hres : IsLocalRing.residue A (u : A) = 1)
    (hpow_mem :
      u ^ n ∈ fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    u = 1 := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  have hCcop : Nat.Coprime p (Nat.card C) := by
    -- The determinant subgroup inherits its prime-to-`p` cardinality from the Hall kernel `I`.
    simpa [C] using
      fixed_constituent_determinant_subgroup_coprime
        (A := A) (G := G) (I := I) hIcop ρA_I
  let c : C := ⟨u ^ n, hpow_mem⟩
  have hc_card : c ^ Nat.card C = 1 := by
    -- Every element of the finite determinant subgroup has order dividing `|C|`.
    exact pow_card_eq_one' (x := c)
  have hpow_unit : u ^ (n * Nat.card C) = 1 := by
    -- Forgetting the subtype identifies the finite-order relation in `C` with the same relation
    -- upstairs in the ambient unit group.
    simpa [c, pow_mul] using congrArg Subtype.val hc_card
  have hpow_ring : ((u : A) ^ (n * Nat.card C)) = 1 := by
    -- The torsion statement is now in the coefficient ring, exactly in the form used by the
    -- principal-unit lemma.
    simpa using congrArg (fun z : Aˣ ↦ (z : A)) hpow_unit
  have hncop' : Nat.Coprime p (n * Nat.card C) := hncop.mul_right hCcop
  -- Apply the already proved principal-unit rigidity lemma with the enlarged prime-to-`p`
  -- exponent `n * |C|`.
  exact
    unit_eq_one_of_pow_eq_one_of_residue_eq_one
      (A := A) (p := p) hp hncop' hpow_ring hres

/-- Helper for Theorem 17-17.6-1: after freezing LinearRepresentations_Serre_1977's Hall-kernel correction determinant
`corrDet ∈ C`, the extra ratio `u = det(normalizedRepresentative q) * corrDet⁻¹` still has
residue class of order dividing `|Candidate|` in `kˣ / (kˣ)^d`. This packages the quotient-level
torsion input that remains before upgrading to literal membership in `C`. -/
private theorem normalized_kernel_correction_ratio_residue_class_pow_card_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    let corrDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    let u : Aˣ := normalizedDet * corrDet⁻¹
    (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) u)) ^ n = 1 := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨corrDet,
      normalized_kernel_representative_correction_det_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let u : Aˣ := normalizedDet * corrDet⁻¹
  have hnormalized_class_one :
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) normalizedDet) = 1 := by
    -- The normalized determinant class is already trivial modulo `d`-th powers.
    simpa [Qd, normalizedDet] using
      normalized_kernel_determinant_class_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hcorr_class_pow_one :
      (fixed_constituent_determinant_subgroup_residue_class
        (A := A) (G := G) (I := I) ρA_I c) ^ n = 1 := by
    -- The correction class already lies in the finite candidate subgroup, so `|Candidate|`
    -- kills it.
    simpa [Candidate, n] using
      fixed_constituent_determinant_subgroup_residue_class_pow_card_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift c
  have hu_class :
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) u) =
        (fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c)⁻¹ := by
    -- The normalized factor contributes the trivial class, so only the inverse correction class
    -- remains in the quotient.
    calc
      QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) u) =
          QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) normalizedDet) *
            (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) corrDet))⁻¹ := by
              simp [u, map_mul]
      _ =
          (fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c)⁻¹ := by
              rw [hnormalized_class_one]
              simp [fixed_constituent_determinant_subgroup_residue_class, c, corrDet]
  -- Raising the quotient class of `u` to `|Candidate|` kills the remaining inverse correction
  -- class.
  calc
    (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) u)) ^ n =
        ((fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c)⁻¹) ^ n := by
            rw [hu_class]
    _ =
        ((fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c) ^ n)⁻¹ := by
            simp
    _ = 1 := by
          simp [hcorr_class_pow_one]

/-- Helper for Theorem 17-17.6-1: the `|Candidate|`-power of LinearRepresentations_Serre_1977's normalized correction ratio
is already a literal `d`-th power in `Aˣ`. This isolates the quotient-torsion lifting step from
the still-open principal-unit rigidity argument in the determinant-normalization branch. -/
private theorem normalized_kernel_correction_ratio_pow_candidate_order_is_dth_power
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let corrDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    ∃ a : Aˣ, a ^ d = (normalizedDet * corrDet⁻¹) ^ n := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let u : Aˣ := normalizedDet * corrDet⁻¹
  have hclass_pow_one :
      (QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) u)) ^ n = 1 := by
    -- This is exactly the quotient-torsion relation already established for the normalized
    -- correction ratio.
    simpa [Candidate, n, d, Qd, corrDet, normalizedDet, u] using
      normalized_kernel_correction_ratio_residue_class_pow_card_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hres_dth_power :
      ∃ b : kˣ, Units.map (IsLocalRing.residue A) (u ^ n) = b ^ d := by
    have hclass_one :
        QuotientGroup.mk' Qd (Units.map (IsLocalRing.residue A) (u ^ n)) = 1 := by
      -- Move the power inside the quotient representative before unpacking membership in `Qd`.
      simpa [map_pow] using hclass_pow_one
    have hu_mem_Qd :
        Units.map (IsLocalRing.residue A) (u ^ n) ∈ Qd := by
      -- Triviality in the quotient is equivalent to literal membership in the `d`-th-power
      -- subgroup.
      exact (QuotientGroup.eq_one_iff (Units.map (IsLocalRing.residue A) (u ^ n))).mp hclass_one
    rcases hu_mem_Qd with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    -- Membership in the range of `powMonoidHom d` is the same as being a literal `d`-th power.
    simpa [Qd, powMonoidHom] using hb.symm
  have hdcop : Nat.Coprime p d := by
    -- The fixed lifted constituent has degree prime to `p`.
    simpa [d] using
      fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  -- Lift the quotient `d`-th power witness from the residue field to an actual unit in `A`.
  simpa [u, normalizedDet, corrDet, d] using
    exists_dth_root_of_unit_of_residue_eq_dth_power
      (A := A) (p := p) hp hdcop hres_dth_power

/-- Helper for Theorem 17-17.6-1: the determinant of LinearRepresentations_Serre_1977's normalized representative is
exactly the determinant of the same-fiber ratio between the raw quotient-out representative and
the chosen Hall-kernel correction. This freezes the source-faithful comparison object before the
remaining literal-membership step in the determinant subgroup `C`. -/
private theorem normalized_kernel_representative_eq_raw_correction_ratio
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      fixed_constituent_transport_fiber_ratio
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  -- Route correction: read LinearRepresentations_Serre_1977's normalized representative directly as the same-fiber ratio
  -- `raw / corr`, instead of hiding it behind the later determinant bookkeeping.
  apply Representation.Equiv.toLinearEquiv_injective
  ext v
  simp [normalized_kernel_representative, raw, corr, x, G2, pi,
    fixed_constituent_transport_fiber_ratio, fixed_constituent_transport_fiber_reindex,
    fixed_constituent_transport_fiber_comp, fixed_constituent_transport_fiber_inv,
    normalized_kernel_representative_correction_val_eq_out_proj]

/-- Helper for Theorem 17-17.6-1: after identifying the normalized representative with LinearRepresentations_Serre_1977's
kernel scalar `kernelScalar q`, multiplying the Hall-kernel correction by that scalar literally
recovers the raw quotient-out representative. This is the source-level collapse from the
comparison object `raw / corr` to the actual scalar in `U₁ = Aˣ`. -/
private theorem raw_eq_kernel_scalar_adjusted_hall_kernel_correction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    let kernelScalar :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
    fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I kernelScalar)
        corr =
      raw := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  let kernelScalar :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hratio :
      fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr =
        scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I kernelScalar := by
    -- The normalized representative is both the literal ratio `raw / corr` and the scalar point
    -- `(1, kernelScalar q)`, so the two kernel-fiber elements are equal.
    calc
      fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr =
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 := by
            symm
            simpa [G2, pi, x, raw, corr] using
              normalized_kernel_representative_eq_raw_correction_ratio
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
      _ =
        scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I kernelScalar := by
            simpa [kernelScalar] using
              normalized_kernel_representative_eq_scalar_fiber
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                hTransportLift q
  -- Compose the identified kernel ratio with `corr`; the inverse in the ratio cancels and
  -- returns the original raw representative.
  apply Representation.Equiv.toLinearEquiv_injective
  ext v
  have hcomp :
      (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar)
          corr).toLinearMap =
        raw.toLinearMap := by
    calc
      (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar)
          corr).toLinearMap =
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr)
          corr).toLinearMap := by
            rw [hratio]
      _ = raw.toLinearMap := by
            simpa [fixed_constituent_transport_fiber_comp] using
              fixed_constituent_transport_fiber_ratio_comp_right
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr
  exact LinearMap.congr_fun hcomp v

/-- Helper for Theorem 17-17.6-1: the raw quotient-out representative over the Hall-kernel
correction has determinant equal to the correction determinant times LinearRepresentations_Serre_1977's scalar
`kernelScalar(q)^d`. This is the literal determinant identity coming from
`raw = (kernelScalar q) • id ∘ corr`, and it replaces the previously over-strong attempt to
identify the correction determinant itself with the scalar power. -/
private theorem raw_hall_kernel_det_eq_correction_det_mul_kernel_scalar_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    let kernelScalar :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
        kernelScalar ^ Module.finrank A P_S := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  let kernelScalar :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hraw :
      fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar)
          corr =
        raw := by
    -- This is the already stabilized source-level identity `raw = (kernelScalar q) • id ∘ corr`.
    simpa [G2, pi, x, raw, corr, kernelScalar] using
      raw_eq_kernel_scalar_adjusted_hall_kernel_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hscalar :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar) =
        kernelScalar ^ Module.finrank A P_S := by
    -- The scalar factor lives in LinearRepresentations_Serre_1977's kernel fiber `U₁`, so its determinant is the literal
    -- `d`-th power of the scalar.
    simpa [kernelScalar] using
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) rfl
  -- Take determinants of `raw = (kernelScalar q) • id ∘ corr` and expand the scalar factor.
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar)
          corr) := by
            rw [hraw]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I kernelScalar) := by
            simpa using
              fixed_constituent_transport_fiber_det_comp
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                (scalar_transport_fiber_one
                  (A := A) (G := G) (I := I) ρA_I kernelScalar)
                corr
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
        kernelScalar ^ Module.finrank A P_S := by
            rw [hscalar]

/-- Helper for Theorem 17-17.6-1: the determinant of LinearRepresentations_Serre_1977's normalized representative is
exactly the determinant of the same-fiber ratio between the raw quotient-out representative and
the chosen Hall-kernel correction. This freezes the source-faithful comparison object before the
remaining literal-membership step in the determinant subgroup `C`. -/
private theorem normalized_kernel_representative_det_eq_raw_correction_ratio_det
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr) := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  have hnormalized :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr)⁻¹ := by
    -- Repackage the existing raw-times-correction-inverse determinant formula in the same-fiber
    -- notation that LinearRepresentations_Serre_1977 uses for the comparison ratio.
    simpa [raw, corr, G2, pi, x] using
      normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hratio :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr) := by
    -- The raw point and the correction point lie in the same fiber over `x`, so their quotient
    -- in that fiber is LinearRepresentations_Serre_1977's kernel ratio.
    exact
      fixed_constituent_transport_fiber_det_eq_ratio_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr
  -- Cancel the correction determinant to identify the normalized determinant with the ratio
  -- determinant itself.
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr)⁻¹ := by
            exact hnormalized
    _ =
      (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr)) *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr)⁻¹ := by
            rw [hratio]
    _ =
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr) := by
            simp [mul_assoc]

/-- Helper for Theorem 17-17.6-1: for a kernel element `q ∈ N̄`, the raw quotient-out
representative and the canonical Hall-kernel correction over the same `x ∈ I` induce the same
reduced map on `S̄` up to a single scalar endomorphism. This isolates the last reduced-side
ambiguity in the determinant-normalization branch. -/
private theorem hall_kernel_comparison_reduction_smul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    ∃ c : k,
      red_S.comp raw.toLinearMap =
        (((c • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule).restrictScalars A).comp
          (red_S.comp corr.toLinearMap)) := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  let eRaw :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (x : G) raw
  let eCorr :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (x : G) corr
  let phi : Sbar.toRepresentation.Equiv Sbar.toRepresentation := eRaw.symm.trans eCorr
  have hphi :
      ((phi.toLinearMap.restrictScalars A).comp (red_S.comp corr.toLinearMap)) =
        red_S.comp raw.toLinearMap := by
    -- Compare `raw` and the Hall-kernel correction by inserting the two chosen reduction
    -- bridges into the same canonical transported map over `x`.
    calc
      ((phi.toLinearMap.restrictScalars A).comp (red_S.comp corr.toLinearMap)) =
        ((eRaw.symm.toLinearMap.restrictScalars A).comp
          (((eCorr.toLinearMap.restrictScalars A).comp red_S).comp corr.toLinearMap)) := by
            simp [phi, LinearMap.comp_assoc]
      _ =
        ((eRaw.symm.toLinearMap.restrictScalars A).comp
          (((transportedSubrepresentation_rep_equiv_local ρ Sbar (x : G)).toLinearMap
            .restrictScalars A).comp red_S)) := by
              rw [fixed_constituent_transport_fiber_reduction_equiv_spec
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                hTransportLift (x : G) corr]
      _ =
        ((eRaw.symm.toLinearMap.restrictScalars A).comp
          (((eRaw.toLinearMap.restrictScalars A).comp red_S).comp raw.toLinearMap)) := by
              rw [fixed_constituent_transport_fiber_reduction_equiv_spec
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                hTransportLift (x : G) raw]
      _ = red_S.comp raw.toLinearMap := by
            simp [LinearMap.comp_assoc]
  obtain ⟨c, hc⟩ :=
    fixed_constituent_reduced_scalar_id_surjective
      I ρ Sbar hSbar_irred phi.toIntertwiningMap
  have hphi_scalar :
      phi.toLinearMap = c • LinearMap.id := by
    -- Schur's lemma turns the residual reduced-side ambiguity into a single scalar factor.
    simpa using
      congrArg
        (fun f : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation =>
          (f : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule))
        hc
  refine ⟨c, ?_⟩
  -- Rewrite the comparison equivalence as a scalar endomorphism of `S̄`.
  calc
    red_S.comp raw.toLinearMap =
      ((phi.toLinearMap.restrictScalars A).comp (red_S.comp corr.toLinearMap)) := by
        simpa using hphi.symm
    _ =
      (((c • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule).restrictScalars A).comp
        (red_S.comp corr.toLinearMap)) := by
          rw [hphi_scalar]

/-- Helper for Theorem 17-17.6-1: the reduced Hall-kernel comparison scalar is automatically a
unit of `k`, and one may choose an upstairs unit lift of it in `A`. This isolates the source
bridge from the reduced Schur scalar ambiguity to the scalar-adjusted transport-fiber correction
used in LinearRepresentations_Serre_1977's normalization argument. -/
private theorem hall_kernel_comparison_scalar_unit_lift_exists
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let x :=
      normalized_kernel_representative_correction
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
    let raw :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (x : G) := by
        simpa [G2, pi, x] using q.1.out.1.2
    let corr :=
      fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
    ∃ cbar : kˣ, ∃ a : Aˣ,
      red_S.comp raw.toLinearMap =
        ((((cbar : k) • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule)
          .restrictScalars A).comp
          (red_S.comp corr.toLinearMap)) ∧
      Units.map (IsLocalRing.residue A) a = cbar := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  obtain ⟨c, hc⟩ :=
    hall_kernel_comparison_reduction_smul
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hred_surj : Function.Surjective red_S := by
    -- The fixed constituent reduction map is surjective, so a zero comparison scalar would force
    -- the impossible conclusion `red_S = 0`.
    exact fixed_constituent_reduction_surjective (A := A) (H := I) hred
  have hc_ne_zero : c ≠ 0 := by
    intro hc_zero
    have hraw_zero : red_S.comp raw.toLinearMap = 0 := by
      simpa [hc_zero] using hc
    have hred_zero : red_S = 0 := by
      ext y
      obtain ⟨z, rfl⟩ := raw.toLinearEquiv.surjective y
      have hy :=
        congrArg (fun f : P_S →ₗ[A] Sbar.toSubmodule => f z) hraw_zero
      simpa [LinearMap.comp_apply] using hy
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    letI : Nontrivial Sbar.toSubmodule := by
      infer_instance
    obtain ⟨y, hy⟩ := exists_ne (0 : Sbar.toSubmodule)
    obtain ⟨z, hz⟩ := hred_surj y
    have : y = 0 := by simpa [hred_zero] using hz
    exact hy this
  let cbar : kˣ := Units.mk0 c hc_ne_zero
  obtain ⟨a, ha⟩ :=
    surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A))
      (by infer_instance) cbar
  refine ⟨cbar, a, ?_, ha⟩
  -- Replace the scalar from the reduced comparison by the corresponding residue-field unit.
  simpa [cbar] using hc

/-- Helper for Theorem 17-17.6-1: once the candidate subgroup is placed inside LinearRepresentations_Serre_1977's bounded
roots-of-unity owner, its cardinal is automatically prime to `p`. This packages the prime-to-`p`
exponent used in the remaining principal-unit upgrade. -/
private theorem scalar_transport_fiber_one_reduction_comp
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (a : Aˣ) :
    red_S.comp
        (scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I a).toLinearMap =
      ((((IsLocalRing.residue A (a : A)) •
            (LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule)).restrictScalars A).comp
        red_S) := by
  -- The scalar fiber element over `1` acts by the literal homothety `a • id`, so reduction
  -- simply applies the scalar residue to the fixed-constituent reduction map.
  ext x
  simp [scalar_transport_fiber_one, LinearMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: if two points of the same transport fiber differ on reduction
by the scalar `c`, then after multiplying the second point by any scalar lift `a` of `c`, the
two reduced maps coincide. This is the transport-stable bridge from LinearRepresentations_Serre_1977's reduced scalar
comparison to the identity-reduction input needed for the principal-unit step. -/
private theorem same_fiber_scalar_adjustment_has_equal_reduction
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    {s : G}
    (raw corr :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    {c : k} {a : Aˣ}
    (hcomparison :
      red_S.comp raw.toLinearMap =
        (((c • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule).restrictScalars A).comp
          (red_S.comp corr.toLinearMap)))
    (ha : IsLocalRing.residue A (a : A) = c) :
    red_S.comp raw.toLinearMap =
      red_S.comp
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I a)
          corr).toLinearMap := by
  -- Replace the reduced scalar `c` by the chosen lift `a`, then recognize the right-hand side as
  -- the reduction of the scalar-adjusted fiber point.
  calc
    red_S.comp raw.toLinearMap =
      (((c • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule).restrictScalars A).comp
        (red_S.comp corr.toLinearMap)) := hcomparison
    _ =
      ((((IsLocalRing.residue A (a : A)) •
            (LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule)).restrictScalars A).comp
          (red_S.comp corr.toLinearMap)) := by
            rw [← ha]
    _ =
      ((red_S.comp
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I a).toLinearMap).comp corr.toLinearMap) := by
            rw [scalar_transport_fiber_one_reduction_comp
              (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar) ρA_I red_S a]
            simp [LinearMap.comp_assoc]
    _ =
      red_S.comp
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I a)
          corr).toLinearMap := by
            ext x
            simp [fixed_constituent_transport_fiber_comp, LinearMap.comp_apply]

/-- Helper for Theorem 17-17.6-1: after correcting a same-fiber comparison by a scalar lift
`a : Aˣ`, the resulting ratio lies in the kernel fiber and its determinant reduces to `1`. This
packages the exact reduction-to-principal-unit bridge used in the normalized Hall-kernel branch. -/
private theorem same_fiber_ratio_det_residue_eq_one_of_scalar_adjustment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    {s : G}
    (raw corr :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    {c : k} {a : Aˣ}
    (hcomparison :
      red_S.comp raw.toLinearMap =
        (((c • LinearMap.id : Sbar.toSubmodule →ₗ[k] Sbar.toSubmodule).restrictScalars A).comp
          (red_S.comp corr.toLinearMap)))
    (ha : IsLocalRing.residue A (a : A) = c) :
    Units.map (IsLocalRing.residue A)
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            raw
            (fixed_constituent_transport_fiber_comp
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (scalar_transport_fiber_one
                (A := A) (G := G) (I := I) ρA_I a)
              corr))) = 1 := by
  let corrAdjusted :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a)
      corr
  have hred_eq :
      red_S.comp raw.toLinearMap = red_S.comp corrAdjusted.toLinearMap := by
    -- The scalar-adjusted correction now has exactly the same reduction as `raw`.
    simpa [corrAdjusted] using
      same_fiber_scalar_adjustment_has_equal_reduction
        (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S raw corr hcomparison ha
  -- Apply the existing equal-reduction ratio lemma to the adjusted comparison.
  simpa [corrAdjusted] using
    fixed_constituent_transport_fiber_ratio_det_residue_eq_one_of_equal_reduction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar raw corrAdjusted hred_eq

/-- Helper for Theorem 17-17.6-1: after scalar-adjusting the Hall-kernel correction by `a : Aˣ`,
the determinant of the resulting same-fiber ratio is the raw determinant discrepancy divided by
the extra scalar factor `a ^ dim(S)`. This isolates the determinant bookkeeping from the
principal-unit argument that follows. -/
private theorem scalar_adjusted_hall_kernel_ratio_det_eq_raw_discrepancy
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (raw corr :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (a : Aˣ) :
    let corrAdjusted :=
      fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I a)
        corr
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted) =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
          a ^ Module.finrank A P_S)⁻¹ := by
  let corrAdjusted :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a)
      corr
  have hdet_scalar :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (scalar_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I a) =
        a ^ Module.finrank A P_S := by
    -- The scalar correction lives in the kernel fiber `U₁`, so its determinant is the literal
    -- `d`-th power of the chosen unit.
    exact
      fixed_constituent_transport_kernel_det_eq_unit_pow
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) rfl
  have hdet_corrAdjusted :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
          a ^ Module.finrank A P_S := by
    -- The adjusted correction is the product of the original Hall-kernel correction and the
    -- scalar kernel element, so determinants multiply accordingly.
    simpa [corrAdjusted, hdet_scalar] using
      fixed_constituent_transport_fiber_det_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (scalar_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I a)
        corr
  have hratio :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted) := by
    -- Compare the raw point with the scalar-adjusted correction inside the same fiber over `s`.
    exact
      fixed_constituent_transport_fiber_det_eq_ratio_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted
  -- Solve the determinant identity once by cancelling the adjusted correction determinant.
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted) =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted)⁻¹ := by
            calc
              fixed_constituent_transport_fiber_det
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                  (fixed_constituent_transport_fiber_ratio
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted) =
                (fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted *
                  fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                    (fixed_constituent_transport_fiber_ratio
                      (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corrAdjusted)) *
                  (fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted)⁻¹ := by
                      simp [mul_assoc, mul_comm, mul_left_comm]
              _ =
                fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
                  (fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) corrAdjusted)⁻¹ := by
                      rw [← hratio]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr *
          a ^ Module.finrank A P_S)⁻¹ := by
            rw [hdet_corrAdjusted]

/-- Helper for Theorem 17-17.6-1: once the candidate subgroup is placed inside LinearRepresentations_Serre_1977's bounded
roots-of-unity owner, its cardinal is automatically prime to `p`. This packages the prime-to-`p`
exponent used in the remaining principal-unit upgrade. -/
private theorem candidate_order_coprime_of_bounded_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    Nat.Coprime p
      (Nat.card
        (fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)) := by
  -- This is exactly the prime-to-`p` half of the bounded candidate-owner package.
  simpa using
    (candidate_subgroup_cyclic_and_coprime_of_bounded_containment
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      hcandidate_le).2

/-- Helper for Theorem 17-17.6-1: the Hall-kernel correction determinant already lies in
LinearRepresentations_Serre_1977's determinant subgroup `C`, so its `|Candidate|`-th power stays in `C`. This isolates the
literal subgroup-membership half of the remaining normalization argument. -/
private theorem normalized_kernel_representative_correction_det_pow_candidate_order_mem_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let corrDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
    corrDet ^ n ∈ C := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let c : C := ⟨corrDet,
    normalized_kernel_representative_correction_det_mem_determinant_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q⟩
  -- Once the correction determinant is named as an element of `C`, closure under powers is
  -- immediate.
  simpa [Candidate, n, C, corrDet, c] using C.pow_mem c.2 n

/-- Helper for Theorem 17-17.6-1: after freezing LinearRepresentations_Serre_1977's normalized kernel representative and the
chosen Hall-kernel correction, the remaining determinant discrepancy
`u = normalizedDet * corrDet⁻¹` already satisfies the two power statements isolated earlier:
`u ^ |Candidate|` is a `d`-th power, and `corrDet ^ |Candidate|` lies in `C`. This packages the
closed algebraic part of the determinant-normalization route before the final principal-unit
upgrade. -/
private theorem hall_kernel_scalar_discrepancy_power_package
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let corrDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    ∃ u a : Aˣ,
      normalizedDet = corrDet * u ∧
      a ^ d = u ^ n ∧
      corrDet ^ n ∈ C := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let u : Aˣ := normalizedDet * corrDet⁻¹
  obtain ⟨a, ha⟩ :=
    normalized_kernel_correction_ratio_pow_candidate_order_is_dth_power
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hcorr_pow_mem :
      corrDet ^ n ∈ C := by
    -- The chosen Hall-kernel correction already contributes a determinant in `C`, so taking the
    -- `|Candidate|`-th power stays inside `C`.
    simpa [Candidate, n, C, corrDet] using
      normalized_kernel_representative_correction_det_pow_candidate_order_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  refine ⟨u, a, ?_, ?_, hcorr_pow_mem⟩
  · -- The discrepancy unit is defined exactly so that `normalizedDet = corrDet * u`.
    simp [u, normalizedDet, corrDet, mul_assoc]
  · -- The existing quotient-torsion theorem already identifies `u ^ |Candidate|` with a
    -- literal `d`-th power in `Aˣ`.
    simpa [u, Candidate, n, d, normalizedDet, corrDet] using ha

/-- Helper for Theorem 17-17.6-1: after lifting the reduced Schur scalar comparing the raw
kernel representative with the Hall-kernel correction, the adjusted normalized determinant is
already a principal unit. This is the source-faithful reduction-side conclusion available before
identifying that scalar correction with LinearRepresentations_Serre_1977's final discrepancy unit. -/
private theorem hall_kernel_normalized_det_scalar_adjustment_residue_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    let d := Module.finrank A P_S
    ∃ a : Aˣ, Units.map (IsLocalRing.residue A) (normalizedDet * (a ^ d)⁻¹) = 1 := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let x :=
    normalized_kernel_representative_correction
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  let raw :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (x : G) := by
      simpa [G2, pi, x] using q.1.out.1.2
  let corr :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) corr
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let d := Module.finrank A P_S
  obtain ⟨cbar, a, hcomparison, ha_unit⟩ :=
    hall_kernel_comparison_scalar_unit_lift_exists
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have ha : IsLocalRing.residue A (a : A) = (cbar : k) := by
    -- Forgetting the unit wrapper turns the chosen lift equation into the scalar equality needed
    -- by the transport-fiber adjustment lemma.
    exact congrArg (fun z : kˣ ↦ (z : k)) ha_unit
  have hres_adjusted :
      Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              raw
              (fixed_constituent_transport_fiber_comp
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                (scalar_transport_fiber_one
                  (A := A) (G := G) (I := I) ρA_I a)
                corr))) = 1 := by
    -- After scalar adjustment, the two same-fiber points have identical reduction, so the ratio
    -- determinant is a principal unit.
    simpa [raw, corr, x, G2, pi] using
      same_fiber_ratio_det_residue_eq_one_of_scalar_adjustment
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar raw corr hcomparison ha
  have hnormalized :
      normalizedDet =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
          corrDet⁻¹ := by
    -- Rewrite the normalized determinant using the raw representative and the chosen
    -- Hall-kernel correction over the same `x ∈ I`.
    simpa [normalizedDet, corrDet, raw, corr, x, G2, pi] using
      normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet_adjusted :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            raw
            (fixed_constituent_transport_fiber_comp
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (scalar_transport_fiber_one
                (A := A) (G := G) (I := I) ρA_I a)
              corr)) =
        normalizedDet * (a ^ d)⁻¹ := by
    -- The adjusted ratio determinant is exactly the normalized determinant with the lifted scalar
    -- correction factored off.
    calc
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            raw
            (fixed_constituent_transport_fiber_comp
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (scalar_transport_fiber_one
                (A := A) (G := G) (I := I) ρA_I a)
              corr)) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
          (corrDet * a ^ d)⁻¹ := by
            simpa [corrDet, corr, raw, x, G2, pi, d] using
              scalar_adjusted_hall_kernel_ratio_det_eq_raw_discrepancy
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw corr a
      _ =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) raw *
          corrDet⁻¹ * (a ^ d)⁻¹ := by
            simp [mul_assoc, mul_comm, mul_left_comm]
      _ = normalizedDet * (a ^ d)⁻¹ := by
            rw [hnormalized]
            ac_rfl
  refine ⟨a, ?_⟩
  -- Rewrite the adjusted ratio determinant into the normalized determinant form promised in the
  -- statement.
  simpa [normalizedDet, d, hdet_adjusted] using hres_adjusted

/-- Helper for Theorem 17-17.6-1: package the scalar-adjusted normalized determinant into the
exact principal-unit input shape used in the Hall-kernel branch. This isolates the only remaining
source-faithful algebraic gap between the adjusted-ratio comparison and LinearRepresentations_Serre_1977's literal
discrepancy unit `u`. -/
private theorem hall_kernel_adjusted_normalized_det_power_mem_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    ∃ a : Aˣ,
      Units.map (IsLocalRing.residue A) (normalizedDet * (a ^ d)⁻¹) = 1 ∧
      (normalizedDet * (a ^ d)⁻¹) ^ n ∈ C := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let a : Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet :
      normalizedDet = a ^ d := by
    -- Route correction: use the already normalized scalar point in LinearRepresentations_Serre_1977's kernel fiber.
    -- The determinant of the normalized representative is literally the `d`-th power of
    -- `kernelScalar(q)`, so the adjusted unit can be chosen to be `1` on the nose.
    simpa [normalizedDet, a, d] using
      normalized_kernel_representative_det_eq_kernel_scalar_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  refine ⟨a, ?_, ?_⟩
  · -- After rewriting by the scalar form of the normalized representative, the adjusted unit is
    -- literally `1`, so its reduction is `1`.
    rw [hdet]
    simp
  · -- The same rewrite makes the `|Candidate|`-th power equal to `1`, which belongs to `C`.
    rw [hdet]
    simpa using C.one_mem

/-- Helper for Theorem 17-17.6-1: after rewriting the normalized kernel representative by its
literal scalar coordinate `kernelScalar(q)`, the adjusted determinant
`det(normalizedRepresentative q) * kernelScalar(q)^{-d}` is already `1`. This freezes the
normalized side of LinearRepresentations_Serre_1977's Hall-kernel comparison before the final correction-determinant
identification. -/
private theorem hall_kernel_adjusted_normalized_det_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let d := Module.finrank A P_S
    let normalizedDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
    let a :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
    normalizedDet * (a ^ d)⁻¹ = 1 := by
  let d := Module.finrank A P_S
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let a :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet : normalizedDet = a ^ d := by
    -- Route correction: once the normalized representative is rewritten as LinearRepresentations_Serre_1977's scalar point
    -- `(1, kernelScalar(q) • id)`, its determinant is literally the expected `d`-th power.
    simpa [normalizedDet, a, d] using
      normalized_kernel_representative_det_eq_kernel_scalar_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  -- Substitute the scalar determinant formula; the adjusted normalized factor cancels on the nose.
  rw [hdet]
  simp

/-- Helper for Theorem 17-17.6-1: after rewriting LinearRepresentations_Serre_1977's normalized determinant as the literal
scalar power `kernelScalar(q)^d`, the comparison-scalar adjustment still produces a principal
unit. This records the reduction-side statement in the source language actually attached to the
kernel scalar. -/
private theorem hall_kernel_scalar_power_adjustment_residue_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let d := Module.finrank A P_S
    let kernelScalar :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
    ∃ a : Aˣ, Units.map (IsLocalRing.residue A) (kernelScalar ^ d * (a ^ d)⁻¹) = 1 := by
  let d := Module.finrank A P_S
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let kernelScalar :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  obtain ⟨a, ha⟩ :=
    hall_kernel_normalized_det_scalar_adjustment_residue_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet : normalizedDet = kernelScalar ^ d := by
    -- This is the scalar determinant formula for the normalized representative.
    simpa [normalizedDet, kernelScalar, d] using
      normalized_kernel_representative_det_eq_kernel_scalar_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  refine ⟨a, ?_⟩
  -- Rewrite the normalized determinant to the literal scalar power before using the already
  -- established comparison-scalar principal-unit statement.
  calc
    Units.map (IsLocalRing.residue A) (kernelScalar ^ d * (a ^ d)⁻¹) =
      Units.map (IsLocalRing.residue A) (normalizedDet * (a ^ d)⁻¹) := by
        rw [hdet]
    _ = 1 := by
          simpa [normalizedDet, d] using ha

/-- Helper for Theorem 17-17.6-1: after rewriting the normalized determinant as
`kernelScalar(q)^d`, the quotient-level torsion statement becomes a literal `d`-th-power witness
for the discrepancy ratio `kernelScalar(q)^d * corrDet⁻¹`. This isolates the exact algebraic
information already proved on the scalar side before the remaining upgrade to membership in `C`. -/
private theorem hall_kernel_scalar_ratio_pow_candidate_order_is_dth_power
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let n := Nat.card Candidate
    let d := Module.finrank A P_S
    let corrDet :=
      fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (normalized_kernel_representative_correction
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
    let kernelScalar :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
    ∃ a : Aˣ, a ^ d = (kernelScalar ^ d * corrDet⁻¹) ^ n := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  let normalizedDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (normalized_kernel_representative
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2
  let kernelScalar :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  obtain ⟨a, ha⟩ :=
    normalized_kernel_correction_ratio_pow_candidate_order_is_dth_power
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hdet : normalizedDet = kernelScalar ^ d := by
    -- This is the same scalar determinant computation, now reused in the quotient-torsion step.
    simpa [normalizedDet, kernelScalar, d] using
      normalized_kernel_representative_det_eq_kernel_scalar_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  refine ⟨a, ?_⟩
  -- The previously proved normalized-determinant torsion package becomes the literal scalar-ratio
  -- statement after this single rewrite.
  simpa [Candidate, n, d, corrDet, normalizedDet, kernelScalar, hdet] using ha

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's actual kernel invariant is that the scalar attached to a
normalized kernel representative already lies in the determinant root subgroup, i.e.
`kernelScalar(q)^d ∈ C`. This is the source-faithful replacement for the older over-strong route
that tried to identify the Hall-kernel correction determinant itself with that scalar power. -/
private theorem kernel_scalar_pow_mem_determinant_subgroup_of_candidate_order
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar)
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) ^
        Module.finrank A P_S ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let n := Nat.card Candidate
  let d := Module.finrank A P_S
  let corrDet :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative_correction
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q))
  obtain ⟨a_res, ha_res⟩ :=
    hall_kernel_scalar_power_adjustment_residue_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  obtain ⟨a_pow, ha_pow⟩ :=
    hall_kernel_scalar_ratio_pow_candidate_order_is_dth_power
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hncop :
      Nat.Coprime p n := by
    -- The candidate-order exponent is already known to be prime to `p`.
    simpa [Candidate, n] using
      candidate_order_coprime_of_bounded_containment
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        hcandidate_le
  -- Route correction: the open determinant-normalization frontier is now the literal source
  -- statement `kernelScalar(q)^d ∈ C`, not the stronger and likely false equality
  -- `corrDet = kernelScalar(q)^d`.
  -- TODO: the remaining blocker is now isolated to one exact correction-side bridge.
  -- The proved prefix already gives a comparison-scalar principal unit
  -- `ha_res : res(kernelScalar(q)^d * (a_res^d)⁻¹) = 1`,
  -- a literal `d`-th-power witness
  -- `ha_pow : a_pow^d = (kernelScalar(q)^d * corrDet⁻¹)^|Candidate|`,
  -- the correction-side subgroup membership `corrDet ^ |Candidate| ∈ C`, and the prime-to-`p`
  -- exponent bound `hncop`.
  -- What is still missing is a source-faithful comparison between the lifted comparison scalar
  -- `a_res` and the Hall-kernel correction determinant `corrDet`, strong enough to convert the
  -- `d`-th-power witness `ha_pow` into literal membership
  -- `(kernelScalar(q)^d * corrDet⁻¹)^|Candidate| ∈ C`.
  -- Once that exact bridge is available, `principal_unit_eq_one_of_power_mem_fixed_constituent_determinant_subgroup`
  -- applies to `u = kernelScalar(q)^d * corrDet⁻¹`, yielding `u = 1` and hence
  -- `kernelScalar(q)^d = corrDet ∈ C`.
  sorry

private theorem normalized_kernel_representative_det_mem_determinant_subgroup_of_candidate_order
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar)
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- Route correction: the determinant-membership theorem should consume LinearRepresentations_Serre_1977's literal scalar
  -- invariant `kernelScalar(q)^d ∈ C`, not the older discrepancy-unit equality route.
  rw [normalized_kernel_representative_det_eq_kernel_scalar_pow
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
  exact
    kernel_scalar_pow_mem_determinant_subgroup_of_candidate_order
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      hcandidate_le q

/-- Helper for Theorem 17-17.6-1: the normalized representative of a kernel class in `N̄`
already lies in LinearRepresentations_Serre_1977's literal determinant cover once the determinant upgrade is established. This
packages the source-faithful pivot requested by the current plan. -/
private theorem normalized_kernel_representative_mem_literal_determinant_cover_of_candidate_order
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar)
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    (normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1 ∈
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I := by
  -- Literal determinant-cover membership is definitionally the same as determinant membership in
  -- `C`, so this is exactly the normalized-determinant theorem repackaged at the source object.
  change
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (normalized_kernel_representative
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  exact
    normalized_kernel_representative_det_mem_determinant_subgroup_of_candidate_order
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      hcandidate_le q

/-- Helper for Theorem 17-17.6-1: once the literal inclusion
`kernelScalar(q) ^ d ∈ C` is available, the rest of LinearRepresentations_Serre_1977's finite-kernel package is a formal
transport along the injective scalar map `N̄ → Aˣ`. This keeps the remaining blocker confined to
the single upstairs membership step. -/
private theorem kernel_scalar_mem_determinant_root_subgroup_local
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let d := Module.finrank A P_S
    let S : Subgroup Aˣ :=
      { carrier := { a | a ^ d ∈ C }
        one_mem' := by
          simpa using C.one_mem
        mul_mem' := by
          intro a b ha hb
          simpa [mul_pow] using C.mul_mem ha hb
        inv_mem' := by
          intro a ha
          simpa [inv_pow] using C.inv_mem ha }
    let kernelScalar : Nbar →* Aˣ :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ q : Nbar, kernelScalar q ∈ S := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let d := Module.finrank A P_S
  let S : Subgroup Aˣ :=
    { carrier := { a | a ^ d ∈ C }
      one_mem' := by
        simpa using C.one_mem
      mul_mem' := by
        intro a b ha hb
        simpa [mul_pow] using C.mul_mem ha hb
      inv_mem' := by
        intro a ha
        simpa [inv_pow] using C.inv_mem ha }
  let kernelScalar : Nbar →* Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  intro q
  -- Once LinearRepresentations_Serre_1977's scalar power is known to lie in `C`, membership in the root subgroup `S` is
  -- immediate by unfolding the definition of `S`.
  change kernelScalar q ^ d ∈ C
  simpa [G2, I2, pi2, Nbar, C, d, kernelScalar] using
    kernel_scalar_pow_mem_determinant_subgroup_of_candidate_order
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      hcandidate_le q

/-- Helper for Theorem 17-17.6-1: once the literal inclusion
`kernelScalar(q) ^ d ∈ C` is available, the rest of LinearRepresentations_Serre_1977's finite-kernel package is a formal
transport along the injective scalar map `N̄ → Aˣ`. This keeps the remaining blocker confined to
the single upstairs membership step. -/
private theorem kernel_subgroup_cyclic_and_coprime_of_bounded_generator_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    IsCyclic Nbar ∧ Nat.Coprime p (Nat.card Nbar) :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let d := Module.finrank A P_S
  let S : Subgroup Aˣ :=
    { carrier := { a | a ^ d ∈ C }
      one_mem' := by
        simpa using C.one_mem
      mul_mem' := by
        intro a b ha hb
        simpa [mul_pow] using C.mul_mem ha hb
      inv_mem' := by
        intro a ha
        simpa [inv_pow] using C.inv_mem ha }
  let kernelScalar : Nbar →* Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hkernelScalar_injective : Function.Injective kernelScalar := by
    -- The normalized scalar already remembers the full kernel class in `N̄`.
    simpa [kernelScalar, Nbar, G2, I2, pi2] using
      kernel_scalar_unit_injective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hCcop :
      Nat.Coprime p (Nat.card C) := by
    -- The determinant subgroup is a finite quotient of the Hall kernel `I`.
    simpa [C] using
      fixed_constituent_determinant_subgroup_coprime
        (A := A) (G := G) (I := I) hIcop ρA_I
  have hdcop : Nat.Coprime p d := by
    -- The degree of the lifted fixed constituent is already known to be prime to `p`.
    simpa [d] using
      fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hS_cyclic_coprime : IsCyclic S ∧ Nat.Coprime p (Nat.card S) := by
    -- Once LinearRepresentations_Serre_1977's root subgroup is named explicitly, its cyclic prime-to-`p` nature is
    -- independent of the kernel package itself.
    letI : Finite C := by
      exact finite_of_card_ne_zero (Nat.Coprime.ne_zero_right hCcop)
    simpa [S, C, d] using
      determinant_root_subgroup_cyclic_and_coprime
        (p := p) (A := A) hp C hCcop hdcop
  have hkernelScalar_mem_S :
      ∀ q : Nbar, kernelScalar q ∈ S := by
    -- Route correction: the remaining source-level task is no longer phrased as a bare quotient
    -- cancellation. It has been refactored into literal membership of the normalized
    -- representative in the determinant cover, after which the scalar conclusion is formal.
    simpa [G2, I2, pi2, Nbar, C, d, S, kernelScalar] using
      kernel_scalar_mem_determinant_root_subgroup_local
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift hcandidate_le
  let kernelScalarS : Nbar →* S :=
    MonoidHom.codRestrict kernelScalar S hkernelScalar_mem_S
  constructor
  · -- After codomain restriction, cyclicity transports from LinearRepresentations_Serre_1977's root subgroup to `N̄`.
    exact isCyclic_of_injective kernelScalarS <| by
      intro q₁ q₂ hq
      exact hkernelScalar_injective <| congrArg Subtype.val hq
  · -- The same injective comparison identifies `N̄` with a subgroup of the same prime-to-`p`
    -- finite cyclic group.
    have hcard_eq : Nat.card Nbar = Nat.card kernelScalarS.range := by
      exact Nat.card_congr (MonoidHom.ofInjective kernelScalarS <| by
        intro q₁ q₂ hq
        exact hkernelScalar_injective <| congrArg Subtype.val hq).toEquiv
    have hrange_coprime :
        Nat.Coprime p (Nat.card kernelScalarS.range) := by
      exact hS_cyclic_coprime.2.of_dvd_right kernelScalarS.range.card_subgroup_dvd_card
    rw [hcard_eq]
    exact hrange_coprime

-- Route correction: the quotient module `τ` is now built from an explicit upstairs `G₂`-action.
-- The next declarations isolate that action, its group law, and the Hall-kernel descent before
-- returning to the quotient representation itself.
/-- Helper for Theorem 17-17.6-1: the canonical chosen-section operator
`v ↦ ρ(s)(f((transportedSubrepresentation_rep_equiv_local ρ S̄ s).symm v))`
already lands in the transported multiplicity space. This isolates the genuine source-faithful
closure step before the arbitrary fiber correction is inserted. -/
private theorem fixed_isotypic_cover_section_action_postcompose_precompose_isIntertwining
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :
    (((ρ s).comp
        ((f : Sbar.toSubmodule →ₗ[k] V).comp
          (transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm.toLinearMap)).IsIntertwiningMap
      (transportedSubrepresentation ρ Sbar s).toRepresentation
      (ρ.comp I.subtype) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro a v
  -- First move the transported `I`-action back across the canonical transported-source
  -- equivalence, where it becomes the conjugated action on `S̄`.
  have hsource :
      (transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm
          (((transportedSubrepresentation ρ Sbar s).toRepresentation a) v) =
        ((Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom) a)
          ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v) := by
    simpa using
      LinearMap.congr_fun
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm.isIntertwining' a) v
  -- Then use that `f` is already `I`-equivariant on `S̄`, now evaluated at the conjugated
  -- source element coming from the transported constituent.
  have hf :
      f (((Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom) a)
          ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v)) =
        ((ρ.comp I.subtype).comp (MulAut.conjNormal s⁻¹).toMonoidHom) a
          (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v)) := by
    simpa using
      LinearMap.congr_fun
        (f.isIntertwining' ((MulAut.conjNormal s⁻¹) a))
        ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v)
  -- Finally push the conjugated target action back to the ordinary one by the literal ambient
  -- operator `ρ s`.
  calc
    ((ρ s).comp
        ((f : Sbar.toSubmodule →ₗ[k] V).comp
          (transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm.toLinearMap))
        (((transportedSubrepresentation ρ Sbar s).toRepresentation a) v) =
      ρ s
        (f (((Sbar.toRepresentation.comp (MulAut.conjNormal s⁻¹).toMonoidHom) a)
          ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v))) := by
            simp [LinearMap.comp_apply, hsource]
    _ =
      ρ s
        (((ρ.comp I.subtype).comp (MulAut.conjNormal s⁻¹).toMonoidHom) a
          (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v))) := by
            rw [hf]
    _ =
      ρ (s * (((MulAut.conjNormal s⁻¹) a : I)))
        (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v)) := by
            simpa using
              (LinearMap.congr_fun
                (ρ.map_mul s (((MulAut.conjNormal s⁻¹) a : I)))
                (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v))).symm
    _ =
      ρ ((a : G) * s)
        (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v)) := by
            simp [MulAut.conjNormal_apply, mul_assoc]
    _ =
      (ρ.comp I.subtype) a
        (((ρ s).comp
          ((f : Sbar.toSubmodule →ₗ[k] V).comp
            (transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm.toLinearMap)) v) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun
                (ρ.map_mul (a : G) s)
                (f ((transportedSubrepresentation_rep_equiv_local ρ Sbar s).symm v))

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's first missing object in the fixed-constituent branch is
the explicit upstairs operator of a cover element `g ∈ G₂` on the multiplicity space
`F = Hom^I(S̄, V)`. Naming it separately keeps the transport/coercion frontier out of the quotient
construction `τ`. -/
private noncomputable def fixed_isotypic_cover_section_action_linearEquiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  -- Route correction: this is LinearRepresentations_Serre_1977's chosen-section operator on `Hom^I(S̄, V)` before the
  -- same-fiber source correction for an arbitrary lift in `U_s` is inserted.
  -- TODO: the canonical closure lemma above now proves the source-faithful transported operator
  -- lands in `Hom^I(sS̄, V)`. What remains is to compare the chosen comparison `hTransport s`
  -- against that canonical transport, package the resulting map and its inverse as a linear
  -- equivalence, and then transport it back to `Hom^I(S̄, V)` as planned.
  sorry

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's first missing object in the fixed-constituent branch is
the explicit upstairs operator of a cover element `g ∈ G₂` on the multiplicity space
`F = Hom^I(S̄, V)`. Naming it separately keeps the transport/coercion frontier out of the quotient
construction `τ`. -/
private noncomputable def fixed_isotypic_cover_action_linearEquiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    G2 →
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
        fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fun g ↦
    -- Route correction: follow LinearRepresentations_Serre_1977's source-faithful factorization. First apply the chosen
    -- section action over `g.1.1`, then remove the discrepancy between the arbitrary fiber
    -- component `g.1.2` and the chosen section by the inverse source-correction operator.
    (fixed_isotypic_cover_section_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g.1.1).trans
      ((fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1.1 g.1.2).symm)

/-- Helper for Theorem 17-17.6-1: once the explicit upstairs operator is named, the only group-law
data needed to build LinearRepresentations_Serre_1977's cover representation is the normalization at `1`. This keeps the
representation packaging independent of the later quotient descent. -/
private theorem fixed_isotypic_cover_action_toLinearMap_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (fixed_isotypic_cover_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G2)).toLinearMap =
      LinearMap.id := by
  -- Route correction: the quotient module `τ` should be built only after the upstairs `G₂`-action
  -- is frozen. The remaining work here is exactly the identity case of that action.
  sorry

/-- Helper for Theorem 17-17.6-1: after the identity case is split off, the remaining coherence
for the upstairs action is the literal multiplication rule on `G₂`. This isolates the cocycle
frontier from the quotient package. -/
private theorem fixed_isotypic_cover_action_toLinearMap_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ g h : G2,
      (fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (g * h)).toLinearMap =
        ((fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift h)
          .toLinearMap).comp
          ((fixed_isotypic_cover_action_linearEquiv
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift g)
            .toLinearMap) := by
  -- Route correction: the multiplication law is now the isolated transport/composition blocker,
  -- rather than being buried inside the quotient representation hole.
  sorry

/-- Helper for Theorem 17-17.6-1: once the operator and its group law are separated out, LinearRepresentations_Serre_1977's
upstairs cover action on `F = Hom^I(S̄, V)` is an ordinary representation of `G₂`. This freezes
the pre-quotient object before proving that `I₂` acts trivially. -/
private noncomputable def fixed_isotypic_cover_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation k G2 (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  { toFun := fun g ↦
      (fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g).toLinearMap
    map_one' :=
      fixed_isotypic_cover_action_toLinearMap_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    map_mul' :=
      fixed_isotypic_cover_action_toLinearMap_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift }

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's Hall-kernel subgroup `I₂ ≤ G₂` should act trivially on
the upstairs multiplicity-space representation before the quotient `τ` is defined. Isolating this
fact leaves `Representation.ofQuotient` as a purely formal step. -/
private theorem fixed_isotypic_cover_action_isTrivial_on_hall_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsTrivial (coverRep.comp I2.subtype) := by
  -- Route correction: Hall-kernel triviality is now a standalone source-level statement on the
  -- explicit upstairs action, exactly matching LinearRepresentations_Serre_1977's `I₂`-descent step.
  sorry

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's multiplicity space `F = Hom^I(S̄, V)` carries a natural
`G₂ / I₂`-action once the transport action of `G₂` on `S̄` and `V` is descended through the
embedded Hall kernel. This isolates the quotient-module construction `τ`. -/
private noncomputable def fixed_isotypic_multiplicity_space_quotient_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation k (G2 ⧸ I2) (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  -- Route correction: `τ` is now defined only after the explicit upstairs `G₂`-action and the
  -- Hall-kernel triviality statement are separated out. The quotient step itself is formal.
  coverRep.ofQuotient I2

/-- Helper for Theorem 17-17.6-1: LinearRepresentations_Serre_1977's quotient module `τ` on the multiplicity space is
irreducible because the isotypic decomposition identifies `V` with `S̄ ⊗ F` equivariantly for the
finite cover. This isolates the irreducibility transfer needed before lower-height recursion. -/
private theorem fixed_isotypic_multiplicity_space_quotient_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let tau :=
      fixed_isotypic_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    tau.IsIrreducible :=
  -- TODO: build the `G₂`-equivariant tensor-product isomorphism
  -- `S̄ ⊗ Hom^I(S̄, V) ≃ V`, then transfer irreducibility of `ρ` to `τ`.
  sorry

/-- Helper for Theorem 17-17.6-1: once the quotient-side multiplicity module `τ` is lifted, LinearRepresentations_Serre_1977
recovers a lift of `ρ` by tensoring with the fixed constituent lift, killing the central
prime-to-`p` kernel, and descending back from the finite cover to `G`. -/
private theorem descend_lift_of_fixed_constituent_tensor
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let tau :=
      fixed_isotypic_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    ∀ {P_tau : Type (max u v x)} (_ : AddCommGroup P_tau) (_ : Module A P_tau)
      (_ : Module.Free A P_tau) (_ : Module.Finite A P_tau)
      (ρA_tau : Representation A (G2 ⧸ I2) P_tau)
      (red_tau :
        P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar),
        IsResidueFieldLift tau ρA_tau red_tau →
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G P)
            (red : P →ₗ[A] V),
              IsResidueFieldLift ρ ρA red :=
  -- TODO: tensor the lift of `τ` with the fixed constituent lift `ρA_I`, transport the reduction
  -- through the `S̄ ⊗ F ≃ V` isomorphism, prove the central kernel acts trivially on the tensor
  -- lift, and descend along the quotient equivalence back to `G`.
  sorry

/-- Helper for Theorem 17-17.6-1: once the candidate determinant subgroup is placed inside the
bounded roots-of-unity owner `D̄`, the remaining work is the literal LinearRepresentations_Serre_1977 package
`G₂`, `I₂`, `N̄`, `τ`, and tensor descent. This keeps the final blocker separate from the already
formalized closure step. -/
private noncomputable def projective_extension_kernel_quotient_data_from_bounded_generator_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    ConstituentProjectiveExtensionQuotientData
      (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
  -- Route correction: the closure step into the bounded subgroup `D̄` is now isolated in
  -- `hcandidate_le`. What remains is the literal source packaging of the determinant-normalized
  -- total-space cover into `G₂`, `I₂`, `N̄`, the quotient action `τ`, and the tensor descent.
  -- The `G₁` carrier, its group law, and the projection hom `G₁ →* G` are now explicit in
  -- `fixed_constituent_transport_total_space_group` and
  -- `fixed_constituent_transport_total_space_proj_hom`; the generated subgroup `G₂` itself and
  -- the surjectivity of its restricted projection are now isolated in
  -- `fixed_constituent_generated_cover_subgroup` and
  -- `fixed_constituent_generated_cover_proj_surjective`. The remaining blocker starts exactly at
  -- quotienting by the embedded Hall kernel and then normalizing determinants inside that
  -- quotient cover.
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 :
      G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let quotientEquiv : ((G2 ⧸ I2) ⧸ Nbar) ≃* (G ⧸ I) :=
    generated_cover_kernel_quotient_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let hnormalize := generated_cover_kernel_has_normalized_representative
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hcandidate_cyclic_coprime :
      IsCyclic
          (fixed_constituent_projective_extension_candidate_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∧
        Nat.Coprime p
          (Nat.card
            (fixed_constituent_projective_extension_candidate_subgroup
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)) := by
    -- The bounded-exponent closure step is now completely finished on the candidate subgroup.
    exact
      candidate_subgroup_cyclic_and_coprime_of_bounded_containment
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        hcandidate_le
  let normalizedRepresentative : Nbar → G2 :=
    normalized_kernel_representative
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hnormalizedRepresentative_proj :
      ∀ q : Nbar, pi (normalizedRepresentative q) = 1 := by
    -- The normalized representative is now frozen as actual data in the `pi = 1` fiber.
    intro q
    exact
      normalized_kernel_representative_proj_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hnormalizedScalar :
      ∀ q : Nbar,
        ∃ a : Aˣ, (normalizedRepresentative q).1.2.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- This is the first source-faithful scalar extraction step on `N̄ = ker(pi₂)`.
    intro q
    exact
      normalized_kernel_scalar_exists
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  let kernelScalar : Nbar →* Aˣ :=
    kernel_scalar_unit
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hkernelScalar :
      ∀ q : Nbar, (normalizedRepresentative q).1.2.toLinearEquiv = kernelScalar q •
        LinearEquiv.refl A P_S := by
    -- The normalized scalar is now packaged as a multiplicative map `N̄ → Aˣ`.
    intro q
    simpa [kernelScalar, normalizedRepresentative] using
      kernel_scalar_unit_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hkernelScalar_injective : Function.Injective kernelScalar := by
    -- The normalized scalar already remembers the full kernel class in `N̄`.
    simpa [kernelScalar] using
      kernel_scalar_unit_injective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hnormalizedRepresentative_det :
      ∀ q : Nbar,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalizedRepresentative q).1.2 =
          kernelScalar q ^ Module.finrank A P_S := by
    -- This records the exact determinant carried by the scalar-normalized representative.
    intro q
    simpa [kernelScalar, normalizedRepresentative] using
      normalized_kernel_representative_det_eq_kernel_scalar_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hcorrection_det_mem_C :
      ∀ q : Nbar,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_of_hall_kernel_element
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (normalized_kernel_representative_correction
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)) ∈
          fixed_constituent_determinant_subgroup
            (A := A) (G := G) (I := I) ρA_I := by
    -- The Hall-kernel correction already contributes a determinant inside LinearRepresentations_Serre_1977's subgroup `C`.
    intro q
    simpa using
      normalized_kernel_representative_correction_det_mem_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hNbar_central : Nbar ≤ Subgroup.center (G2 ⧸ I2) := by
    -- Route correction: centrality no longer waits on the quotient-module package. It already
    -- follows from rewriting normalized kernel representatives as scalar points `(1, a • id)`.
    simpa [Nbar, G2, I2, pi2] using
      kernel_subgroup_central_of_normalized_representatives
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hkernelOutDetCorrectionClass :
      ∀ q : Nbar,
        QuotientGroup.mk'
            ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
            (Units.map (IsLocalRing.residue A)
              (fixed_constituent_transport_fiber_det
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2)) =
          fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I
            ⟨fixed_constituent_transport_fiber_det
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                (fixed_constituent_transport_fiber_of_hall_kernel_element
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                  (normalized_kernel_representative_correction
                    (p := p) (A := A) (G := G) (V := V)
                    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q)),
              hcorrection_det_mem_C q⟩ := by
    -- Route correction: the raw quotient-out representative is now compared to the literal
    -- Hall-kernel correction already frozen by `normalizedRepresentative`, rather than to an
    -- arbitrary existential element of `C`.
    intro q
    simpa [Nbar, G2, I2, pi2] using
      kernel_out_representative_det_residue_class_eq_correction_residue_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hnormalizedRepresentative_det_rewrite :
      ∀ q : Nbar,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalizedRepresentative q).1.2 =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) q.1.out.1.2 *
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_transport_fiber_of_hall_kernel_element
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                (normalized_kernel_representative_correction
                  (p := p) (A := A) (G := G) (V := V)
                  hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport
                  hTransportLift q)))⁻¹ := by
    -- This flattens the determinant calculation for the normalized representative before the
    -- final kernel-membership step.
    intro q
    simpa [normalizedRepresentative] using
      normalized_kernel_representative_det_eq_raw_det_mul_correction_inv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hnormalizedDetClassOne :
      ∀ q : Nbar,
        QuotientGroup.mk'
            ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
            (Units.map (IsLocalRing.residue A)
              (fixed_constituent_transport_fiber_det
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                (normalizedRepresentative q).1.2)) =
          1 := by
    -- The determinant of each normalized kernel representative is now known to be quotient-trivial
    -- after cancelling the chosen Hall-kernel correction.
    intro q
    simpa [Nbar, G2, I2, pi2, normalizedRepresentative] using
      normalized_kernel_determinant_class_eq_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q
  have hkernelScalarPowClassOne :
      ∀ q : Nbar,
        QuotientGroup.mk'
            ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
            (Units.map (IsLocalRing.residue A)
              (kernelScalar q ^ Module.finrank A P_S)) =
          1 := by
    -- Reuse the localized kernel-scalar theorem so the remaining blocker stays isolated to the
    -- literal determinant-subgroup upgrade in `Aˣ`.
    simpa [G2, I2, pi2, Nbar, kernelScalar] using
      kernel_scalar_pow_residue_class_eq_one_on_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  -- TODO: follow LinearRepresentations_Serre_1977's literal route from this stabilized quotient skeleton. The remaining
  -- source-faithful blocker is now downstream of the scalar extraction step on `N̄ := ker pi₂`:
  -- the representative is frozen as `normalizedRepresentative`, `kernelScalar : N̄ →* Aˣ`
  -- already packages the literal scalar in LinearRepresentations_Serre_1977's kernel `U₁ = Aˣ`,
  -- `hnormalizedRepresentative_det` computes its determinant as `kernelScalar q ^ d`,
  -- `hnormalizedRepresentative_det_rewrite` rewrites that determinant as raw determinant times
  -- inverse correction determinant, `hkernelOutDetCorrectionClass` identifies the raw class with
  -- the class of the literal correction used in `normalizedRepresentative`, and
  -- `hnormalizedDetClassOne`/`hkernelScalarPowClassOne` close the quotient-level cancellation.
  -- Together with centrality of `N̄` inside `G₂ / I₂` from `hNbar_central`, this leaves one exact
  -- kernel blocker: upgrade that quotient-triviality to the literal source condition
  -- `(kernelScalar q)^d ∈ C`, and only then read off `hNbar_cyclic` and `hNbar_coprime` from the
  -- scalar route.
  -- After that, the remaining work is the quotient-module package (`tau`, `tau_irred`, and
  -- `descendLift`) along the existing multiplicity-space tensor route.
  exact
    { G2 := G2
      instGroupG2 := inferInstance
      instFiniteG2 := inferInstance
      pi := pi
      I2 := I2
      instNormalI2 := inferInstance
      Nbar := Nbar
      instNormalNbar := inferInstance
      hNbar_central := hNbar_central
      hNbar_cyclic :=
        (kernel_subgroup_cyclic_and_coprime_of_bounded_generator_containment
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift hcandidate_le).1
      hNbar_coprime :=
        (kernel_subgroup_cyclic_and_coprime_of_bounded_generator_containment
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift hcandidate_le).2
      tau :=
        fixed_isotypic_multiplicity_space_quotient_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift
      tau_irred :=
        fixed_isotypic_multiplicity_space_quotient_irreducible
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift
      quotientEquiv := quotientEquiv
      descendLift :=
        descend_lift_of_fixed_constituent_tensor
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift }

/-- Helper for Theorem 17-17.6-1: package LinearRepresentations_Serre_1977's finite projective extension on the fixed lifted
constituent `S̄` and descend the literal multiplicity space to the quotient representation `τ`. -/
private noncomputable def exists_constituent_projective_extension_quotient_data
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ConstituentProjectiveExtensionQuotientData
      (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
  let G1 :=
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I
  let pi1 :
      G1 →* G :=
    fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  have hpi1_surj : Function.Surjective pi1 := by
    -- The literal carrier `G₁ = {(s, u) | u ∈ U_s}` already surjects onto `G`, with an explicit
    -- section recorded by `fixed_constituent_transport_total_space_proj_section`.
    simpa [G1, pi1] using
      fixed_constituent_transport_total_space_proj_surjective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let C :=
    fixed_constituent_determinant_subgroup
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  have hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
    -- The fixed lift now satisfies LinearRepresentations_Serre_1977's scalar endomorphism classification.
    intro f
    exact
      fixed_constituent_lift_equivariant_endomorphism_scalar
        (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
        hSbar_irred ρA_I red_S hLiftSbar f
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    -- This is the literal source upgrade `U₁ = Aˣ` obtained from the scalar endomorphism theorem.
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I hscalar u
  have hdet_coset :
      ∀ s : G,
        ∀ u :
          fixed_constituent_transport_fiber
            (A := A) (G := G) I ρA_I s,
          ∃ a : Aˣ,
            fixed_constituent_transport_fiber_det
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
              fixed_constituent_transport_fiber_det
                  (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                  ((fixed_constituent_transport_total_space_section
                    (p := p) (A := A) (G := G) (V := V)
                    hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) *
                a ^ Module.finrank A P_S := by
    -- Same-fiber determinants are now reduced to the chosen section determinant up to a `d`-th
    -- power of a unit, exactly as in LinearRepresentations_Serre_1977's determinant-normalization step.
    intro s u
    exact
      fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s u
  have hCcop :
      Nat.Coprime p (Nat.card C) := by
    -- The determinant subgroup `C` is now pinned down as a finite quotient of `I`, so its order
    -- is automatically prime to `p`.
    simpa [C] using
      fixed_constituent_determinant_subgroup_coprime
        (A := A) (G := G) (I := I) hIcop ρA_I
  have hdimcop : Nat.Coprime p (Module.finrank A P_S) := by
    -- The fixed lifted constituent has degree prime to `p`, exactly as in LinearRepresentations_Serre_1977's argument before
    -- the determinant-normalized subgroup `G₂` is carved out.
    exact
      fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hprincipal_root :
      ∀ {u : Aˣ}, IsLocalRing.residue A (u : A) = 1 →
        ∃ a : Aˣ, a ^ Module.finrank A P_S = u := by
    -- The new Hensel step removes any principal-unit error from a determinant class.
    intro u hu
    exact
      exists_dth_root_of_unit_of_residue_eq_one
        (p := p) (A := A) hp hdimcop hu
  have hsection_card_root :
      ∀ s : G,
        ∃ a : Aˣ,
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              ((fixed_constituent_transport_total_space_section
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) ^
            Nat.card G =
            a ^ Module.finrank A P_S := by
    -- The chosen section determinants now have uniform `|G|`-torsion modulo `d`-th powers.
    intro s
    exact
      fixed_constituent_section_det_pow_card_eq_unit_pow
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  have hsection_class_card :
      ∀ s : G,
        let d := Module.finrank A P_S
        let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
        let sec :=
          fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
        (QuotientGroup.mk' Qd
          (Units.map (IsLocalRing.residue A)
            (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2))) ^
          Nat.card G = 1 := by
    -- This is the exact quotient-owner frontier from the current LinearRepresentations_Serre_1977 route: the chosen section
    -- determinants are torsion only modulo `d`-th powers, not as literal residue units.
    intro s
    exact
      section_determinant_class_pow_card_eq_one_mod_dth_powers
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  let NbarCandidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let hsection_mem_candidate :
      ∀ s : G,
        fixed_constituent_section_determinant_class
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
          NbarCandidate :=
    fixed_constituent_section_determinant_class_mem_candidate
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let hC_mem_candidate :
      ∀ c : C,
        fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c ∈
          NbarCandidate :=
    fixed_constituent_determinant_subgroup_residue_class_mem_candidate
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Qd : Subgroup kˣ :=
    (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  have hC_mem_lcm :
      ∀ c : C,
        fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c ∈
          (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
    intro c
    -- The determinant-subgroup generator family is now fully normalized into the common bounded
    -- roots-of-unity subgroup predicted by LinearRepresentations_Serre_1977.
    simpa [C, Qd] using
      determinant_subgroup_residue_class_mem_lcm_rootsOfUnity_image
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) c
  have hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar := by
    -- The closure step is now fully factored out: once the section family is normalized into the
    -- same bounded roots-of-unity owner as `C`, the candidate subgroup follows by closure.
    simpa [C, Qd] using
      candidate_subgroup_le_rootsOfUnity_lcm_image
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  -- Route correction: the main theorem no longer hides the whole fixed-constituent package behind
  -- one monolithic placeholder. The remaining two source-level blockers are now explicit:
  -- normalize the section family into the bounded roots-of-unity owner, then package the literal
  -- determinant-normalized cover `G₂/I₂/N̄` and the multiplicity-space descent.
  exact
    projective_extension_kernel_quotient_data_from_bounded_generator_containment
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport hTransportLift
      hcandidate_le

/-- Helper for Theorem 17-17.6-1: in LinearRepresentations_Serre_1977's successor-height quotient branch, the recursive
height witness on `H ⧸ N` already exposes the next normal step `M / N` whose order is either
prime to `p` or a `p`-power. -/
private theorem exists_quotient_normal_step_of_psolvableHeight_succ
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hquot : IsPSolvableOfHeight p (Nat.succ h) (H ⧸ N)) :
    ∃ Mbar : Subgroup (H ⧸ N),
      ∃ _ : Mbar.Normal,
        (Nat.Coprime p (Nat.card Mbar) ∨ IsPGroup p Mbar) ∧
          IsPSolvableOfHeight p h ((H ⧸ N) ⧸ Mbar) := by
  -- Unfold the successor-height witness once so the remaining work can focus on LinearRepresentations_Serre_1977's two
  -- quotient-side cases for the chosen step `M / N`.
  simpa [Nat.succ_eq_add_one] using IsPSolvableOfHeight.succ_iff.mp hquot

/-- Helper for Theorem 17-17.6-1: pulling back LinearRepresentations_Serre_1977's fixed quotient step `M̄ ≤ H ⧸ N` along the
quotient map recovers the literal subgroup `M ≤ H`, and the corresponding double quotient is
canonically `H ⧸ M`. -/
private noncomputable def quotient_preimage_equiv_of_quotient_normal_step
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal] :
    ((H ⧸ N) ⧸ Mbar) ≃* H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hmap : M.map (QuotientGroup.mk' N) = Mbar := by
    -- The quotient map is surjective, so LinearRepresentations_Serre_1977's fixed step is recovered exactly after pullback.
    simpa [M] using
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Mbar
  -- Route correction: normalize the iterated quotient first, then hand the remaining branch work
  -- to the source-faithful `p`-group / coprime split on the literal subgroup `M ≤ H`.
  exact
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient N M hNM)

/-- Helper for Theorem 17-17.6-1: if LinearRepresentations_Serre_1977's quotient step `M̄ = M / N` has order prime to `p`,
then the literal pullback subgroup `M ≤ H` also has order prime to `p`, because `|M| = |M̄| |N|`.
-/
private theorem coprime_card_preimage_of_quotient_normal_step
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N))
    (hMbar_cop : Nat.Coprime p (Nat.card Mbar)) :
    Nat.Coprime p (Nat.card (Subgroup.comap (QuotientGroup.mk' N) Mbar)) := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let φ : M →* H ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  letI : (N.subgroupOf M).Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hker : φ.ker = N.subgroupOf M := by
    ext x
    change (QuotientGroup.mk' N ((x : M) : H) = 1) ↔ ((x : H) ∈ N)
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mpr hx
  have hrange : φ.range = Mbar := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hq
      rcases QuotientGroup.mk'_surjective N q with ⟨x, rfl⟩
      exact ⟨⟨x, hq⟩, rfl⟩
  have hcardNsub : Nat.card (N.subgroupOf M) = Nat.card N := by
    -- The pullback contains `N`, so the restricted kernel subgroup has the same cardinality.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcardMquot : Nat.card (M ⧸ N.subgroupOf M) = Nat.card Mbar := by
    -- The quotient of the literal pullback by `N` is exactly LinearRepresentations_Serre_1977's chosen step `M̄`.
    simpa [hker] using
      (Nat.card_congr
        (((QuotientGroup.quotientKerEquivRange φ).trans
            (MulEquiv.subgroupCongr hrange)).toEquiv))
  -- Route correction: keep LinearRepresentations_Serre_1977's literal subgroup `M` and use the exact cardinal factorization
  -- `|M| = |M / N| |N|` instead of introducing a transport-heavy surrogate subgroup.
  rw [show Nat.card M = Nat.card (M ⧸ N.subgroupOf M) * Nat.card (N.subgroupOf M) by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)]
  rw [hcardMquot, hcardNsub]
  exact Nat.Coprime.mul_right hMbar_cop hNcop

/-- Helper for Theorem 17-17.6-1: if LinearRepresentations_Serre_1977's chosen quotient step `M̄ = M / N` has order prime to
`p`, then the literal pullback subgroup `M ≤ H` already gives a same-height recursive call on `H`.
-/
private theorem
    exists_residueFieldLift_of_central_cyclic_coprime_kernel_coprime_preimage_branch
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p (Nat.succ h) G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMbar_cop : Nat.Coprime p (Nat.card Mbar))
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    -- LinearRepresentations_Serre_1977's literal subgroup `M` inherits prime-to-`p` order from `M / N` and `N`.
    simpa [M] using
      coprime_card_preimage_of_quotient_normal_step
        (p := p) (N := N) hNcop Mbar hMbar_cop
  have hHsolv : IsPSolvableOfHeight p (Nat.succ h) H := by
    -- Reinsert the prime-to-`p` subgroup `M` as the first step in the height tower for `H`.
    refine IsPSolvableOfHeight.succ_iff.mpr ?_
    exact ⟨M, inferInstance, Or.inl hMcop, by simpa [M] using hMquot⟩
  -- The coprime branch is now exactly the recursive same-height call on `H`.
  exact hrecLower hHsolv τ

/-- Helper for Theorem 17-17.6-1: in LinearRepresentations_Serre_1977's `p`-group quotient branch, Schur-Zassenhaus may be
applied inside the literal pullback subgroup `M := preimage(M̄)` to split off a `p`-group
complement to `N`. This isolates the concrete subgroup data before the later quotient descent. -/
private theorem pgroup_preimage_complement_data_of_quotient_normal_step
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMp : IsPGroup p Mbar) :
    ∃ P : Subgroup H,
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar ∧
      IsPGroup p P ∧
      Disjoint N P ∧
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar := by
  letI : Fact p.Prime := ⟨hp⟩
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let Nsub : Subgroup M := N.subgroupOf M
  letI : M.Normal := by infer_instance
  letI : Nsub.Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  let φ : M →* H ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hker : φ.ker = Nsub := by
    ext x
    change (QuotientGroup.mk' N ((x : M) : H) = 1) ↔ ((x : H) ∈ N)
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mpr hx
  have hrange : φ.range = Mbar := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hq
      rcases QuotientGroup.mk'_surjective N q with ⟨x, rfl⟩
      exact ⟨⟨x, hq⟩, rfl⟩
  have hcardNsub : Nat.card Nsub = Nat.card N := by
    -- Passing to the subgroup-of-subgroup view does not change the kernel cardinality.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcardMquot : Nat.card (M ⧸ Nsub) = Nat.card Mbar := by
    -- The quotient of the literal pullback by `N` is exactly LinearRepresentations_Serre_1977's chosen quotient step `M̄`.
    simpa [hker] using
      (Nat.card_congr
        (((QuotientGroup.quotientKerEquivRange φ).trans
            (MulEquiv.subgroupCongr hrange)).toEquiv))
  have hindexNsub : Nsub.index = Nat.card Mbar := by
    rw [Subgroup.index_eq_card]
    exact hcardMquot
  have hcopNsub :
      Nat.Coprime (Nat.card Nsub) Nsub.index := by
    obtain ⟨n, hn⟩ := hMp.exists_card_eq
    rw [hcardNsub, hindexNsub, hn]
    exact hNcop.symm.pow_right n
  obtain ⟨Q, hQcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := Nsub) hcopNsub
  have hMquot_p : IsPGroup p (M ⧸ Nsub) := by
    -- LinearRepresentations_Serre_1977's quotient step `M / N` is literally the chosen `p`-group `M̄`.
    have hMquot_p' : IsPGroup p (M ⧸ φ.ker) := by
      exact
        hMp.of_equiv
          ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)).symm
    exact hMquot_p'.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)
  have hQp : IsPGroup p Q := by
    -- A complement to the prime-to-`p` subgroup `N` identifies with the quotient `M / N`.
    exact hMquot_p.of_equiv (hQcomp.symm.QuotientMulEquiv)
  let P : Subgroup H := Q.map M.subtype
  have hP_le_M : P ≤ M := by
    exact Subgroup.map_subtype_le Q
  have hP_disjoint : Disjoint N P := by
    have hdisj_map :
        Disjoint ((N.subgroupOf M).map M.subtype) (Q.map M.subtype) := by
      exact Subgroup.disjoint_map (f := M.subtype) Subtype.coe_injective hQcomp.disjoint
    have hmapN : (N.subgroupOf M).map M.subtype = N := by
      simpa [M] using Subgroup.map_subgroupOf_eq_of_le hNM
    simpa [P, hmapN] using hdisj_map
  have hP_sup : N ⊔ P = M := by
    have hmapN : (N.subgroupOf M).map M.subtype = N := by
      simpa [M] using Subgroup.map_subgroupOf_eq_of_le hNM
    calc
      N ⊔ P = (N.subgroupOf M).map M.subtype ⊔ Q.map M.subtype := by
        simp [P, hmapN]
      _ = ((N.subgroupOf M) ⊔ Q).map M.subtype := by
        rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hQcomp.sup_eq_top]
      _ = M := by
        simpa [MonoidHom.range_eq_map] using M.range_subtype
  refine ⟨P, hP_le_M, ?_, hP_disjoint, hP_sup⟩
  -- The concrete complement subgroup `P ≤ H` is a `p`-group because it comes from the quotient
  -- `M / N ≃ M̄`, which is already the `p`-group step in LinearRepresentations_Serre_1977's recursion.
  simpa [P] using hQp.map M.subtype

/-- Helper for Theorem 17-17.6-1: once LinearRepresentations_Serre_1977's literal split `M = N × P` is fixed with `N`
central and of order prime to `p`, the complement `P` is already normal in `H`. The proof keeps
the source route: first show `P` is normal in `M` because conjugation by `n * p` reduces to
conjugation by `p`, then upgrade to `H` by identifying `P` with the unique Sylow `p`-subgroup of
`M`. -/
private theorem normal_of_pgroup_preimage_complement
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H)
    (hP_le :
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hPp : IsPGroup p P)
    (hP_disjoint : Disjoint N P)
    (hP_sup :
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar) :
    P.Normal := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  let Nsub : Subgroup M := N.subgroupOf M
  let Psub : Subgroup M := P.subgroupOf M
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hN_le_normalizer : N ≤ Subgroup.normalizer P := by
    -- The central kernel `N` normalizes `P` because conjugation by `n ∈ N` is trivial.
    intro n hn
    rw [Subgroup.mem_normalizer_iff']
    intro x
    rw [(Subgroup.mem_center_iff.mp (hNcentral hn) x).symm]
  have hM_le_normalizer : M ≤ Subgroup.normalizer P := by
    -- Route correction: use the literal split `M = N ⊔ P` elementwise to show all of `M`
    -- normalizes `P`.
    let T : Subgroup H := Subgroup.normalizer P
    have hN_le_T : N ≤ T := hN_le_normalizer
    intro m hm
    have hmSup : m ∈ N ⊔ P := by
      simpa [M, hP_sup] using hm
    rcases (Subgroup.mem_sup_of_normal_left.mp hmSup) with ⟨n, hnN, u, huP, rfl⟩
    have hu_norm : u ∈ T := by
      exact (Subgroup.le_normalizer (H := P)) huP
    have hmul : n * u ∈ T := T.mul_mem (hN_le_T hnN) hu_norm
    simpa [T] using hmul
  have hPsub_normal : Psub.Normal := by
    -- Inside `M`, the complement `P` is normal because `M ≤ normalizer(P)`.
    exact Subgroup.normal_subgroupOf_of_le_normalizer hM_le_normalizer
  have hNsub_disjoint : Disjoint Nsub Psub := by
    -- The pullback split keeps the factors disjoint after passing to `M`.
    rw [Subgroup.disjoint_def]
    intro x hxN hxP
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hP_disjoint) hxN hxP
  have hNsub_sup_top : Nsub ⊔ Psub = ⊤ := by
    -- Any element of `M` already decomposes as an `N`-part times a `P`-part by the source split.
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hxSup : ((x : M) : H) ∈ N ⊔ P := by
        simpa [M, hP_sup] using x.property
      rcases (Subgroup.mem_sup_of_normal_left.mp hxSup) with ⟨n, hnN, p, hpP, hnp⟩
      refine (Subgroup.mem_sup_of_normal_left).2 ?_
      exact ⟨⟨n, hNM hnN⟩, hnN, ⟨p, hP_le hpP⟩, hpP, Subtype.ext hnp⟩
  have hcomp : Nsub.IsComplement' Psub := by
    -- The restricted factors inside `M` are complementary in the exact Schur-Zassenhaus split.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNsub_disjoint ?_
    simpa [hNsub_sup_top] using (Subgroup.normal_mul Nsub Psub).symm
  have hPsub_p : IsPGroup p Psub := by
    -- Passing from `P ≤ H` to `P ≤ M` does not change the `p`-group structure.
    exact hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le).symm
  have hcardNsub : Nat.card Nsub = Nat.card N := by
    -- The kernel subgroup keeps the same cardinality inside the pullback.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hindexPsub : Psub.index = Nat.card Nsub := by
    -- In a complement decomposition, the index of `P` in `M` is the cardinality of `N`.
    exact hcomp.index_eq_card
  have hPsub_not_dvd : ¬ p ∣ Psub.index := by
    -- The prime-to-`p` order of `N` forces the complement index to be prime to `p`.
    rw [hindexPsub, hcardNsub]
    exact hp.coprime_iff_not_dvd.mp hNcop
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let PsubSylow : Sylow p M := IsPGroup.toSylow (P := Psub) hPsub_p hPsub_not_dvd
  have hPsub_char : Psub.Characteristic := by
    -- A normal Sylow subgroup is characteristic, so LinearRepresentations_Serre_1977's complement is fixed by all
    -- automorphisms of `M`.
    exact
      Sylow.characteristic_of_normal PsubSylow
        (by simpa [IsPGroup.toSylow_coe (P := Psub) hPsub_p hPsub_not_dvd] using hPsub_normal)
  letI : Psub.Characteristic := hPsub_char
  have hmapPsub : Subgroup.map M.subtype Psub = P := by
    -- Mapping the restricted complement back into `H` recovers the literal subgroup `P`.
    simpa [Psub] using Subgroup.map_subgroupOf_eq_of_le hP_le
  -- Upgrade normality from `M` to `H` by characteristic transport along the normal pullback `M`.
  rw [← hmapPsub]
  exact ConjAct.normal_of_characteristic_of_normal (H := M) (K := Psub)

/-- Helper for Theorem 17-17.6-1: the quotient package attached to the concrete split
`M = N × P` in the `p`-group branch. -/
private structure PgroupPreimageSplitQuotientData
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H) [P.Normal]
    where
  hN_image_central :
    N.map (QuotientGroup.mk' P) ≤ Subgroup.center (H ⧸ P)
  hN_image_cyclic :
    IsCyclic (N.map (QuotientGroup.mk' P))
  hN_image_coprime :
    Nat.Coprime p (Nat.card (N.map (QuotientGroup.mk' P)))
  hQuotientHeight :
    IsPSolvableOfHeight p (Nat.succ h) (H ⧸ P)
  quotientEquiv :
    ((H ⧸ P) ⧸ N.map (QuotientGroup.mk' P)) ≃*
      H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar

private noncomputable def central_cyclic_image_quotient_data_of_pgroup_preimage_split
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H) [P.Normal]
    (hP_le :
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hP_disjoint : Disjoint N P)
    (hP_sup :
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    PgroupPreimageSplitQuotientData
      (p := p) (h := h) (N := N) Mbar P := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let q : H →* H ⧸ P := QuotientGroup.mk' P
  let N' : Subgroup (H ⧸ P) := N.map q
  letI : N'.Normal := by infer_instance
  have hmapM : M.map q = N' := by
    -- Quotienting the split `M = N ⊔ P` by `P` kills exactly the `P`-factor.
    calc
      M.map q = (N ⊔ P).map q := by rw [hP_sup]
      _ = N.map q ⊔ P.map q := by rw [Subgroup.map_sup]
      _ = N.map q ⊔ ⊥ := by rw [QuotientGroup.map_mk'_self P]
      _ = N' := by simp [N']
  have hcomapN' : Subgroup.comap q N' = M := by
    -- The image subgroup `N'` pulls back to the original LinearRepresentations_Serre_1977 step `M`.
    calc
      Subgroup.comap q N' = Subgroup.comap q (M.map q) := by rw [hmapM]
      _ = M := by
        rw [Subgroup.comap_map_eq_self]
        simpa [M, q, QuotientGroup.ker_mk'] using hP_le
  have hN'_central : N' ≤ Subgroup.center (H ⧸ P) := by
    -- Centrality of `N` survives after pushing it into the quotient by `P`.
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨n, hnN, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    rcases QuotientGroup.mk'_surjective P y with ⟨h, rfl⟩
    have hcomm : h * (n : H) = (n : H) * h := Subgroup.mem_center_iff.mp (hNcentral hnN) h
    simpa using congrArg (QuotientGroup.mk' P) hcomm
  let φ : N →* H ⧸ P := q.comp N.subtype
  have hφker : φ.ker = ⊥ := by
    -- Disjointness with `P` makes the quotient map injective on the central kernel `N`.
    rw [MonoidHom.ker_eq_bot_iff]
    intro n₁ n₂ hEq
    apply Subtype.ext
    have hmem :
        ((n₁ : N) : H) / (n₂ : H) ∈ P := by
      exact (QuotientGroup.eq_iff_div_mem).mp hEq
    have hdiv_one : ((n₁ : N) : H) / (n₂ : H) = 1 := by
      exact
        (Subgroup.disjoint_def.mp hP_disjoint)
          (by
            exact
              N.div_mem n₁.property n₂.property)
          hmem
    exact div_eq_one.mp hdiv_one
  have hφrange : φ.range = N' := by
    -- The restricted quotient map has image exactly `N.map q`.
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(n : N), n.property, rfl⟩
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨n, hnN, rfl⟩
      exact ⟨⟨n, hnN⟩, rfl⟩
  let eN : N ≃* N' :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange)))
  have hN'_cyclic : IsCyclic N' := by
    -- Injectivity on `N` transports LinearRepresentations_Serre_1977's cyclic kernel to the quotient image `N'`.
    letI : IsCyclic N := hNcyclic
    exact isCyclic_of_surjective eN eN.surjective
  have hcardN' : Nat.card N' = Nat.card N := by
    -- The same restricted equivalence transports the cardinality of the kernel.
    exact (Nat.card_congr eN.toEquiv).symm
  have hN'_cop : Nat.Coprime p (Nat.card N') := by
    -- Coprimality with `p` is unchanged under the kernel-image equivalence.
    simpa [hcardN'] using hNcop
  have hquotEquiv :
      ((H ⧸ P) ⧸ N') ≃* H ⧸ M := by
    -- Reuse the existing third-isomorphism step with kernel `P` and then rewrite the pullback
    -- subgroup back to the literal LinearRepresentations_Serre_1977 step `M`.
    exact
      (quotient_preimage_equiv_of_quotient_normal_step (N := P) N').trans
        (QuotientGroup.quotientMulEquivOfEq hcomapN')
  have hQuotLower : IsPSolvableOfHeight p h ((H ⧸ P) ⧸ N') := by
    -- Transport LinearRepresentations_Serre_1977's lower-height witness through the concrete quotient equivalence.
    exact IsPSolvableOfHeight.of_equiv hquotEquiv.symm hMquot
  refine
    ⟨hN'_central, hN'_cyclic, hN'_cop, ?_, hquotEquiv⟩
  -- The quotient by `P` is again one LinearRepresentations_Serre_1977 step above the lower-height quotient by `N'`.
  exact IsPSolvableOfHeight.succ_iff.mpr ⟨N', inferInstance, Or.inl hN'_cop, hQuotLower⟩

/-- Helper for Theorem 17-17.6-1: if LinearRepresentations_Serre_1977's chosen quotient step `M̄ = M / N` is a `p`-group,
the remaining work is the source-faithful Schur-Zassenhaus split `M = N × P` inside the literal
pullback subgroup `M ≤ H`. -/
private theorem
    exists_residueFieldLift_of_central_cyclic_coprime_kernel_pgroup_preimage_branch
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p (Nat.succ h) G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMp : IsPGroup p Mbar)
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP_le_M, hPp, hP_disjoint, hP_sup⟩ :
      ∃ P : Subgroup H,
        P ≤ M ∧
        IsPGroup p P ∧
        Disjoint N P ∧
        N ⊔ P = M := by
    -- First isolate LinearRepresentations_Serre_1977's literal subgroup decomposition `M = N × P`; the remaining blocker is
    -- only the quotient descent through this concrete complement.
    simpa [M] using
      pgroup_preimage_complement_data_of_quotient_normal_step
        (p := p) hp (N := N) hNcop Mbar hMp
  letI : P.Normal := by
    -- Route correction: install normality on the literal complement `P` before forming
    -- `H ⧸ P`; this is the exact subgroup-transport step that was previously left implicit.
    exact
      normal_of_pgroup_preimage_complement
        (p := p) hp (N := N) hNcentral hNcop Mbar P hP_le_M hPp hP_disjoint hP_sup
  have hτ_trivial : Representation.IsTrivial (τ.comp P.subtype) := by
    -- A normal `p`-subgroup acts trivially on an irreducible module in characteristic `p`.
    exact
      isTrivial_restrict_normal_pSubgroup_of_isIrreducible
        (p := p) (A := A) (G := H) (V := W) τ P hPp
  letI : Representation.IsTrivial (τ.comp P.subtype) := hτ_trivial
  let τP : Representation k (H ⧸ P) W := τ.ofQuotient P
  letI : τP.IsIrreducible := by
    exact isIrreducible_of_ofQuotient_of_isTrivial τ P
  let hPkg :=
    central_cyclic_image_quotient_data_of_pgroup_preimage_split
      (p := p) (h := h) (N := N) hNcentral hNcyclic hNcop Mbar P hP_le_M hP_disjoint hP_sup
      hMquot
  have hHPsolv := hPkg.hQuotientHeight
  have hLiftQuot :
      ∃ (P' : Type (max u v x)) (_ : AddCommGroup P') (_ : Module A P')
        (_ : Module.Free A P') (_ : Module.Finite A P')
        (ρA : Representation A (H ⧸ P) P')
        (red : P' →ₗ[A] W),
          IsResidueFieldLift τP ρA red := by
    -- The recursive content is now exactly LinearRepresentations_Serre_1977's lower-height step on `H ⧸ P`.
    exact hrecLower hHPsolv τP
  -- Inflate the recursive quotient lift back to `τ` in the already prepared witness universe.
  exact
    exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
      (A := A) (ρ := τ) (I := P) hLiftQuot

/-- Helper for Theorem 17-17.6-1: once LinearRepresentations_Serre_1977's quotient module `τ` over `H / N̄` is in hand, the
remaining source-faithful step is a lower-height induction across the central cyclic coprime
kernel `N̄`. -/
private theorem
    exists_residueFieldLift_of_isIrreducible_of_central_cyclic_coprime_kernel_via_lower_height
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (hquot : IsPSolvableOfHeight p h (H ⧸ N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  cases h with
  | zero =>
      letI : Subsingleton (H ⧸ N) := hquot
      have hN_top : N = ⊤ := by
        -- When `H ⧸ N` is trivial, every element of `H` maps to `1`, so the kernel is all of `H`.
        ext x
        constructor
        · intro hx
          simp
        · intro _
          have hxq : (QuotientGroup.mk x : H ⧸ N) = 1 := Subsingleton.elim _ _
          exact (QuotientGroup.eq_one_iff (N := N) (x := x)).mp hxq
      have hHcop : ¬ p ∣ Nat.card H := by
        -- In LinearRepresentations_Serre_1977's base case `H = N`, so the whole group has order prime to `p`.
        rcases CharP.char_is_prime_or_zero k p with hp | hp0
        · simpa [hN_top] using (hp.coprime_iff_not_dvd.mp hNcop)
        · subst hp0
          simpa using (Nat.card_pos (α := H)).ne'
      -- With `H = N`, the Chapter `17.3` prime-to-`p` lift theorem applies directly.
      rcases
          exists_residueFieldLift_of_non_dvd_card_witness
            (A := A) (p := p) (G' := H) (V' := W) hHcop τ with
        ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
      exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  | succ h =>
      -- Route correction: the remaining source-faithful work is only LinearRepresentations_Serre_1977's successor-height
      -- split inside `H / N`. One must choose the normal step `M / N`, handle the `p`-group case
      -- by killing the normal `p`-subgroup action, and handle the prime-to-`p` case by lowering
      -- the ambient quotient height before feeding the result to `hrecLower`.
      obtain ⟨Mbar, hMbar_normal, hMbar_step, hMbar_quot⟩ :=
        exists_quotient_normal_step_of_psolvableHeight_succ
          (p := p) (h := h) (N := N) hquot
      let _ := Mbar
      let _ := hMbar_normal
      let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
      letI : M.Normal := by infer_instance
      have hMquot : IsPSolvableOfHeight p h (H ⧸ M) := by
        -- First move the quotient-height witness from `((H ⧸ N) ⧸ M̄)` to the literal pullback
        -- subgroup `M ≤ H`; the remaining work is now the genuine LinearRepresentations_Serre_1977 branch split on `M / N`.
        change IsPSolvableOfHeight p h (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)
        simpa [M] using
          IsPSolvableOfHeight.of_equiv
            (quotient_preimage_equiv_of_quotient_normal_step (N := N) Mbar)
            hMbar_quot
      have hMcop_preimage :
          Nat.Coprime p (Nat.card Mbar) →
            Nat.Coprime p (Nat.card M) := by
        -- In the prime-to-`p` branch, LinearRepresentations_Serre_1977's literal subgroup `M` inherits coprime order from
        -- the exact factorization `|M| = |M / N| |N|`.
        intro hMbar_cop
        exact
          coprime_card_preimage_of_quotient_normal_step
            (p := p) (N := N) hNcop Mbar hMbar_cop
      let _ := hMquot
      let _ := hMcop_preimage
      rcases hMbar_step with hMbar_cop | hMp
      · -- In the coprime branch, the literal subgroup `M` already has prime-to-`p` order, so the
        -- same-height recursion hypothesis applies directly to the whole ambient group `H`.
        exact
          exists_residueFieldLift_of_central_cyclic_coprime_kernel_coprime_preimage_branch
            (p := p) (A := A) (h := h) (N := N) hNcop hrecLower τ Mbar hMbar_cop hMquot
      · -- In the `p`-group branch, the only remaining blocker is LinearRepresentations_Serre_1977's explicit
        -- Schur-Zassenhaus complement construction on the literal pullback subgroup `M`.
        exact
          exists_residueFieldLift_of_central_cyclic_coprime_kernel_pgroup_preimage_branch
            (p := p) (A := A) (h := h) hp (N := N)
            hNcentral hNcyclic hNcop hrecLower τ Mbar hMp hMquot

theorem exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIsotypic :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k I) V) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A G P)
        (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Route correction: this branch must follow LinearRepresentations_Serre_1977's `S̄ ⊗ F` route through the finite central
  -- extension `G₂`; replacing it by an ad hoc recursion would lose the source proof's main
  -- controlling object and the lower-height quotient `H = G₂ / I`.
  -- The verified prefix in this file already handles the two outer recursive branches:
  -- `p`-kernel descent through quotients and the non-isotypic Hall-kernel branch through proper
  -- stabilizers. The only missing frontier is the intrinsic projective-extension package for the
  -- genuinely isotypic Hall-kernel case.
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  rcases
      exists_irreducible_constituent_with_isotypic_component_top_of_isotypic_restriction
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ hIsotypic with
    ⟨Sbar, hSbar_irred, hSbar_top⟩
  letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
  let F := fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar
  have hCoord :
      ∃ n : ℕ, Nonempty (V ≃ₗ[MonoidAlgebra k I] Fin n → Sbar.asSubmodule) := by
    -- Rigidify LinearRepresentations_Serre_1977's chosen constituent onto a coordinate model before building `G₂`.
    exact
      exists_linearEquiv_pi_of_isotypic_component_top
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        (by simpa using hSbar_top)
  have hLiftSbar :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A I P)
        (red : P →ₗ[A] Sbar.toSubmodule),
          IsResidueFieldLift Sbar.toRepresentation ρA red := by
    -- LinearRepresentations_Serre_1977's source route lifts the fixed constituent before defining the finite cover `G₂`.
    exact
      exists_residueFieldLift_of_fixed_constituent
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar
  rcases hCoord with ⟨d, eCoord⟩
  rcases hLiftSbar with
    ⟨P_S, hP_S_add, hP_S_mod, hP_S_free, hP_S_finite, ρA_I, red_S, hLiftSbar⟩
  letI : AddCommGroup P_S := hP_S_add
  letI : Module A P_S := hP_S_mod
  letI : Module.Free A P_S := hP_S_free
  letI : Module.Finite A P_S := hP_S_finite
  have hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation) := by
    -- This is the source-faithful `U_s ≠ ∅` step on the fixed literal constituent `S̄`.
    exact
      transported_constituent_equiv_of_isotypic_component_top
        (p := p) (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        (by simpa using hSbar_top)
  have hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S) := by
    -- Transport the fixed `A[I]`-lift of `S̄` across the source-faithful equivalence
    -- `S̄ ≃ sS̄`; only the reduction map changes by postcomposition.
    intro s
    exact
      residueFieldLift_of_equiv_target_local
        (A := A) (G := I) (ρA := ρA_I) (red := red_S) hLiftSbar (hTransport s).some
  let pkg :
      ConstituentProjectiveExtensionQuotientData
        (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
    exists_constituent_projective_extension_quotient_data
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Group pkg.G2 := pkg.instGroupG2
  letI : Finite pkg.G2 := pkg.instFiniteG2
  letI : pkg.I2.Normal := pkg.instNormalI2
  letI : pkg.Nbar.Normal := pkg.instNormalNbar
  have hquotPkg : IsPSolvableOfHeight p h ((pkg.G2 ⧸ pkg.I2) ⧸ pkg.Nbar) := by
    -- The quotient in LinearRepresentations_Serre_1977's finite cover is designed to recover the original lower-height
    -- quotient `G / I`.
    exact IsPSolvableOfHeight.of_equiv pkg.quotientEquiv.symm hquot
  letI : pkg.tau.IsIrreducible := pkg.tau_irred
  have hTauLift :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A (pkg.G2 ⧸ pkg.I2) P)
        (red : P →ₗ[A] F),
          IsResidueFieldLift pkg.tau ρA red := by
    -- The quotient-side module is now isolated; the remaining recursive content is purely the
    -- lower-height induction across the central cyclic prime-to-`p` kernel.
    exact
      exists_residueFieldLift_of_isIrreducible_of_central_cyclic_coprime_kernel_via_lower_height
        (p := p) (A := A) (h := h) hp (N := pkg.Nbar)
        pkg.hNbar_central pkg.hNbar_cyclic pkg.hNbar_coprime hquotPkg hrecLower pkg.tau
  rcases hTauLift with ⟨P_tau, hP_tau_add, hP_tau_mod, hP_tau_free, hP_tau_finite, ρA_tau,
      red_tau, hLift_tau⟩
  -- The only remaining source-faithful work is now owned by the fixed-constituent package:
  -- tensor the lifted constituent with this quotient-side lift and descend the prime-to-`p`
  -- kernel upstairs. The main theorem only consumes that packaged assembly.
  exact
    pkg.descendLift hP_tau_add hP_tau_mod hP_tau_free hP_tau_finite ρA_tau red_tau hLift_tau

/-- Helper for Theorem 17-17.6-1: the coprime-kernel branch packages LinearRepresentations_Serre_1977's isotypic
decomposition and projective-extension argument for a normal Hall subgroup. -/
theorem exists_residueFieldLift_of_isIrreducible_of_normal_coprime_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) (hI : I.Normal)
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p h G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  letI : I.Normal := hI
  -- Route correction: the trivial-quotient case is already covered by the Chapter `15` Hall lift.
  -- The only remaining frontier is the genuine proper Hall-kernel case, which needs the
  -- Clifford/stabilizer split and LinearRepresentations_Serre_1977's projective-extension descent.
  by_cases hItop : I = ⊤
  · -- If `I = G`, then `|G|` is itself prime to `p`, so the Chapter `15` lifting theorem applies
    -- directly without any quotient recursion.
    have hGcop : ¬ p ∣ Nat.card G := by
      simpa [hItop] using (hp.coprime_iff_not_dvd.mp hIcop)
    rcases exists_residueFieldLift_of_non_dvd_card_witness (A := A) (p := p) hGcop ρ with
      ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
    exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  have hsemisimple :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra k I) V)
  · -- If the restricted module has a single isotypic component, we are exactly in LinearRepresentations_Serre_1977's
    -- projective-extension branch.
    have hIsotypic : IsIsotypic (MonoidAlgebra k I) V := by
      exact
        isIsotypic_of_subsingleton_isotypicComponents
          (R := MonoidAlgebra k I) (M := V) hsub
    exact
      exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
        (p := p) (A := A) (h := h) (G := G) (V := V)
        hp I hIcop hquot hrecLower ρ hIsotypic
  · have hsplit :
        (∃ H : Subgroup G,
          I ≤ H ∧ H < ⊤ ∧
            ∃ W : Subrepresentation (ρ.comp H.subtype),
              W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
          (let ρI : Representation k I V := ρ.comp I.subtype
           letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
           IsIsotypic (MonoidAlgebra k I) V) :=
      exists_proper_overgroup_irreducible_induced_or_restriction_isotypic_of_semisimple_restriction
        I ρ hsemisimple
    rcases hsplit with hproper | hIsotypic
    · -- In the non-isotypic branch, recurse on the proper stabilizer overgroup and then induce
      -- the lifted representation back to `G`.
      exact
        exists_residueFieldLift_of_proper_overgroup_induced_hall
          (p := p) (A := A) (h := h) (G := G) (V := V)
          hp I hIcop hquot hrecSame ρ hproper
    · -- In the isotypic branch, LinearRepresentations_Serre_1977's projective-extension construction is the remaining step.
      exact
        exists_residueFieldLift_of_restriction_isotypic_via_projective_extension
          (p := p) (A := A) (h := h) (G := G) (V := V)
          hp I hIcop hquot hrecLower ρ hIsotypic

-- Proof sketch: recurse outermost on the ambient cardinal bound and only then on the height, so
-- the proper-stabilizer Hall branch gets access to same-height recursion on smaller groups while
-- the quotient branch keeps the lower-height recursion.
/-- Helper for Theorem 17-17.6-1: explicit height induction together with a cardinal bound, so the
same-height recursive call is available on proper subgroups. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight_aux
    (hp : Nat.Prime p) :
    ∀ {h' n : ℕ} {G' : Type v} [Group G'] [Finite G']
      {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (hG' : IsPSolvableOfHeight p h' G') (hcard : Nat.card G' ≤ n)
      (ρ : Representation k G' V') [ρ.IsIrreducible],
        ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
            IsResidueFieldLift ρ ρA red := by
  intro h'
  induction h' with
  | zero =>
      intro n G' _ _ V' _ _ _ hG' hcard ρ _
      letI : Fact p.Prime := ⟨hp⟩
      letI : Subsingleton G' := hG'
      letI : Unique G' := { default := 1, uniq := fun g ↦ Subsingleton.elim g 1 }
      -- At height `0` the group is trivial, so the prime-to-`p` lifting theorem applies
      -- directly to the whole group.
      have hcardG' : Nat.card G' = 1 := by
        exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      have hGcop : ¬ p ∣ Nat.card G' := by
        simpa [hcardG'] using hp.not_dvd_one
      rcases exists_residueFieldLift_of_non_dvd_card_witness (A := A) (p := p) hGcop ρ with
        ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
      exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  | succ h ihh =>
      intro n
      induction n with
      | zero =>
          intro G' _ _ V' _ _ _ hG' hcard ρ _
          have hfalse : False := (Nat.not_lt_of_ge hcard) Nat.card_pos
          exact False.elim hfalse
      | succ n ihn =>
          intro G' _ _ V' _ _ _ hG' hcard ρ _
          letI : Fact p.Prime := ⟨hp⟩
          rcases (IsPSolvableOfHeight.succ_iff.mp hG') with ⟨I, hI, hstep, hquot⟩
          rcases hstep with hIcop | hIp
          · letI : I.Normal := hI
            -- Route correction: the proper-subgroup branch still descends on cardinality, but
            -- the lower-height branch now comes directly from the outer height induction with no
            -- ambient cardinal bound.
            have hrecSame :
                ∀ {H : Subgroup G'} {W : Type x} [AddCommGroup W] [Module k W]
                  [FiniteDimensional k W]
                  (hH : H < ⊤)
                  (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
                  (σ : Representation k H W) [σ.IsIrreducible],
                    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
                      (_ : Module.Free A P) (_ : Module.Finite A P)
                      (ρA : Representation A H P)
                      (red : P →ₗ[A] W),
                        IsResidueFieldLift σ ρA red := by
              intro H W _ _ _ hH hHG σ _
              have hcardH : Nat.card H ≤ n := by
                exact
                  Nat.lt_succ_iff.mp <|
                    lt_of_lt_of_le (subgroup_natCard_lt_of_ne_top H hH.ne) hcard
              rcases ihn hHG hcardH σ with
                ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
              exact ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
            have hrecLower :
                ∀ {G'' : Type v} [Group G''] [Finite G'']
                  {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
                  (hG'' : IsPSolvableOfHeight p h G'')
                  (σ : Representation k G'' W) [σ.IsIrreducible],
                    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
                      (_ : Module.Free A P) (_ : Module.Finite A P)
                      (ρA : Representation A G'' P)
                      (red : P →ₗ[A] W),
                        IsResidueFieldLift σ ρA red := by
              intro G'' _ _ W _ _ _ hG'' σ _
              exact
                @ihh (Nat.card G'') G'' _ _ W _ _ _ hG''
                  (le_rfl : Nat.card G'' ≤ Nat.card G'') σ inferInstance
            exact
              exists_residueFieldLift_of_isIrreducible_of_normal_coprime_kernel
                hp I hI hIcop hquot hrecSame hrecLower ρ
          · letI : I.Normal := hI
            letI : Representation.IsTrivial (ρ.comp I.subtype) :=
              isTrivial_restrict_normal_pSubgroup_of_isIrreducible ρ I hIp
            let τ : Representation k (G' ⧸ I) V' := ρ.ofQuotient I
            letI : τ.IsIrreducible := isIrreducible_of_ofQuotient_of_isTrivial ρ I
            -- Descend through the trivial `p`-kernel, recurse on the strictly lower height
            -- quotient with its own cardinal bound, then inflate back to `G'`.
            exact
              exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
                (A := A) (ρ := ρ) (I := I)
                (@ihh (Nat.card (G' ⧸ I)) (G' ⧸ I) _ _ V' _ _ _
                  hquot (le_rfl : Nat.card (G' ⧸ I) ≤ Nat.card (G' ⧸ I)) τ inferInstance)

/-- The height-indexed inductive form of Theorem `17-17.6-1`, phrased on the primitive recursive
`p`-solvable data. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight
    (hp : Nat.Prime p) (hG : IsPSolvableOfHeight p h G) (ρ : Representation k G V)
    [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Specialize the explicit `(height, card)` recursion at the actual ambient group order.
  exact
    exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight_aux
      (A := A) (p := p) (h' := h) (G' := G) (V' := V)
      hp hG (le_rfl : Nat.card G ≤ Nat.card G) ρ

/-- Theorem 17-17.6-1: if `A` is henselian local and the finite group `G` is `p`-solvable, then
every finite-dimensional irreducible representation of `G` over the residue field of `A` admits a
free finitely generated lift. Equivalently, every simple finite-dimensional `k[G]`-module lifts
to a free finitely generated `A[G]`-module. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hG with ⟨h, hG⟩
  exact exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight hp hG ρ

end

end Representation
