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
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedProjectiveCoverData
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelOwnerTransport

universe u v w x

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

/-- Helper for Theorem 17-17.6-1: a subrepresentation whose underlying owner submodule is `⊤`
is equivariantly the ambient representation. -/
noncomputable def top_subrepresentation_equiv_of_toSubmodule_eq_top
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
theorem scalar_representation_self_equiv_isIntertwining
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (a : kˣ) :
    σ.IsIntertwiningMap σ (((a • LinearEquiv.refl k W : W ≃ₗ[k] W) : W →ₗ[k] W)) := by
  -- A scalar homothety commutes with every representation operator on the nose.
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  simp [mul_comm]

/-- Helper for Theorem 17-17.6-1: package a scalar unit as the corresponding representation
self-equivalence. This keeps later transport corrections in the language of representation
equivalences instead of raw linear maps. -/
noncomputable def scalar_representation_self_equiv
    {G' : Type*} [Group G']
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G' W)
    (a : kˣ) :
    σ.Equiv σ :=
  Representation.Equiv.mk
    (a • LinearEquiv.refl k W)
    (fun g ↦ by
      ext x
      simp)

/-- Helper for Theorem 17-17.6-1: once Serre's constituent `S̄` is fixed, the literal
multiplicity-space carrier is `Hom^I(S̄, V)`. Naming this owner avoids reopening the carrier
choice in later projective-extension lemmas. -/
abbrev fixed_isotypic_multiplicity_space
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) : Type x :=
  Sbar.toRepresentation.IntertwiningMap (ρ.comp I.subtype)

/-- Helper for Theorem 17-17.6-1: Serre's multiplicity space `Hom^I(S̄, V)` is finite-dimensional,
since it sits inside the finite-dimensional space of all linear maps from `S̄` to `V`. -/
noncomputable def fixed_isotypic_multiplicity_space_finiteDimensional
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    FiniteDimensional k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
  -- Unfold the carrier once; the ambient intertwining space inherits finite-dimensionality from
  -- the finite-dimensional source and target representations.
  dsimp [fixed_isotypic_multiplicity_space]
  infer_instance

/-- Helper for Theorem 17-17.6-1: changing the source constituent by an `I`-equivariant
equivalence transports Serre's multiplicity space by precomposition. This is the basic source-side
bridge needed before descending the `G₂`-action to the quotient module `τ`. -/
noncomputable def fixed_isotypic_multiplicity_space_precompose_linearEquiv
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
noncomputable def transported_fixed_isotypic_multiplicity_space_linearEquiv
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    (e : Sbar.toRepresentation.Equiv (transportedSubrepresentation ρ Sbar s).toRepresentation) →
    fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar
  | e =>
      fixed_isotypic_multiplicity_space_precompose_linearEquiv
        (I := I) (ρ := ρ) e

/-- Helper for Theorem 17-17.6-1: if the transport element already lies in the Hall kernel `I`,
then transporting the fixed constituent `S̄` does not change the underlying subrepresentation.
This isolates the literal `I`-stability fact needed in the remaining Hall-kernel comparison
branch. -/
theorem transportedSubrepresentation_eq_self_of_mem_hall_kernel
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
theorem residueFieldLift_of_equiv_target_local
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

end

end Representation
