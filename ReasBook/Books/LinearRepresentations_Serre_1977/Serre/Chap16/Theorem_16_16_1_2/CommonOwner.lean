import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.BrauerMultiplicity

noncomputable section

universe u v

namespace Representation

open CategoryTheory
open scoped MonoidAlgebra Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2: the representation-level `asModule` owner of a finite
projective `k[G]`-module is itself projective over the group algebra. -/
private theorem projective_toRep_asModule_projective_commonOwner
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective (MonoidAlgebra k G) P.toRep.ρ.asModule := by
  -- Transport projectivity from the original finite-projective owner through the counit
  -- equivalence between representations and group-algebra modules.
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
    (Module.Projective.of_equiv'
      ((Rep.counitIso P.V).toLinearEquiv.symm) :
      Module.Projective (MonoidAlgebra k G)
        ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj P.V))

/-- Helper for Theorem 16-16.1-2: the stable owner for equivariant module maps between two
finite-dimensional representations. -/
private abbrev fdRepModuleHomSpace_commonOwner (M N : FDRep k G) :=
  Representation.asModule M.ρ →ₗ[MonoidAlgebra k G] Representation.asModule N.ρ

/-- Helper for Theorem 16-16.1-2: the `asModule` owner of an `FDRep` keeps its base-field
module structure. -/
private instance fdRepAsModuleModule_commonOwner (M : FDRep k G) :
    Module k (Representation.asModule M.ρ) :=
  representation_asModuleModule M.ρ

/-- Helper for Theorem 16-16.1-2: the `asModule` owner of an `FDRep` keeps its group-algebra
module structure. -/
private instance fdRepAsModuleGroupAlgebraModule_commonOwner (M : FDRep k G) :
    Module (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
  inferInstance

/-- Helper for Theorem 16-16.1-2: the `asModule` owner of an `FDRep` has the expected scalar
tower from the base field to the group algebra. -/
private instance fdRepAsModuleIsScalarTower_commonOwner (M : FDRep k G) :
    IsScalarTower k (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
  representation_asModule_isScalarTower M.ρ

/-- Helper for Theorem 16-16.1-2: the `asModule` owner of an `FDRep` is finite-dimensional over
the base field. -/
private instance fdRepAsModuleFiniteDimensional_commonOwner (M : FDRep k G) :
    @FiniteDimensional k (Representation.asModule M.ρ) inferInstance inferInstance
      (fdRepAsModuleModule_commonOwner M) := by
  -- The carrier of an `FDRep` is finite over the base field, and `asModule` is a type synonym.
  change Module.Finite k M
  infer_instance

/-- Helper for Theorem 16-16.1-2: the stable FDRep Hom-space owner carries its natural
`k`-module structure. -/
private instance fdRepModuleHomSpaceModule_commonOwner (M N : FDRep k G) :
    Module k (fdRepModuleHomSpace_commonOwner M N) := by
  letI : Module k (Representation.asModule M.ρ) := fdRepAsModuleModule_commonOwner M
  letI : Module k (Representation.asModule N.ρ) := fdRepAsModuleModule_commonOwner N
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
    fdRepAsModuleIsScalarTower_commonOwner M
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule N.ρ) :=
    fdRepAsModuleIsScalarTower_commonOwner N
  -- Install the scalar structures once at the named owner, avoiding repeated synthesis through
  -- the raw `IntertwiningMap`/`asModule` transport in later finrank calculations.
  delta fdRepModuleHomSpace_commonOwner
  infer_instance

/-- Helper for Theorem 16-16.1-2: intertwining maps are linearly equivalent to the stable
`k[G]`-linear Hom-space owner. -/
private noncomputable abbrev fdRepIntertwiningLinearEquivModuleHomSpace_commonOwner
    (M N : FDRep k G) :
    Representation.IntertwiningMap M.ρ N.ρ ≃ₗ[k]
      fdRepModuleHomSpace_commonOwner M N :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := N.ρ)

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: projectivity of `F` swaps the two representation-level
intertwining dimensions. This is the Hom-symmetry part of Serre's Brauer reciprocity argument. -/
theorem projectiveIntertwining_finrank_swap_commonOwner
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) =
      Module.finrank k (F.toRep.ρ.IntertwiningMap E.ρ) := by
  let P : FDRep k G := F.toFiniteRep
  have hproj : Module.Projective (MonoidAlgebra k G) (Representation.asModule P.ρ) := by
    -- The projective owner `F` and its finite-representation wrapper have the same
    -- representation-level `asModule` carrier.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      projective_toRep_asModule_projective_commonOwner (G := G) F
  letI : Module.Projective (MonoidAlgebra k G) (Representation.asModule P.ρ) := hproj
  letI : Module k (Representation.asModule E.ρ) := fdRepAsModuleModule_commonOwner E
  letI : Module (MonoidAlgebra k G) (Representation.asModule E.ρ) :=
    fdRepAsModuleGroupAlgebraModule_commonOwner E
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule E.ρ) :=
    fdRepAsModuleIsScalarTower_commonOwner E
  letI : @FiniteDimensional k (Representation.asModule E.ρ) inferInstance inferInstance
      (fdRepAsModuleModule_commonOwner E) :=
    fdRepAsModuleFiniteDimensional_commonOwner E
  letI : Module k (Representation.asModule P.ρ) := fdRepAsModuleModule_commonOwner P
  letI : Module (MonoidAlgebra k G) (Representation.asModule P.ρ) :=
    fdRepAsModuleGroupAlgebraModule_commonOwner P
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule P.ρ) :=
    fdRepAsModuleIsScalarTower_commonOwner P
  letI : @FiniteDimensional k (Representation.asModule P.ρ) inferInstance inferInstance
      (fdRepAsModuleModule_commonOwner P) :=
    fdRepAsModuleFiniteDimensional_commonOwner P
  letI : Module k (fdRepModuleHomSpace_commonOwner E P) :=
    fdRepModuleHomSpaceModule_commonOwner E P
  letI : Module k (fdRepModuleHomSpace_commonOwner P E) :=
    fdRepModuleHomSpaceModule_commonOwner P E
  have hleft :
      Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner E P) := by
    -- Move the left intertwining owner to the stable module-Hom owner.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (fdRepIntertwiningLinearEquivModuleHomSpace_commonOwner E P).finrank_eq
  have hright :
      Module.finrank k (F.toRep.ρ.IntertwiningMap E.ρ) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner P E) := by
    -- Move the right intertwining owner to the same stable module-Hom world.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (fdRepIntertwiningLinearEquivModuleHomSpace_commonOwner P E).finrank_eq
  have hcarrier :
      Module.finrank k (fdRepModuleHomSpace_commonOwner P E) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner E P) := by
    -- Apply the carrier-level projective Hom-symmetry theorem with `P` as the projective
    -- source, then fold the raw Hom spaces back into the stable owner.
    exact @finrank_hom_eq_finrank_hom_swap_of_projective
      k inferInstance G inferInstance inferInstance
      (Representation.asModule P.ρ) inferInstance
      (fdRepAsModuleModule_commonOwner P)
      (fdRepAsModuleGroupAlgebraModule_commonOwner P)
      (fdRepAsModuleIsScalarTower_commonOwner P)
      (Representation.asModule E.ρ) inferInstance
      (fdRepAsModuleModule_commonOwner E)
      (fdRepAsModuleGroupAlgebraModule_commonOwner E)
      (fdRepAsModuleIsScalarTower_commonOwner E)
      hproj
      (fdRepAsModuleFiniteDimensional_commonOwner P)
      (fdRepAsModuleFiniteDimensional_commonOwner E)
  exact hleft.trans (hcarrier.symm.trans hright.symm)

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2: the Jacobson-radical quotient of a projective-envelope source
is the simple target it envelopes. -/
theorem projectiveEnvelope_jacobson_quotient_linearEquiv_target_commonOwner
    {ι : Type v}
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i : ι) :
    Nonempty (((P i).V ⧸ Module.jacobson k[G] (P i).V) ≃ₗ[k[G]]
      Representation.asModule (π i).ρ) := by
  letI : Simple (π i) := hπ_complete.isSimple i
  let ρi : Representation k G (π i) := (π i).ρ
  let M : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π i))
  let f : (P i).V →ₗ[k[G]] M := by
    simpa [M, Rep.toModuleMonoidAlgebra] using Classical.choose (hP_envelope i)
  have hf : f.IsProjectiveEnvelope := by
    simpa [M, Rep.toModuleMonoidAlgebra] using Classical.choose_spec (hP_envelope i)
  letI : f.IsProjectiveEnvelope := hf
  have hsimple :
      IsSimpleModule k[G] M := by
    have hρi_irred : Representation.IsIrreducible ρi := by
      simpa [ρi] using (FDRep.isIrreducible_of_simple (π i))
    simpa [M, Rep.toModuleMonoidAlgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρi).mp hρi_irred
  letI : IsSimpleModule k[G] M := hsimple
  have hjac_le : Module.jacobson k[G] (P i).V ≤ LinearMap.ker f := by
    -- The target is simple, so its Jacobson radical is zero and maps from the source radical
    -- vanish after composing with the envelope map.
    have hcomap :
        Module.jacobson k[G] (P i).V ≤ Submodule.comap f (Module.jacobson k[G] M) :=
      Module.le_comap_jacobson (f := f)
    have hEq : Submodule.comap f (Module.jacobson k[G] M) = LinearMap.ker f := by
      rw [IsSimpleModule.jacobson_eq_bot (R := k[G]) (M := M), LinearMap.ker]
    exact hEq ▸ hcomap
  have hker_le : LinearMap.ker f ≤ Module.jacobson k[G] (P i).V := by
    -- Essentiality of the projective envelope gives the reverse containment.
    exact hf.toIsEssential.ker_le_jacobson hf.surjective
  have hker : Module.jacobson k[G] (P i).V = LinearMap.ker f := le_antisymm hjac_le hker_le
  refine ⟨?_⟩
  -- With the kernel identified, the quotient by the radical is the envelope target.
  simpa [M, Rep.toModuleMonoidAlgebra] using
    (Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective f hf.surjective)

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2: every equivariant map into a simple target kills the Jacobson
radical of its source. -/
theorem jacobson_le_ker_of_simple_target_commonOwner
    {M : Type u} [AddCommGroup M] [Module k[G] M]
    {N : Type u} [AddCommGroup N] [Module k[G] N] [IsSimpleModule k[G] N]
    (f : M →ₗ[k[G]] N) :
    Module.jacobson k[G] M ≤ LinearMap.ker f := by
  -- Pull the zero radical of the simple target back along the given map.
  have hcomap :
      Module.jacobson k[G] M ≤ Submodule.comap f (Module.jacobson k[G] N) :=
    Module.le_comap_jacobson (f := f)
  have hEq : Submodule.comap f (Module.jacobson k[G] N) = LinearMap.ker f := by
    rw [IsSimpleModule.jacobson_eq_bot (R := k[G]) (M := N), LinearMap.ker]
  exact hEq ▸ hcomap

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: maps from a projective envelope `P_i` into a simple `E_j`
have the same finrank as maps from the enveloped simple `E_i` into `E_j`. -/
theorem projectiveEnvelope_intertwining_finrank_eq_simple_intertwining_commonOwner
    {ι : Type v}
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i j : ι) :
    Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
      Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) := by
  let ρi : Representation k G (π i) := (π i).ρ
  let ρj : Representation k G (π j) := (π j).ρ
  let Mi : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π i))
  let Mj : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π j))
  letI : Simple (π j) := hπ_complete.isSimple j
  letI : Representation.IsIrreducible ρj := by
    simpa [ρj] using (FDRep.isIrreducible_of_simple (π j))
  have hMj_simple : IsSimpleModule k[G] Mj := by
    simpa [Mj, Rep.toModuleMonoidAlgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρj).mp inferInstance
  letI : IsSimpleModule k[G] Mj := hMj_simple
  let J : Submodule k[G] (P i).V := Module.jacobson k[G] (P i).V
  let precompQ :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) →ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) := by
    refine
      { toFun := fun g ↦ LinearMap.comp g (Submodule.mkQ J)
        map_add' := ?_
        map_smul' := ?_ }
    · intro g h
      ext x
      rfl
    · intro a g
      ext x
      rfl
  have hprecompQ_bijective : Function.Bijective precompQ := by
    constructor
    · intro g h hEq
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn' x ?_
      intro y
      simpa [precompQ, LinearMap.comp_apply] using LinearMap.congr_fun hEq y
    · intro f
      have hJker : J ≤ LinearMap.ker f := by
        change Module.jacobson k[G] (P i).V ≤ LinearMap.ker f
        exact jacobson_le_ker_of_simple_target_commonOwner (M := (P i).V) (N := Mj) f
      refine ⟨J.liftQ f hJker, ?_⟩
      simp [precompQ]
  let liftQEquiv :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) ≃ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) :=
    LinearEquiv.ofBijective precompQ hprecompQ_bijective
  let eQuot :
      ((P i).V ⧸ J) ≃ₗ[k[G]] Mi := by
    simpa [Mi, Rep.toModuleMonoidAlgebra] using
      (Classical.choice <|
        projectiveEnvelope_jacobson_quotient_linearEquiv_target_commonOwner
          π hπ_complete P hP_envelope i)
  let quotTargetHomEquiv :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) ≃ₗ[k]
        (Mi →ₗ[k[G]] Mj) :=
    LinearEquiv.congrLeft (M := Mj) k eQuot
  let eP :
      (P i).toRep.ρ.asModule ≃ₗ[k[G]] (P i).V := by
    simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.counitIso (P i).V).toLinearEquiv
  let projectiveOwnerHomEquiv :
      ((P i).toRep.ρ.asModule →ₗ[k[G]] Mj) ≃ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) :=
    LinearEquiv.congrLeft (M := Mj) k eP
  have hleft :
      Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner ((P i).toFiniteRep) (π j)) := by
    -- Read intertwiners out of the projective owner as `k[G]`-linear maps.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (fdRepIntertwiningLinearEquivModuleHomSpace_commonOwner ((P i).toFiniteRep) (π j)).finrank_eq
  have hright :
      Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner (π i) (π j)) := by
    -- Read the simple-to-simple intertwiners in the same module-Hom owner.
    exact (fdRepIntertwiningLinearEquivModuleHomSpace_commonOwner (π i) (π j)).finrank_eq
  calc
    Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
        Module.finrank k (fdRepModuleHomSpace_commonOwner ((P i).toFiniteRep) (π j)) := hleft
    _ = Module.finrank k ((P i).V →ₗ[k[G]] Mj) := by
          simpa [fdRepModuleHomSpace_commonOwner,
            FiniteProjectiveGroupAlgebraModule.toFiniteRep, Mj, Rep.toModuleMonoidAlgebra] using
            LinearEquiv.finrank_eq projectiveOwnerHomEquiv
    _ = Module.finrank k (((P i).V ⧸ J) →ₗ[k[G]] Mj) := by
          symm
          exact LinearEquiv.finrank_eq liftQEquiv
    _ = Module.finrank k (Mi →ₗ[k[G]] Mj) := by
          exact LinearEquiv.finrank_eq quotTargetHomEquiv
    _ = Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) := by
          simpa [fdRepModuleHomSpace_commonOwner, Mi, Mj, Rep.toModuleMonoidAlgebra] using
            hright.symm

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: the Brauer-reciprocity Hom comparison attached to a
projective-envelope family. -/
theorem projectiveEnvelope_brauerReciprocity_finrank_commonOwner
    {ι : Type v}
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i j : ι) :
    Module.finrank k (Representation.IntertwiningMap (π j).ρ (P i).toRep.ρ) =
      Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) := by
  -- First swap the two Hom owners using projectivity of `P_i`, then replace maps from `P_i`
  -- by maps from the simple quotient `E_i`.
  exact
    (projectiveIntertwining_finrank_swap_commonOwner (G := G) (E := π j) (F := P i)).trans
      (projectiveEnvelope_intertwining_finrank_eq_simple_intertwining_commonOwner
        (G := G) π hπ_complete P hP_envelope i j)

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2: over an algebraically closed residue field, simple-simple
intertwining dimensions are Kronecker deltas. -/
theorem simpleIntertwining_finrank_eq_delta_commonOwner
    {ι : Type v}
    [DecidableEq ι] [IsAlgClosed k]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i j : ι) :
    Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    letI : Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    let scalarMap : k →ₗ[k] Representation.IntertwiningMap (π i).ρ (π i).ρ :=
      { toFun := fun c ↦ c • (1 : Representation.IntertwiningMap (π i).ρ (π i).ρ)
        map_add' := by
          intro a b
          simp [add_smul]
        map_smul' := by
          intro a b
          simp [smul_smul] }
    have hscalar_bijective : Function.Bijective scalarMap := by
      simpa [scalarMap] using
        (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
          (ρ := (π i).ρ))
    let eScalar :
        k ≃ₗ[k] Representation.IntertwiningMap (π i).ρ (π i).ρ :=
      LinearEquiv.ofBijective scalarMap hscalar_bijective
    have hfin :
        Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1 := by
      rw [← LinearEquiv.finrank_eq eScalar]
      simp
    simp [hfin]
  · letI : Simple (π i) := hπ_complete.isSimple i
    letI : Simple (π j) := hπ_complete.isSimple j
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
    have hzero : ∀ f : Representation.IntertwiningMap (π i).ρ (π j).ρ, f = 0 := by
      intro f
      by_contra hf
      have hbij :
          Function.Bijective f :=
        (Representation.IsIrreducible.bijective_or_eq_zero
          (ρ := (π i).ρ) (σ := (π j).ρ) f).resolve_right hf
      have hIso : Nonempty (π i ≅ π j) :=
        ⟨(f.ofBijective hbij).toFDRepIso⟩
      exact (hπ_pairwise hij) hIso
    have hSub : Subsingleton (Representation.IntertwiningMap (π i).ρ (π j).ρ) := by
      refine ⟨fun f g ↦ ?_⟩
      rw [hzero f, hzero g]
    have hfin0 :
        Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) = 0 :=
      Module.finrank_eq_zero_of_subsingleton
        (R := k) (M := Representation.IntertwiningMap (π i).ρ (π j).ρ)
    simp [hij]

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: over an algebraically closed residue field, the
projective-envelope Brauer-reciprocity Hom comparison is the Kronecker-delta pairing. -/
theorem projectiveEnvelope_brauerReciprocity_finrank_eq_delta_commonOwner
    {ι : Type v}
    [DecidableEq ι] [IsAlgClosed k]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i j : ι) :
    Module.finrank k (Representation.IntertwiningMap (π j).ρ (P i).toRep.ρ) =
      if i = j then 1 else 0 := by
  exact
    (projectiveEnvelope_brauerReciprocity_finrank_commonOwner
      (G := G) π hπ_complete P hP_envelope i j).trans
      (simpleIntertwining_finrank_eq_delta_commonOwner
        (G := G) π hπ_pairwise hπ_complete i j)

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): for a projective module `P` over a
group algebra `R` (here `R = k[G]`), the functor `Hom_R(P, -)` is exact, so its `k`-dimension is
additive over a short exact sequence `0 → N → M → Q → 0` of `R`-modules. This is the linear-algebra
core behind the projective-cover multiplicity formula. -/
private theorem projectiveHom_finrank_add_of_exact_commonOwner
    {R : Type u} [Ring R]
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P]
    {N M Q : Type u} [AddCommGroup N] [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R M] [Module R Q]
    [Algebra k R] [Module k P] [Module k N] [Module k M] [Module k Q]
    [IsScalarTower k R P] [IsScalarTower k R N] [IsScalarTower k R M] [IsScalarTower k R Q]
    [FiniteDimensional k P] [FiniteDimensional k N] [FiniteDimensional k M] [FiniteDimensional k Q]
    {f : N →ₗ[R] M} {g : M →ₗ[R] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.finrank k (P →ₗ[R] M) =
      Module.finrank k (P →ₗ[R] N) + Module.finrank k (P →ₗ[R] Q) := by
  -- `k`-linear postcomposition maps on the Hom spaces.
  let F : (P →ₗ[R] N) →ₗ[k] (P →ₗ[R] M) := LinearMap.compRight k f
  let G' : (P →ₗ[R] M) →ₗ[k] (P →ₗ[R] Q) := LinearMap.compRight k g
  -- The Hom spaces are finite-dimensional over `k` because they embed into the full `k`-Hom space.
  haveI : FiniteDimensional k (P →ₗ[R] N) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ k R P N k)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional k (P →ₗ[R] M) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ k R P M k)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional k (P →ₗ[R] Q) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ k R P Q k)
      (LinearMap.restrictScalars_injective _)
  -- Precomposition with the injective `f` is injective on Hom spaces.
  have hF_inj : Function.Injective F := by
    intro a b hab
    have hcomp : f.comp a = f.comp b := hab
    ext x
    exact hf (by simpa using LinearMap.congr_fun hcomp x)
  -- Postcomposition with the surjective `g` is surjective on Hom spaces by projectivity of `P`.
  have hG'_surj : Function.Surjective G' := by
    intro h
    obtain ⟨l, hl⟩ := Module.projective_lifting_property g h hg
    exact ⟨l, by simpa [G', LinearMap.compRight] using hl⟩
  have hgf0 : g.comp f = 0 := hfg.linearMap_comp_eq_zero
  -- The Hom sequence is exact at the middle term.
  have hExact : Function.Exact F G' := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · -- `ker G' ≤ range F`: a map killed by `g` factors through `f` because `range f = ker g`.
      intro h hh
      simp only [LinearMap.mem_ker] at hh
      have hgh : g.comp h = 0 := hh
      have hrange : LinearMap.range h ≤ LinearMap.range f := by
        rw [← LinearMap.exact_iff.mp hfg]
        intro z hz
        rcases hz with ⟨x, rfl⟩
        simp only [LinearMap.mem_ker]
        exact LinearMap.congr_fun hgh x
      let e : N ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
      let hcod : P →ₗ[R] LinearMap.range f :=
        LinearMap.codRestrict (LinearMap.range f) h (fun x => hrange ⟨x, rfl⟩)
      refine ⟨e.symm.toLinearMap.comp hcod, ?_⟩
      change F (e.symm.toLinearMap.comp hcod) = h
      ext x
      have hfe : f (e.symm (hcod x)) = (hcod x : M) := by
        have h1 : (e (e.symm (hcod x)) : M) = f (e.symm (hcod x)) := by
          rw [LinearEquiv.ofInjective_apply]
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      have hcodx : (hcod x : M) = h x := by simp [hcod]
      simpa [F, LinearMap.compRight, hcodx] using hfe.trans hcodx
    · -- `range F ≤ ker G'`: the composite `g ∘ f` already vanishes.
      rintro _ ⟨a, rfl⟩
      simp only [LinearMap.mem_ker]
      change G' (F a) = 0
      have hzero : g.comp (f.comp a) = 0 := by
        rw [← LinearMap.comp_assoc, hgf0, LinearMap.zero_comp]
      simpa [G', F, LinearMap.compRight] using hzero
  -- Rank–nullity for `G'`, with `range G' = ⊤` (surjective) and `ker G' = range F ≅ Hom(P, N)`.
  have hrn := LinearMap.finrank_range_add_finrank_ker G'
  have hrangeG' : Module.finrank k (LinearMap.range G') = Module.finrank k (P →ₗ[R] Q) := by
    rw [LinearMap.range_eq_top.mpr hG'_surj]
    exact finrank_top _ _
  have hkerG' : Module.finrank k (LinearMap.ker G') = Module.finrank k (P →ₗ[R] N) := by
    have hke : LinearMap.ker G' = LinearMap.range F := LinearMap.exact_iff.mp hExact
    rw [hke, ← (LinearEquiv.ofInjective F hF_inj).finrank_eq]
  rw [hrangeG', hkerG'] at hrn
  lia

omit [HenselianLocalRing A] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): the `k`-dimension of the
intertwining space `Hom(P, -)` out of a finite projective `k[G]`-module is additive along a short
exact sequence of finite-dimensional representations. -/
theorem projectiveHom_intertwining_finrank_add_of_shortExact_commonOwner
    (Pi : FiniteProjectiveGroupAlgebraModule k G)
    (T : ShortComplex (FDRep k G)) (hT : T.ShortExact) :
    Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₂.ρ) =
      Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₁.ρ) +
        Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₃.ρ) := by
  -- Transport the FDRep short exact sequence down to the underlying `k[G]`-modules, mirroring the
  -- multiplicity-additivity proof.
  let ρ₁ : Representation k G T.X₁ := T.X₁.ρ
  let ρ₂ : Representation k G T.X₂ := T.X₂.ρ
  let ρ₃ : Representation k G T.X₃ := T.X₃.ρ
  letI : Module k[G] T.X₁ := by simpa using (inferInstance : Module k[G] ρ₁.asModule)
  letI : Module k[G] T.X₂ := by simpa using (inferInstance : Module k[G] ρ₂.asModule)
  letI : Module k[G] T.X₃ := by simpa using (inferInstance : Module k[G] ρ₃.asModule)
  letI : IsScalarTower k k[G] T.X₁ := by simpa using (inferInstance : IsScalarTower k k[G] ρ₁.asModule)
  letI : IsScalarTower k k[G] T.X₂ := by simpa using (inferInstance : IsScalarTower k k[G] ρ₂.asModule)
  letI : IsScalarTower k k[G] T.X₃ := by simpa using (inferInstance : IsScalarTower k k[G] ρ₃.asModule)
  let F : FDRep k G ⥤ ModuleCat k[G] :=
    forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra
  let U : ShortComplex (ModuleCat k[G]) := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  let f : T.X₁ →ₗ[k[G]] T.X₂ := by simpa [U, F] using U.f.hom
  let g : T.X₂ →ₗ[k[G]] T.X₃ := by simpa [U, F] using U.g.hom
  have hf : Function.Injective f := by simpa [f] using hU.moduleCat_injective_f
  have hg : Function.Surjective g := by simpa [g] using hU.moduleCat_surjective_g
  have hfg : Function.Exact f g := by
    simpa [f, g] using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  -- The source module owner is projective and finite-dimensional over the base field.
  haveI : Module.Projective k[G] (Representation.asModule Pi.toRep.ρ) := by
    simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
      (Module.Projective.of_equiv' ((Rep.counitIso Pi.V).toLinearEquiv.symm) :
        Module.Projective (MonoidAlgebra k G)
          ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj Pi.V))
  letI : Module k (Representation.asModule Pi.toRep.ρ) := representation_asModuleModule Pi.toRep.ρ
  letI : IsScalarTower k k[G] (Representation.asModule Pi.toRep.ρ) :=
    representation_asModule_isScalarTower Pi.toRep.ρ
  haveI : FiniteDimensional k (Representation.asModule Pi.toRep.ρ) := by
    have : Module.Finite k Pi.toRep := inferInstance
    delta Representation.asModule
    infer_instance
  haveI : FiniteDimensional k T.X₁ := inferInstanceAs (FiniteDimensional k T.X₁.V)
  haveI : FiniteDimensional k T.X₂ := inferInstanceAs (FiniteDimensional k T.X₂.V)
  haveI : FiniteDimensional k T.X₃ := inferInstanceAs (FiniteDimensional k T.X₃.V)
  -- Apply the linear-algebra core to the module Hom spaces.
  have hcore :
      Module.finrank k (Representation.asModule Pi.toRep.ρ →ₗ[k[G]] T.X₂) =
        Module.finrank k (Representation.asModule Pi.toRep.ρ →ₗ[k[G]] T.X₁) +
          Module.finrank k (Representation.asModule Pi.toRep.ρ →ₗ[k[G]] T.X₃) :=
    projectiveHom_finrank_add_of_exact_commonOwner
      (R := k[G]) (P := Representation.asModule Pi.toRep.ρ)
      (N := T.X₁) (M := T.X₂) (Q := T.X₃) hf hg hfg
  -- Translate each module-Hom dimension back to an intertwining-space dimension.
  have hbridge : ∀ σ : FDRep k G,
      Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ σ.ρ) =
        Module.finrank k (Representation.asModule Pi.toRep.ρ →ₗ[k[G]] Representation.asModule σ.ρ) :=
    fun σ ↦ (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Pi.toRep.ρ) (σ := σ.ρ)).finrank_eq
  rw [hbridge T.X₂, hbridge T.X₁, hbridge T.X₃]
  exact hcore

/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): the additive functional on the free
abelian group of finite-dimensional representations sending `[σ]` to `dim_k Hom(P_i, σ)`. -/
private noncomputable abbrev projectiveHomFinrankLift_commonOwner
    (Pi : FiniteProjectiveGroupAlgebraModule k G) :
    FreeAbelianGroup (FDRep k G) →+ ℤ :=
  FreeAbelianGroup.lift fun σ ↦
    (Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ σ.ρ) : ℤ)

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): the projective-Hom dimension lift
vanishes on the defining Grothendieck relations, because `Hom(P_i, -)` is exact and hence its
dimension is additive along short exact sequences. -/
private theorem finiteRepGrothendieckRelations_le_projectiveHomFinrankLift_ker_commonOwner
    (Pi : FiniteProjectiveGroupAlgebraModule k G) :
    finiteRepGrothendieckRelations k G ≤
      (projectiveHomFinrankLift_commonOwner (A := A) Pi).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨T, hT⟩, rfl⟩
  have hadd :
      Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₂.ρ) =
        Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₁.ρ) +
          Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ T.X₃.ρ) :=
    projectiveHom_intertwining_finrank_add_of_shortExact_commonOwner (A := A) Pi T hT
  change projectiveHomFinrankLift_commonOwner (A := A) Pi
    (FreeAbelianGroup.of T.X₂ - FreeAbelianGroup.of T.X₁ - FreeAbelianGroup.of T.X₃) = 0
  simp only [projectiveHomFinrankLift_commonOwner, map_sub, FreeAbelianGroup.lift_apply_of]
  rw [hadd]
  push_cast
  ring

/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): the descended additive functional
`R₀[k](G) →+ ℤ`, `[σ] ↦ dim_k Hom(P_i, σ)`. -/
private noncomputable def projectiveHomFinrankHom_commonOwner
    (Pi : FiniteProjectiveGroupAlgebraModule k G) :
    finiteRepGrothendieckGroup k G →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (projectiveHomFinrankLift_commonOwner (A := A) Pi)
    (finiteRepGrothendieckRelations_le_projectiveHomFinrankLift_ker_commonOwner (A := A) Pi)

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): the descended projective-Hom
dimension functional evaluates on an honest class `[M]` as `dim_k Hom(P_i, M)`. -/
private theorem projectiveHomFinrankHom_apply_class_commonOwner
    (Pi : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    projectiveHomFinrankHom_commonOwner (A := A) Pi [M]₀ =
      (Module.finrank k (Representation.IntertwiningMap Pi.toRep.ρ M.ρ) : ℤ) := by
  simp [projectiveHomFinrankHom_commonOwner, finiteRepGrothendieckClass,
    projectiveHomFinrankLift_commonOwner]

omit [HenselianLocalRing A] in
/-- Theorem 16-16.1-2 (Brauer reciprocity "Link 4"): if `P_i` is a projective envelope (projective
cover) of the simple module `E_i = π i` over an algebraically closed residue field, then the
`k`-dimension of `Hom_{k[G]}(P_i, M)` computes the Jordan–Hölder multiplicity of `E_i` in `M`.

Both sides are additive functionals on Serre's Grothendieck group `R₀[k](G)`: the left side because
`P_i` is projective (so `Hom(P_i, -)` is exact), the right side by additivity of composition
multiplicities; they agree on the simple generators by the Kronecker-delta computation, hence
everywhere. -/
theorem projectiveEnvelope_hom_finrank_eq_multiplicity_commonOwner
    {ι : Type v} [Fintype ι] [DecidableEq ι] [IsAlgClosed k]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope : ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) (M : FDRep k G) :
    Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ M.ρ) =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) [M]₀ := by
  classical
  letI : Simple (π i) := hπ_complete.isSimple i
  let b := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  -- The two additive functionals on `R₀[k](G)`: the projective-Hom dimension and the simple-class
  -- coordinate at `i`.
  let Φ : finiteRepGrothendieckGroup k G →+ ℤ := projectiveHomFinrankHom_commonOwner (A := A) (P i)
  let coord : finiteRepGrothendieckGroup k G →+ ℤ :=
    { toFun := fun y ↦ b.repr y i
      map_zero' := by simp
      map_add' := by intro y z; simp }
  -- They agree on every basis generator `[π j]`, where both compute the Kronecker delta `δ_{ij}`.
  have hbasis : ∀ j, Φ (b j) = coord (b j) := by
    intro j
    have hΦ : Φ (b j) = (if i = j then 1 else 0 : ℤ) := by
      have h1 : Φ (b j) =
          (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) : ℤ) := by
        rw [simple_finiteRep_classes_basis_of_complete_family_apply]
        exact projectiveHomFinrankHom_apply_class_commonOwner (A := A) (P i) (π j)
      have h2 :
          Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
            (if i = j then 1 else 0) := by
        rw [projectiveEnvelope_intertwining_finrank_eq_simple_intertwining_commonOwner
              (A := A) π hπ_complete P hP_envelope i j,
            simpleIntertwining_finrank_eq_delta_commonOwner
              (A := A) π hπ_pairwise hπ_complete i j]
      rw [h1, h2]; split <;> simp
    have hcoord : coord (b j) = (if i = j then 1 else 0 : ℤ) := by
      have hb : b.repr (b j) = Finsupp.single j (1 : ℤ) := by simpa using b.repr_self j
      show b.repr (b j) i = _
      rw [hb]
      simp [Finsupp.single_apply, eq_comm]
    rw [hΦ, hcoord]
  -- Two `ℤ`-linear functionals that agree on a basis are equal.
  have hΦeq : Φ.toIntLinearMap = coord.toIntLinearMap := by
    apply b.ext; intro j; exact hbasis j
  have hΦM : Φ [M]₀ = coord [M]₀ := by
    have hx := congrArg (fun f : finiteRepGrothendieckGroup k G →ₗ[ℤ] ℤ ↦ f [M]₀) hΦeq
    simpa using hx
  -- The coordinate functional is, by Proposition `14-14.1-1`, the multiplicity functional.
  have hcoordM :
      coord [M]₀ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) [M]₀ := by
    simp only [coord, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact simple_basis_coord_eq_fixed_simple_multiplicity_local
      (A := A) (G := G) (π i) π hπ_pairwise hπ_complete i ⟨Iso.refl _⟩ [M]₀
  -- Assemble: `dim Hom(P_i, M) = Φ [M] = coord [M] = mult(E_i, M)`.
  have hLHS : Φ [M]₀ = (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ M.ρ) : ℤ) :=
    projectiveHomFinrankHom_apply_class_commonOwner (A := A) (P i) M
  rw [← hLHS, hΦM, hcoordM]

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Brauer reciprocity "Link 1": for a complete pairwise-nonisomorphic family of simple
`K`-representations whose members are absolutely irreducible (`End_{K[G]}(πK i) = K`, i.e.
`dim_K Hom(πK i, πK i) = 1` — Serre's "K splitting field"), the simple-to-simple intertwining
dimensions are Kronecker deltas. The `i ≠ j` case is Schur's lemma (any field); the `i = j` case is
absolute irreducibility. -/
theorem simpleKIntertwining_finrank_eq_delta_commonOwner
    {ι : Type v}
    [DecidableEq ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_absIrr : ∀ i, Module.finrank K (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1)
    (i j : ι) :
    Module.finrank K (Representation.IntertwiningMap (π i).ρ (π j).ρ) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [hπ_absIrr i]
  · letI : Simple (π i) := hπ_complete.isSimple i
    letI : Simple (π j) := hπ_complete.isSimple j
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
    have hzero : ∀ f : Representation.IntertwiningMap (π i).ρ (π j).ρ, f = 0 := by
      intro f
      by_contra hf
      have hbij : Function.Bijective f :=
        (Representation.IsIrreducible.bijective_or_eq_zero
          (ρ := (π i).ρ) (σ := (π j).ρ) f).resolve_right hf
      have hIso : Nonempty (π i ≅ π j) := ⟨(f.ofBijective hbij).toFDRepIso⟩
      exact (hπ_pairwise hij) hIso
    have hSub : Subsingleton (Representation.IntertwiningMap (π i).ρ (π j).ρ) :=
      ⟨fun f g ↦ by rw [hzero f, hzero g]⟩
    have hfin0 :
        Module.finrank K (Representation.IntertwiningMap (π i).ρ (π j).ρ) = 0 :=
      Module.finrank_eq_zero_of_subsingleton
        (R := K) (M := Representation.IntertwiningMap (π i).ρ (π j).ρ)
    rw [hfin0]
    simp [hij]

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: the projective-envelope Hom dimension computes fixed-simple
multiplicity under an explicit absolute-irreducibility hypothesis, avoiding the stronger
`[IsAlgClosed k]` assumption. -/
theorem projectiveEnvelope_hom_finrank_eq_multiplicity_of_absIrr_commonOwner
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_absIrr :
      ∀ i, Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i : ι) (M : FDRep k G) :
    Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ M.ρ) =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) [M]₀ := by
  classical
  letI : Simple (π i) := hπ_complete.isSimple i
  let b := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  -- Compare the projective-Hom functional with the simple-basis coordinate by checking both on
  -- every simple generator of the complete family.
  let Φ : finiteRepGrothendieckGroup k G →+ ℤ :=
    projectiveHomFinrankHom_commonOwner (A := A) (P i)
  let coord : finiteRepGrothendieckGroup k G →+ ℤ :=
    { toFun := fun y ↦ b.repr y i
      map_zero' := by simp
      map_add' := by intro y z; simp }
  have hbasis : ∀ j, Φ (b j) = coord (b j) := by
    intro j
    have hΦ : Φ (b j) = (if i = j then 1 else 0 : ℤ) := by
      have h1 : Φ (b j) =
          (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) : ℤ) := by
        rw [simple_finiteRep_classes_basis_of_complete_family_apply]
        exact projectiveHomFinrankHom_apply_class_commonOwner (A := A) (P i) (π j)
      have h2 :
          Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
            (if i = j then 1 else 0) := by
        rw [projectiveEnvelope_intertwining_finrank_eq_simple_intertwining_commonOwner
              (A := A) π hπ_complete P hP_envelope i j,
            simpleKIntertwining_finrank_eq_delta_commonOwner
              (K := k) (G := G) π hπ_pairwise hπ_complete hπ_absIrr i j]
      rw [h1, h2]
      split <;> simp
    have hcoord : coord (b j) = (if i = j then 1 else 0 : ℤ) := by
      have hb : b.repr (b j) = Finsupp.single j (1 : ℤ) := by
        simpa using b.repr_self j
      show b.repr (b j) i = _
      rw [hb]
      simp [Finsupp.single_apply, eq_comm]
    rw [hΦ, hcoord]
  have hΦeq : Φ.toIntLinearMap = coord.toIntLinearMap := by
    apply b.ext
    intro j
    exact hbasis j
  have hΦM : Φ [M]₀ = coord [M]₀ := by
    have hx :=
      congrArg (fun f : finiteRepGrothendieckGroup k G →ₗ[ℤ] ℤ ↦ f [M]₀) hΦeq
    simpa using hx
  have hcoordM :
      coord [M]₀ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) [M]₀ := by
    simp only [coord, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact simple_basis_coord_eq_fixed_simple_multiplicity_local
      (A := A) (G := G) (π i) π hπ_pairwise hπ_complete i ⟨Iso.refl _⟩ [M]₀
  -- Evaluate the projective-Hom functional on the target class and pass through the coordinate
  -- comparison.
  have hLHS :
      Φ [M]₀ =
        (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ M.ρ) : ℤ) :=
    projectiveHomFinrankHom_apply_class_commonOwner (A := A) (P i) M
  rw [← hLHS, hΦM, hcoordM]

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-2: nonisomorphic simple representations have no nonzero
intertwiners, so their intertwining space has dimension zero. -/
theorem simpleIntertwining_finrank_eq_zero_of_ne_commonOwner
    {ι : Type v}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {i j : ι} (hij : i ≠ j) :
    Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) = 0 := by
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Simple (π j) := hπ_complete.isSimple j
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
  have hzero : ∀ f : Representation.IntertwiningMap (π i).ρ (π j).ρ, f = 0 := by
    intro f
    by_contra hf
    have hbij : Function.Bijective f :=
      (Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := (π i).ρ) (σ := (π j).ρ) f).resolve_right hf
    have hIso : Nonempty (π i ≅ π j) := ⟨(f.ofBijective hbij).toFDRepIso⟩
    exact (hπ_pairwise hij) hIso
  have hSub : Subsingleton (Representation.IntertwiningMap (π i).ρ (π j).ρ) :=
    ⟨fun f g ↦ by rw [hzero f, hzero g]⟩
  -- A vector space whose only element is zero has finrank zero.
  exact
    Module.finrank_eq_zero_of_subsingleton
      (R := k) (M := Representation.IntertwiningMap (π i).ρ (π j).ρ)

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: over an arbitrary field, the Hom dimension from a projective
envelope computes the fixed-simple multiplicity with the explicit Schur endomorphism weight. -/
theorem projectiveEnvelope_hom_finrank_eq_schurWeight_mul_multiplicity_commonOwner
    {ι : Type v}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i : ι) (M : FDRep k G) :
    (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ M.ρ) : ℤ) =
      (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) [M]₀ := by
  classical
  let b := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let weight : ℤ :=
    (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ)
  let Φ : finiteRepGrothendieckGroup k G →ₗ[ℤ] ℤ :=
    (projectiveHomFinrankHom_commonOwner (A := A) (P i)).toIntLinearMap
  let Ψ : finiteRepGrothendieckGroup k G →ₗ[ℤ] ℤ :=
    weight • (simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)).toIntLinearMap
  have hmaps : Φ = Ψ := by
    -- The two additive functionals are determined by their values on the simple-class basis.
    apply b.ext
    intro j
    have hΦclass :
        Φ (b j) =
          (Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) : ℤ) := by
      rw [simple_finiteRep_classes_basis_of_complete_family_apply]
      exact projectiveHomFinrankHom_apply_class_commonOwner (A := A) (P i) (π j)
    have hPtoSimple :
        Module.finrank k (Representation.IntertwiningMap (P i).toRep.ρ (π j).ρ) =
          Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) :=
      projectiveEnvelope_intertwining_finrank_eq_simple_intertwining_commonOwner
        (A := A) π hπ_complete P hP_envelope i j
    have hmultCoord :
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i) (b j) =
          b.repr (b j) i := by
      simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
        (simple_basis_coord_eq_fixed_simple_multiplicity_noFinite
          (A := A) (G := G) (S := π i) π hπ_pairwise hπ_complete
          i ⟨Iso.refl _⟩ [π j]₀).symm
    by_cases hji : j = i
    · subst j
      -- On the matching simple, both functionals read the Schur endomorphism dimension.
      calc
        Φ (b i) =
            (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) := by
              rw [hΦclass, hPtoSimple]
        _ = Ψ (b i) := by
              simp [Ψ, weight, hmultCoord]
    · have hij : i ≠ j := fun h ↦ hji h.symm
      have hsimpleZero :
          Module.finrank k (Representation.IntertwiningMap (π i).ρ (π j).ρ) = 0 :=
        simpleIntertwining_finrank_eq_zero_of_ne_commonOwner
          (A := A) π hπ_pairwise hπ_complete hij
      have hbij : b.repr (b j) i = 0 := by
        rw [b.repr_self j]
        exact Finsupp.single_eq_of_ne hij
      -- On a different simple, both functionals vanish.
      calc
        Φ (b j) = 0 := by
          rw [hΦclass, hPtoSimple, hsimpleZero]
          norm_num
        _ = Ψ (b j) := by
          rw [show Ψ (b j) =
              weight * simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
                (b j) by rfl]
          rw [hmultCoord, hbij, mul_zero]
  have hM := congrArg (fun f : finiteRepGrothendieckGroup k G →ₗ[ℤ] ℤ ↦ f [M]₀) hmaps
  -- Evaluate the functional identity on the target class and unfold both sides.
  simpa [Φ, Ψ, weight] using hM

omit [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K] [Finite G] in
/-- Helper for Brauer reciprocity "Link 1": the base-field-generic version of
`projectiveHom_finrank_add_of_exact_commonOwner`. For a projective module `P` over a ring `R`, the
functor `Hom_R(P, -)` is exact, so its `𝕜`-dimension is additive over a short exact sequence
`0 → N → M → Q → 0` of `R`-modules, where `𝕜` is any base field acting compatibly. -/
private theorem projectiveHom_finrank_add_of_exact_generic_commonOwner
    {𝕜 : Type u} [Field 𝕜]
    {R : Type u} [Ring R]
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P]
    {N M Q : Type u} [AddCommGroup N] [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R M] [Module R Q]
    [Algebra 𝕜 R] [Module 𝕜 P] [Module 𝕜 N] [Module 𝕜 M] [Module 𝕜 Q]
    [IsScalarTower 𝕜 R P] [IsScalarTower 𝕜 R N] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 R Q]
    [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 N] [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 Q]
    {f : N →ₗ[R] M} {g : M →ₗ[R] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.finrank 𝕜 (P →ₗ[R] M) =
      Module.finrank 𝕜 (P →ₗ[R] N) + Module.finrank 𝕜 (P →ₗ[R] Q) := by
  -- `𝕜`-linear postcomposition maps on the Hom spaces.
  let F : (P →ₗ[R] N) →ₗ[𝕜] (P →ₗ[R] M) := LinearMap.compRight 𝕜 f
  let G' : (P →ₗ[R] M) →ₗ[𝕜] (P →ₗ[R] Q) := LinearMap.compRight 𝕜 g
  haveI : FiniteDimensional 𝕜 (P →ₗ[R] N) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ 𝕜 R P N 𝕜)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional 𝕜 (P →ₗ[R] M) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ 𝕜 R P M 𝕜)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional 𝕜 (P →ₗ[R] Q) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ 𝕜 R P Q 𝕜)
      (LinearMap.restrictScalars_injective _)
  have hF_inj : Function.Injective F := by
    intro a b hab
    have hcomp : f.comp a = f.comp b := hab
    ext x
    exact hf (by simpa using LinearMap.congr_fun hcomp x)
  have hG'_surj : Function.Surjective G' := by
    intro h
    obtain ⟨l, hl⟩ := Module.projective_lifting_property g h hg
    exact ⟨l, by simpa [G', LinearMap.compRight] using hl⟩
  have hgf0 : g.comp f = 0 := hfg.linearMap_comp_eq_zero
  have hExact : Function.Exact F G' := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro h hh
      simp only [LinearMap.mem_ker] at hh
      have hgh : g.comp h = 0 := hh
      have hrange : LinearMap.range h ≤ LinearMap.range f := by
        rw [← LinearMap.exact_iff.mp hfg]
        intro z hz
        rcases hz with ⟨x, rfl⟩
        simp only [LinearMap.mem_ker]
        exact LinearMap.congr_fun hgh x
      let e : N ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
      let hcod : P →ₗ[R] LinearMap.range f :=
        LinearMap.codRestrict (LinearMap.range f) h (fun x => hrange ⟨x, rfl⟩)
      refine ⟨e.symm.toLinearMap.comp hcod, ?_⟩
      change F (e.symm.toLinearMap.comp hcod) = h
      ext x
      have hfe : f (e.symm (hcod x)) = (hcod x : M) := by
        have h1 : (e (e.symm (hcod x)) : M) = f (e.symm (hcod x)) := by
          rw [LinearEquiv.ofInjective_apply]
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      have hcodx : (hcod x : M) = h x := by simp [hcod]
      simpa [F, LinearMap.compRight, hcodx] using hfe.trans hcodx
    · rintro _ ⟨a, rfl⟩
      simp only [LinearMap.mem_ker]
      change G' (F a) = 0
      have hzero : g.comp (f.comp a) = 0 := by
        rw [← LinearMap.comp_assoc, hgf0, LinearMap.zero_comp]
      simpa [G', F, LinearMap.compRight] using hzero
  have hrn := LinearMap.finrank_range_add_finrank_ker G'
  have hrangeG' : Module.finrank 𝕜 (LinearMap.range G') = Module.finrank 𝕜 (P →ₗ[R] Q) := by
    rw [LinearMap.range_eq_top.mpr hG'_surj]
    exact finrank_top _ _
  have hkerG' : Module.finrank 𝕜 (LinearMap.ker G') = Module.finrank 𝕜 (P →ₗ[R] N) := by
    have hke : LinearMap.ker G' = LinearMap.range F := LinearMap.exact_iff.mp hExact
    rw [hke, ← (LinearEquiv.ofInjective F hF_inj).finrank_eq]
  rw [hrangeG', hkerG'] at hrn
  lia

/-! ### Brauer reciprocity "Link 1" (the `K`-side multiplicity-via-`Hom` formula)

Over a field `K` of characteristic `0` (so `K[G]` is semisimple by Maschke) that is a splitting
field for `G` (every simple `K[G]`-module `F` is absolutely irreducible, i.e.
`End_{K[G]}(F) = K`), the multiplicity of a simple `F` as a composition factor of a
finite-dimensional `K[G]`-module `V` equals `dim_K Hom_{K[G]}(V, F)`.  Concretely, in the
simple-class `ℤ`-basis of Serre's Grothendieck group `R₀[K](G)` (Proposition 14-14.1-1), the
`j`-th coordinate of `[V]` is `dim_K Hom_{K[G]}(V, πK j)`. -/

-- The `asModule` owner of a `K`-side `FDRep` keeps its base-field module structure.
private instance fdRepKAsModuleModule_commonOwner (M : FDRep K G) :
    Module K (Representation.asModule M.ρ) :=
  representation_asModuleModule M.ρ

-- The `asModule` owner of a `K`-side `FDRep` has the expected scalar tower.
private instance fdRepKAsModuleIsScalarTower_commonOwner (M : FDRep K G) :
    IsScalarTower K (MonoidAlgebra K G) (Representation.asModule M.ρ) :=
  representation_asModule_isScalarTower M.ρ

-- The `asModule` owner of a `K`-side `FDRep` is finite-dimensional over `K`.
private instance fdRepKAsModuleFiniteDimensional_commonOwner (M : FDRep K G) :
    @FiniteDimensional K (Representation.asModule M.ρ) inferInstance inferInstance
      (fdRepKAsModuleModule_commonOwner M) := by
  change Module.Finite K M
  infer_instance

omit [HenselianLocalRing A] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper for Brauer reciprocity "Link 1": over a field `K` with `Nat.card G` invertible
(Maschke), `K[G]` is semisimple, so every finite-dimensional `K`-representation is projective as a
`K[G]`-module. -/
private theorem fdRepK_asModule_projective_commonOwner [NeZero (Nat.card G : K)]
    (S : FDRep K G) :
    Module.Projective (MonoidAlgebra K G) (Representation.asModule S.ρ) :=
  Module.projective_of_isSemisimpleRing (MonoidAlgebra K G) (Representation.asModule S.ρ)

omit [HenselianLocalRing A] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper for Brauer reciprocity "Link 1": over a semisimple `K[G]` the `k`-dimension of the
intertwining space `Hom(S, -)` out of a finite-dimensional `K`-representation `S` is additive along
a short exact sequence of finite-dimensional representations (because `S` is projective, so
`Hom(S, -)` is exact). -/
theorem simpleHomK_intertwining_finrank_add_of_shortExact_commonOwner
    [NeZero (Nat.card G : K)]
    (S : FDRep K G)
    (T : ShortComplex (FDRep K G)) (hT : T.ShortExact) :
    Module.finrank K (Representation.IntertwiningMap S.ρ T.X₂.ρ) =
      Module.finrank K (Representation.IntertwiningMap S.ρ T.X₁.ρ) +
        Module.finrank K (Representation.IntertwiningMap S.ρ T.X₃.ρ) := by
  -- Transport the FDRep short exact sequence down to the underlying `K[G]`-modules.
  let ρ₁ : Representation K G T.X₁ := T.X₁.ρ
  let ρ₂ : Representation K G T.X₂ := T.X₂.ρ
  let ρ₃ : Representation K G T.X₃ := T.X₃.ρ
  letI : Module (MonoidAlgebra K G) T.X₁ := by
    simpa using (inferInstance : Module (MonoidAlgebra K G) ρ₁.asModule)
  letI : Module (MonoidAlgebra K G) T.X₂ := by
    simpa using (inferInstance : Module (MonoidAlgebra K G) ρ₂.asModule)
  letI : Module (MonoidAlgebra K G) T.X₃ := by
    simpa using (inferInstance : Module (MonoidAlgebra K G) ρ₃.asModule)
  letI : IsScalarTower K (MonoidAlgebra K G) T.X₁ := by
    simpa using (inferInstance : IsScalarTower K (MonoidAlgebra K G) ρ₁.asModule)
  letI : IsScalarTower K (MonoidAlgebra K G) T.X₂ := by
    simpa using (inferInstance : IsScalarTower K (MonoidAlgebra K G) ρ₂.asModule)
  letI : IsScalarTower K (MonoidAlgebra K G) T.X₃ := by
    simpa using (inferInstance : IsScalarTower K (MonoidAlgebra K G) ρ₃.asModule)
  let F : FDRep K G ⥤ ModuleCat (MonoidAlgebra K G) :=
    forget₂ (FDRep K G) (Rep K G) ⋙ Rep.toModuleMonoidAlgebra
  let U : ShortComplex (ModuleCat (MonoidAlgebra K G)) := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  let f : T.X₁ →ₗ[MonoidAlgebra K G] T.X₂ := by simpa [U, F] using U.f.hom
  let g : T.X₂ →ₗ[MonoidAlgebra K G] T.X₃ := by simpa [U, F] using U.g.hom
  have hf : Function.Injective f := by simpa [f] using hU.moduleCat_injective_f
  have hg : Function.Surjective g := by simpa [g] using hU.moduleCat_surjective_g
  have hfg : Function.Exact f g := by
    simpa [f, g] using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  -- The source module owner is projective and finite-dimensional over `K`.
  haveI : Module.Projective (MonoidAlgebra K G) (Representation.asModule S.ρ) :=
    fdRepK_asModule_projective_commonOwner S
  letI : Module K (Representation.asModule S.ρ) := representation_asModuleModule S.ρ
  letI : IsScalarTower K (MonoidAlgebra K G) (Representation.asModule S.ρ) :=
    representation_asModule_isScalarTower S.ρ
  haveI : FiniteDimensional K (Representation.asModule S.ρ) := by
    have : Module.Finite K S := inferInstance
    delta Representation.asModule
    infer_instance
  haveI : FiniteDimensional K T.X₁ := inferInstanceAs (FiniteDimensional K T.X₁.V)
  haveI : FiniteDimensional K T.X₂ := inferInstanceAs (FiniteDimensional K T.X₂.V)
  haveI : FiniteDimensional K T.X₃ := inferInstanceAs (FiniteDimensional K T.X₃.V)
  -- Apply the same linear-algebra core (`Hom(P, -)` exact for `P` projective) used on the `k` side.
  have hcore :
      Module.finrank K (Representation.asModule S.ρ →ₗ[MonoidAlgebra K G] T.X₂) =
        Module.finrank K (Representation.asModule S.ρ →ₗ[MonoidAlgebra K G] T.X₁) +
          Module.finrank K (Representation.asModule S.ρ →ₗ[MonoidAlgebra K G] T.X₃) :=
    projectiveHom_finrank_add_of_exact_generic_commonOwner
      (𝕜 := K) (R := MonoidAlgebra K G) (P := Representation.asModule S.ρ)
      (N := T.X₁) (M := T.X₂) (Q := T.X₃) hf hg hfg
  -- Translate each module-Hom dimension back to an intertwining-space dimension.
  have hbridge : ∀ σ : FDRep K G,
      Module.finrank K (Representation.IntertwiningMap S.ρ σ.ρ) =
        Module.finrank K
          (Representation.asModule S.ρ →ₗ[MonoidAlgebra K G] Representation.asModule σ.ρ) :=
    fun σ ↦ (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := S.ρ) (σ := σ.ρ)).finrank_eq
  rw [hbridge T.X₂, hbridge T.X₁, hbridge T.X₃]
  exact hcore

/-- Helper for Brauer reciprocity "Link 1": the additive functional on the free abelian group of
finite-dimensional `K`-representations sending `[σ]` to `dim_K Hom(S, σ)`. -/
private noncomputable abbrev simpleKHomFinrankLift_commonOwner
    (S : FDRep K G) :
    FreeAbelianGroup (FDRep K G) →+ ℤ :=
  FreeAbelianGroup.lift fun σ ↦
    (Module.finrank K (Representation.IntertwiningMap S.ρ σ.ρ) : ℤ)

omit [HenselianLocalRing A] in
/-- Helper for Brauer reciprocity "Link 1": the `Hom(S, -)` dimension lift vanishes on the defining
Grothendieck relations, because `Hom(S, -)` is exact (over semisimple `K[G]`). -/
private theorem finiteRepGrothendieckRelations_le_simpleKHomFinrankLift_ker_commonOwner
    [NeZero (Nat.card G : K)]
    (S : FDRep K G) :
    finiteRepGrothendieckRelations K G ≤
      (simpleKHomFinrankLift_commonOwner S).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨T, hT⟩, rfl⟩
  have hadd :
      Module.finrank K (Representation.IntertwiningMap S.ρ T.X₂.ρ) =
        Module.finrank K (Representation.IntertwiningMap S.ρ T.X₁.ρ) +
          Module.finrank K (Representation.IntertwiningMap S.ρ T.X₃.ρ) :=
    simpleHomK_intertwining_finrank_add_of_shortExact_commonOwner S T hT
  change simpleKHomFinrankLift_commonOwner S
    (FreeAbelianGroup.of T.X₂ - FreeAbelianGroup.of T.X₁ - FreeAbelianGroup.of T.X₃) = 0
  simp only [simpleKHomFinrankLift_commonOwner, map_sub, FreeAbelianGroup.lift_apply_of]
  rw [hadd]
  push_cast
  ring

/-- Helper for Brauer reciprocity "Link 1": the descended additive functional `R₀[K](G) →+ ℤ`,
`[σ] ↦ dim_K Hom(S, σ)`. -/
private noncomputable def simpleKHomFinrankHom_commonOwner
    [NeZero (Nat.card G : K)]
    (S : FDRep K G) :
    finiteRepGrothendieckGroup K G →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (simpleKHomFinrankLift_commonOwner S)
    (finiteRepGrothendieckRelations_le_simpleKHomFinrankLift_ker_commonOwner S)

omit [HenselianLocalRing A] in
/-- Helper for Brauer reciprocity "Link 1": the descended `Hom(S, -)` dimension functional evaluates
on an honest class `[M]` as `dim_K Hom(S, M)`. -/
private theorem simpleKHomFinrankHom_apply_class_commonOwner
    [NeZero (Nat.card G : K)]
    (S M : FDRep K G) :
    simpleKHomFinrankHom_commonOwner S [M]₀ =
      (Module.finrank K (Representation.IntertwiningMap S.ρ M.ρ) : ℤ) := by
  simp [simpleKHomFinrankHom_commonOwner, finiteRepGrothendieckClass,
    simpleKHomFinrankLift_commonOwner]

omit [HenselianLocalRing A] in
set_option backward.isDefEq.respectTransparency false in
/-- Brauer reciprocity "Link 1" (the `K`-side multiplicity-via-`Hom` formula): for a complete
pairwise-nonisomorphic family `πK` of *absolutely irreducible* simple `K`-representations (i.e. `K`
a splitting field, `End_{K[G]}(πK j) = K`) over a field `K` with `Nat.card G` invertible
(`K[G]` semisimple by Maschke), the `j`-th coordinate of `[V]` in the simple-class `ℤ`-basis of
`R₀[K](G)` is the `K`-dimension of the intertwining space `Hom_{K[G]}(V, πK j)`.

Both sides are additive functionals on Serre's Grothendieck group `R₀[K](G)`: the right side because
`πK j` is projective over the semisimple `K[G]`, so `Hom(πK j, -)` is exact and its dimension is
additive (then `dim Hom(V, πK j) = dim Hom(πK j, V)` by projective Hom-symmetry); the left side is a
basis coordinate.  They agree on the simple generators by the Kronecker-delta computation, hence
everywhere. -/
theorem simpleK_basis_coord_eq_hom_finrank_commonOwner
    {κ : Type v} [Fintype κ] [DecidableEq κ] [NeZero (Nat.card G : K)]
    (πK : κ → FDRep K G) (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (hπK_absIrr : ∀ i, Module.finrank K (Representation.IntertwiningMap (πK i).ρ (πK i).ρ) = 1)
    (V : FDRep K G) (j : κ) :
    (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr [V]₀ j =
      Module.finrank K (Representation.IntertwiningMap V.ρ (πK j).ρ) := by
  classical
  let b := simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  -- Two additive functionals on `R₀[K](G)`: the `Hom(πK j, -)` dimension and the `j`-coordinate.
  let Φ : finiteRepGrothendieckGroup K G →+ ℤ := simpleKHomFinrankHom_commonOwner (πK j)
  let coord : finiteRepGrothendieckGroup K G →+ ℤ :=
    { toFun := fun y ↦ b.repr y j
      map_zero' := by simp
      map_add' := by intro y z; simp }
  -- They agree on every basis generator `[πK i]`, where both compute the Kronecker delta `δ_{ji}`.
  have hbasis : ∀ i, Φ (b i) = coord (b i) := by
    intro i
    have hΦ : Φ (b i) = (if j = i then 1 else 0 : ℤ) := by
      have h1 : Φ (b i) =
          (Module.finrank K (Representation.IntertwiningMap (πK j).ρ (πK i).ρ) : ℤ) := by
        rw [simple_finiteRep_classes_basis_of_complete_family_apply]
        exact simpleKHomFinrankHom_apply_class_commonOwner (πK j) (πK i)
      have h2 :
          Module.finrank K (Representation.IntertwiningMap (πK j).ρ (πK i).ρ) =
            (if j = i then 1 else 0) :=
        simpleKIntertwining_finrank_eq_delta_commonOwner
          πK hπK_pairwise hπK_complete hπK_absIrr j i
      rw [h1, h2]; split <;> simp
    have hcoord : coord (b i) = (if j = i then 1 else 0 : ℤ) := by
      have hb : b.repr (b i) = Finsupp.single i (1 : ℤ) := by simpa using b.repr_self i
      show b.repr (b i) j = _
      rw [hb]
      simp [Finsupp.single_apply, eq_comm]
    rw [hΦ, hcoord]
  -- Two `ℤ`-linear functionals that agree on a basis are equal.
  have hΦeq : Φ.toIntLinearMap = coord.toIntLinearMap := by
    apply b.ext; intro i; exact hbasis i
  have hΦV : Φ [V]₀ = coord [V]₀ := by
    have hx := congrArg (fun fn : finiteRepGrothendieckGroup K G →ₗ[ℤ] ℤ ↦ fn [V]₀) hΦeq
    simpa using hx
  -- `Φ [V] = dim Hom(πK j, V) = dim Hom(V, πK j)` (projective Hom-symmetry).
  have hΦV_val : Φ [V]₀ = (Module.finrank K (Representation.IntertwiningMap (πK j).ρ V.ρ) : ℤ) :=
    simpleKHomFinrankHom_apply_class_commonOwner (πK j) V
  have hswap :
      Module.finrank K (Representation.IntertwiningMap (πK j).ρ V.ρ) =
        Module.finrank K (Representation.IntertwiningMap V.ρ (πK j).ρ) := by
    -- `Hom(πK j, V)` and `Hom(V, πK j)` have equal `K`-dimension because `πK j` is projective.
    letI : Module K (Representation.asModule (πK j).ρ) := representation_asModuleModule (πK j).ρ
    letI : IsScalarTower K (MonoidAlgebra K G) (Representation.asModule (πK j).ρ) :=
      representation_asModule_isScalarTower (πK j).ρ
    letI : Module K (Representation.asModule V.ρ) := representation_asModuleModule V.ρ
    letI : IsScalarTower K (MonoidAlgebra K G) (Representation.asModule V.ρ) :=
      representation_asModule_isScalarTower V.ρ
    haveI : FiniteDimensional K (Representation.asModule (πK j).ρ) := by
      have : Module.Finite K (πK j) := inferInstance
      delta Representation.asModule; infer_instance
    haveI : FiniteDimensional K (Representation.asModule V.ρ) := by
      have : Module.Finite K V := inferInstance
      delta Representation.asModule; infer_instance
    haveI : Module.Projective (MonoidAlgebra K G) (Representation.asModule (πK j).ρ) :=
      fdRepK_asModule_projective_commonOwner (πK j)
    have hjV :
        Module.finrank K (Representation.IntertwiningMap (πK j).ρ V.ρ) =
          Module.finrank K (Representation.asModule (πK j).ρ →ₗ[MonoidAlgebra K G]
            Representation.asModule V.ρ) :=
      (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := (πK j).ρ) (σ := V.ρ)).finrank_eq
    have hVj :
        Module.finrank K (Representation.IntertwiningMap V.ρ (πK j).ρ) =
          Module.finrank K (Representation.asModule V.ρ →ₗ[MonoidAlgebra K G]
            Representation.asModule (πK j).ρ) :=
      (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := V.ρ) (σ := (πK j).ρ)).finrank_eq
    rw [hjV, hVj]
    exact finrank_hom_eq_finrank_hom_swap_of_projective
      (E := Representation.asModule (πK j).ρ) (F := Representation.asModule V.ρ)
  -- Assemble.
  have hgoal :
      (b.repr [V]₀ j : ℤ) =
        (Module.finrank K (Representation.IntertwiningMap V.ρ (πK j).ρ) : ℤ) := by
    have : coord [V]₀ = (Module.finrank K (Representation.IntertwiningMap V.ρ (πK j).ρ) : ℤ) := by
      rw [← hΦV, hΦV_val, hswap]
    simpa [coord] using this
  exact hgoal

end

end Representation
