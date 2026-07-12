import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

-- Declarations for this item will be appended below by the statement pipeline.

open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v w w₁ w₂ w₃

noncomputable section

variable {Λ : Type u} [CommRing Λ]

variable {κ : Type w₁} [CommRing κ] [Algebra Λ κ]
variable {G : Type v} [Group G]
variable {P : Type w} [AddCommGroup P] [Module Λ P] [Module Λ[G] P]
variable [IsScalarTower Λ Λ[G] P]

/-
Domain-style sampling:
* Primary domain: base change of `Λ[G]`-modules along `Λ → κ`, specialized below to residue-field
  reduction over a local ring.
* Core/canonical owners: `IsBaseChange` for the tensor-product realization of scalar extension,
  `Representation.IsIntertwiningMap` / `Representation.IntertwiningMap` for equivariant maps,
  the endomorphism owner `ρ.IntertwiningMap ρ`, and `IsBaseChange.endHom` for base-changed
  endomorphisms.
* Source-facing layer: Lemma `14-14.4-2`, which compares projectivity and isomorphism classes
  before and after residue-field reduction.
* Primitive data: a reduction map is first a base-change map and separately an owner-level
  intertwining map; the induced map on equivariant endomorphisms is derived from those owners.
-/

/-- Scalar extension of a `Λ[G]`-module carries the induced `κ[G]`-module structure. -/
noncomputable instance : Module κ[G] (κ ⊗[Λ] P) :=
  let ρ : Representation κ G (κ ⊗[Λ] P) :=
    Representation.scalarExtension (show Representation Λ G P from Representation.ofModule' P)
  Module.compHom _ ρ.asAlgebraHom.toRingHom

noncomputable instance : IsScalarTower κ κ[G] (κ ⊗[Λ] P) :=
  let ρ : Representation κ G (κ ⊗[Λ] P) :=
    Representation.scalarExtension (show Representation Λ G P from Representation.ofModule' P)
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change ρ.asAlgebraHom (algebraMap κ κ[G] a) x = a • x
    simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x

section

variable [IsLocalRing Λ]

namespace LinearMap

variable {P : Type w} [AddCommGroup P] [Module Λ P]
variable {Pbar : Type w₁} [AddCommGroup Pbar]
variable [Module (IsLocalRing.ResidueField Λ) Pbar] [Module Λ Pbar]
variable [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Pbar]

/-- A `Λ`-linear map `P → Pbar` exhibits `Pbar` as a `G`-equivariant realization of the canonical
residue-field base change of the `Λ[G]`-module `P`. -/
def IsResidueFieldReduction (G : Type v) [Group G]
    [Module Λ[G] P] [IsScalarTower Λ Λ[G] P]
    [Module (IsLocalRing.ResidueField Λ)[G] Pbar]
    [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Pbar]
    (f : P →ₗ[Λ] Pbar) : Prop :=
  letI : Module Λ[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      -- The restricted `Λ[G]`-action on `Pbar` was defined by composing along
      -- `Λ[G] → (IsLocalRing.ResidueField Λ)[G]`, so scalar-tower compatibility is definitional.
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ a) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ a) • x
            = (IsLocalRing.residue Λ a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) a x)
  let ρ : Representation Λ G P := Representation.ofModule' P
  let ρbar : Representation Λ G Pbar := Representation.ofModule' Pbar
  IsBaseChange (IsLocalRing.ResidueField Λ) f ∧ ρ.IsIntertwiningMap ρbar f

namespace IsResidueFieldReduction

theorem map_monoidAlgebra_of {G : Type v} [Group G]
    [Module Λ[G] P] [IsScalarTower Λ Λ[G] P]
    [Module (IsLocalRing.ResidueField Λ)[G] Pbar]
    [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Pbar]
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G) (g : G) (x : P) :
    f (MonoidAlgebra.of Λ G g • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G g • f x := by
  letI : Module Λ[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun a y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) a) • y =
          a • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ a) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ a) • y
            = (IsLocalRing.residue Λ a) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ a) y)
        _ = a • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) a y)
  -- Compare the source action with the reduced action through the local `Λ[G]`-module structure on
  -- `Pbar` used in `IsResidueFieldReduction`.
  have hΛ : f (MonoidAlgebra.of Λ G g • x) = MonoidAlgebra.of Λ G g • f x := by
    simpa [Representation.ofModule'] using hf.2.isIntertwining g x
  calc
    f (MonoidAlgebra.of Λ G g • x) = MonoidAlgebra.of Λ G g • f x := hΛ
    _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G g • f x := by
          change
            (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
                (MonoidAlgebra.of Λ G g) • f x =
              MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G g • f x
          simp

end IsResidueFieldReduction

end LinearMap

open LinearMap

namespace MonoidAlgebra

variable {G : Type v} [Group G]
variable {P : Type w} [AddCommGroup P] [Module Λ P] [Module Λ[G] P]
variable [IsScalarTower Λ Λ[G] P]

/-- Helper for Lemma 14-14.4-2: the canonical pure-tensor reduction commutes with the action of
`MonoidAlgebra.of` on a `Λ[G]`-module. -/
lemma tensorProduct_mk_map_monoidAlgebra_of (g : G) (x : P) :
    TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1 (MonoidAlgebra.of Λ G g • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G g •
        TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1 x := by
  -- Rewrite the reduced `kΛ[G]`-action through the scalar-extended representation and then
  -- evaluate it on the pure tensor `1 ⊗ x`.
  let ρ : Representation Λ G P := Representation.ofModule' P
  let ρk :
      Representation (IsLocalRing.ResidueField Λ) G
        ((IsLocalRing.ResidueField Λ) ⊗[Λ] P) :=
    Representation.scalarExtension ρ
  have hsingle :=
    Representation.single_smul
      (ρ := ρk) (t := (1 : IsLocalRing.ResidueField Λ)) (g := g)
      (v := TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1 x)
  simpa [ρ, ρk, Representation.scalarExtension, Representation.ofModule',
    MonoidAlgebra.of_apply] using hsingle.symm

/-- The canonical tensor-product reduction realizes the intrinsic residue-field reduction of a
`Λ[G]`-module. -/
theorem tensorProduct_mk_isResidueFieldReduction :
    IsResidueFieldReduction G (TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1) := by
  -- The tensor-product map is the canonical base change, and the induced group action is defined
  -- precisely so that this map is equivariant.
  constructor
  · simpa using
      (TensorProduct.isBaseChange (R := Λ) (S := IsLocalRing.ResidueField Λ) (M := P))
  · -- Check equivariance on the generators `MonoidAlgebra.of Λ G g`.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    change TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1 (MonoidAlgebra.of Λ G g • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ))
        (MonoidAlgebra.of Λ G g)) •
        TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1 x
    simpa using
      MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of (Λ := Λ) (G := G) (P := P) g x

end MonoidAlgebra

variable {G : Type v} [Group G] [Finite G]
attribute [local instance] Fintype.ofFinite

variable {P : Type w} [AddCommGroup P] [Module Λ P] [Module Λ[G] P]
variable [IsScalarTower Λ Λ[G] P] [Module.Finite Λ P]

-- Proof sketch: for the forward implication, tensor a projective resolution with the residue field
-- and use that projectivity descends to direct summands over base change. For the reverse
-- implication, combine Lemma `14-14.4-1` with the lifted averaging endomorphism over the residue
-- field and Nakayama's lemma to recover an averaging endomorphism over `Λ`.
variable {Pbar : Type w₁} [AddCommGroup Pbar]
variable [Module (IsLocalRing.ResidueField Λ) Pbar] [Module Λ Pbar]
variable [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Pbar]
variable [Module (IsLocalRing.ResidueField Λ)[G] Pbar]
variable [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Pbar]

namespace LinearMap.IsResidueFieldReduction

local notation "kΛ" => IsLocalRing.ResidueField Λ
local notation "ρΛ" => (Representation.ofModule' P : Representation Λ G P)
local notation "ρkΛ" => (Representation.ofModule' Pbar : Representation kΛ G Pbar)
local notation "EndΛ" => Representation.IntertwiningMap ρΛ ρΛ
local notation "EndkΛ" => Representation.IntertwiningMap ρkΛ ρkΛ

noncomputable local instance : Algebra Λ EndkΛ :=
  Algebra.compHom EndkΛ (algebraMap Λ kΛ)

noncomputable local instance : IsScalarTower Λ kΛ EndkΛ :=
  IsScalarTower.of_algebraMap_smul fun a u ↦ by
    ext x
    rfl

private noncomputable def endIntertwiningMap
    {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndΛ) :
    EndkΛ :=
  (hf.1.endHom u.toLinearMap).intertwiningMap_of_isIntertwiningMap ρkΛ ρkΛ
    fun g v ↦ by
      let uBar : Pbar →ₗ[kΛ] Pbar := hf.1.endHom u.toLinearMap
      have hcomm : uBar.comp (ρkΛ g) = (ρkΛ g).comp uBar := by
        apply hf.1.algHom_ext'
        apply LinearMap.ext
        intro x
        change uBar (ρkΛ g (f x)) = ρkΛ g (uBar (f x))
        rw [show ρkΛ g (f x) = f (ρΛ g x) by
              simpa [Representation.ofModule'] using (hf.map_monoidAlgebra_of g x).symm]
        rw [show uBar (f (ρΛ g x)) = f (u (ρΛ g x)) by
              simpa [uBar] using hf.1.endHom_comp_apply u.toLinearMap (ρΛ g x)]
        rw [show uBar (f x) = f (u x) by
              simpa [uBar] using hf.1.endHom_comp_apply u.toLinearMap x]
        rw [show u (ρΛ g x) = ρΛ g (u x) by
              simpa using LinearMap.congr_fun (u.isIntertwining' g) x]
        simpa [Representation.ofModule'] using hf.map_monoidAlgebra_of g (u x)
      exact LinearMap.congr_fun hcomm v

private noncomputable def endLinearMap
    {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    EndΛ →ₗ[Λ] EndkΛ := by
  exact
    { toFun := endIntertwiningMap hf
      map_add' := by
        intro u v
        apply Representation.IntertwiningMap.ext
        apply hf.1.algHom_ext'
        apply LinearMap.ext
        intro x
        simp [endIntertwiningMap, hf.1.endHom_comp_apply]
      map_smul' := by
        intro a u
        apply Representation.IntertwiningMap.ext
        apply hf.1.algHom_ext'
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply]
        change endIntertwiningMap hf (a • u) (f x) =
          ((algebraMap Λ kΛ a) • endIntertwiningMap hf u) (f x)
        rw [Representation.IntertwiningMap.smul_apply]
        rw [show endIntertwiningMap hf u (f x) = f (u x) by
              change hf.1.endHom u.toLinearMap (f x) = f (u x)
              simpa using hf.1.endHom_comp_apply u.toLinearMap x]
        rw [show endIntertwiningMap hf (a • u) (f x) = f ((a • u) x) by
              change hf.1.endHom (a • u.toLinearMap) (f x) = f ((a • u) x)
              simpa using hf.1.endHom_comp_apply (a • u.toLinearMap) x]
        rw [Representation.IntertwiningMap.smul_apply, f.map_smul]
        exact (IsScalarTower.algebraMap_smul kΛ a (f (u x))).symm }

/-- The canonical reduction algebra homomorphism on equivariant endomorphisms induced by a
residue-field reduction. -/
noncomputable def endAlgHom
    {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    EndΛ →ₐ[Λ] EndkΛ := by
  -- Package the already constructed linear map once we know it preserves `1` and composition on
  -- the reduction image.
  refine AlgHom.ofLinearMap (endLinearMap hf) ?_ ?_
  · apply Representation.IntertwiningMap.ext
    -- Compare the identity endomorphisms after precomposing with the reduction map.
    apply hf.1.algHom_ext'
    ext x
    change hf.1.endHom (1 : Module.End Λ P) (f x) = (1 : EndkΛ) (f x)
    simpa using hf.1.endHom_comp_apply (1 : Module.End Λ P) x
  · intro u v
    apply Representation.IntertwiningMap.ext
    -- Compare compositions after precomposing with the reduction map.
    apply hf.1.algHom_ext'
    ext x
    have hv :
        endIntertwiningMap hf v (f x) = f (v.toLinearMap x) := by
      change hf.1.endHom v.toLinearMap (f x) = f (v.toLinearMap x)
      simpa using hf.1.endHom_comp_apply v.toLinearMap x
    have hu :
        endIntertwiningMap hf u (f (v.toLinearMap x)) = f (u.toLinearMap (v.toLinearMap x)) := by
      change hf.1.endHom u.toLinearMap (f (v.toLinearMap x)) = f (u.toLinearMap (v.toLinearMap x))
      simpa using hf.1.endHom_comp_apply u.toLinearMap (v.toLinearMap x)
    calc
      hf.1.endHom (u * v : Module.End Λ P) (f x) = f ((u * v) x) := by
        simpa using hf.1.endHom_comp_apply (u * v : Module.End Λ P) x
      _ = f (u.toLinearMap (v.toLinearMap x)) := rfl
      _ = endIntertwiningMap hf u (f (v.toLinearMap x)) := hu.symm
      _ = endIntertwiningMap hf u (endIntertwiningMap hf v (f x)) := by rw [hv]
      _ = (endLinearMap hf u * endLinearMap hf v) (f x) := rfl

/-- Helper for Lemma 14-14.4-2: residue-field reduction carries the Maschke averaging operator on
endomorphisms to the averaged reduced endomorphism. -/
lemma endHom_conjugate_on_image
    {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : Module.End Λ P) (g : G) (x : P) :
    hf.1.endHom (u.conjugate g) (f x) = (hf.1.endHom u).conjugate g (f x) := by
  -- Rewrite both conjugates pointwise and transport the action through the reduction map.
  calc
    hf.1.endHom (u.conjugate g) (f x) = f (u.conjugate g x) := by
      simpa using hf.1.endHom_comp_apply (u.conjugate g) x
    _ = f (MonoidAlgebra.single g⁻¹ (1 : Λ) • u (MonoidAlgebra.single g (1 : Λ) • x)) := by
          rfl
    _ = MonoidAlgebra.single g⁻¹ (1 : IsLocalRing.ResidueField Λ) •
          f (u (MonoidAlgebra.single g (1 : Λ) • x)) := by
            simpa [MonoidAlgebra.of_apply] using
              hf.map_monoidAlgebra_of g⁻¹ (u (MonoidAlgebra.single g (1 : Λ) • x))
    _ = MonoidAlgebra.single g⁻¹ (1 : IsLocalRing.ResidueField Λ) •
          (hf.1.endHom u (f (MonoidAlgebra.single g (1 : Λ) • x))) := by
            rw [show hf.1.endHom u (f (MonoidAlgebra.single g (1 : Λ) • x)) =
                f (u (MonoidAlgebra.single g (1 : Λ) • x)) by
                  simpa using hf.1.endHom_comp_apply u (MonoidAlgebra.single g (1 : Λ) • x)]
    _ = MonoidAlgebra.single g⁻¹ (1 : IsLocalRing.ResidueField Λ) •
          (hf.1.endHom u)
            (MonoidAlgebra.single g (1 : IsLocalRing.ResidueField Λ) • f x) := by
            rw [show f (MonoidAlgebra.single g (1 : Λ) • x) =
                MonoidAlgebra.single g (1 : IsLocalRing.ResidueField Λ) • f x by
                  simpa [MonoidAlgebra.of_apply] using hf.map_monoidAlgebra_of g x]
    _ = (hf.1.endHom u).conjugate g (f x) := by
          rfl

/-- Helper for Lemma 14-14.4-2: residue-field reduction carries the Maschke averaging operator on
endomorphisms to the averaged reduced endomorphism. -/
lemma endHom_sumOfConjugates
    {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : Module.End Λ P) :
    hf.1.endHom (u.sumOfConjugates G) = (hf.1.endHom u).sumOfConjugates G := by
  -- Compare both endomorphisms on the reduction image, where the base-change map is canonical.
  apply hf.1.algHom_ext'
  ext x
  calc
    hf.1.endHom (u.sumOfConjugates G) (f x) = f (u.sumOfConjugates G x) := by
      simpa using hf.1.endHom_comp_apply (u.sumOfConjugates G) x
    _ = ∑ g : G, hf.1.endHom (u.conjugate g) (f x) := by
          rw [LinearMap.sumOfConjugates_apply]
          simp [hf.1.endHom_comp_apply]
    _ = ∑ g : G, (hf.1.endHom u).conjugate g (f x) := by
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          exact endHom_conjugate_on_image hf u g x
    _ = (hf.1.endHom u).sumOfConjugates G (f x) := by
          rw [LinearMap.sumOfConjugates_apply]

/-- Helper for Lemma 14-14.4-2: if a finite free endomorphism becomes the identity after
residue-field reduction, then it is already invertible over the local ring. -/
lemma endomorphism_isUnit_of_endHom_eq_id
    [Module.Free Λ P] {f : P →ₗ[Λ] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : Module.End Λ P)
    (hu : hf.1.endHom u = LinearMap.id) :
    IsUnit u := by
  -- Route correction: the source proof uses a Nakayama-style argument; in Lean the stable route is
  -- to compare determinants through `IsBaseChange.det_endHom`.
  have hdet :
      algebraMap Λ (IsLocalRing.ResidueField Λ) (LinearMap.det u) = 1 := by
    have hdet_red : LinearMap.det (hf.1.endHom u) = 1 := by
      simpa using congrArg LinearMap.det hu
    calc
      algebraMap Λ (IsLocalRing.ResidueField Λ) (LinearMap.det u)
          = LinearMap.det (hf.1.endHom u) := by
              symm
              exact IsBaseChange.det_endHom
                (S := IsLocalRing.ResidueField Λ) (M := P) (P := Pbar) hf.1 u
      _ = 1 := hdet_red
  have hdet_unit : IsUnit (LinearMap.det u) := by
    -- Over a local ring, a scalar whose residue is nonzero is a unit.
    have hresidue_ne_zero : IsLocalRing.residue Λ (LinearMap.det u) ≠ 0 := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq, hdet]
      simp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (LinearMap.det u)).mp hresidue_ne_zero
  exact (LinearMap.isUnit_iff_isUnit_det u).mpr hdet_unit

end LinearMap.IsResidueFieldReduction

/-- Any `G`-equivariant realization of the canonical residue-field reduction has the same
projectivity behavior as the intrinsic tensor-product reduction. -/
theorem projective_monoidAlgebra_iff_projective_of_isResidueFieldReduction [Module.Free Λ P]
    (f : P →ₗ[Λ] Pbar) (hf : f.IsResidueFieldReduction G) :
    Module.Projective Λ[G] P ↔
      Module.Projective (IsLocalRing.ResidueField Λ)[G] Pbar := by
  constructor
  · intro hP
    -- Move Serre's averaging criterion through residue-field reduction.
    rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := Λ) (G := G) (P := P)).mp hP with ⟨_, u, hu⟩
    let _ : Module.Free (IsLocalRing.ResidueField Λ) Pbar := hf.1.free
    refine
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := IsLocalRing.ResidueField Λ) (G := G) (P := Pbar)).mpr ?_
    refine ⟨inferInstance, hf.1.endHom u, ?_⟩
    -- The reduced averaging endomorphism still averages to the identity.
    calc
      (hf.1.endHom u).sumOfConjugates G = hf.1.endHom (u.sumOfConjugates G) := by
        symm
        exact hf.endHom_sumOfConjugates u
      _ = hf.1.endHom (LinearMap.id : Module.End Λ P) := by rw [hu]
      _ = LinearMap.id := hf.1.endHom_one
  · intro hPbar
    -- Lift the reduced averaging endomorphism and normalize by the inverse of its equivariant
    -- average, exactly as in Serre's argument.
    rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := IsLocalRing.ResidueField Λ) (G := G) (P := Pbar)).mp hPbar with ⟨_, ubar, hubar⟩
    have hsurj : Function.Surjective hf.1.endHom := by
      let hend : IsBaseChange (IsLocalRing.ResidueField Λ) hf.1.endHom :=
        IsBaseChange.end (S := IsLocalRing.ResidueField Λ) hf.1
      have hres :
          Function.Surjective (algebraMap Λ (IsLocalRing.ResidueField Λ)) := by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
      intro ubar
      obtain ⟨t, rfl⟩ := hend.equiv.surjective ubar
      obtain ⟨u, hu⟩ := TensorProduct.mk_surjective (R := Λ) (S := IsLocalRing.ResidueField Λ)
        (M := Module.End Λ P) hres t
      refine ⟨u, ?_⟩
      calc
        hf.1.endHom u = (1 : IsLocalRing.ResidueField Λ) • hf.1.endHom u := by simp
        _ = hend.equiv ((TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) (Module.End Λ P) 1) u) := by
              symm
              simpa [hend] using hend.equiv_tmul (1 : IsLocalRing.ResidueField Λ) u
        _ = hend.equiv t := by rw [hu]
    obtain ⟨u0, hu0⟩ := hsurj ubar
    let uavg : Module.End Λ P := u0.sumOfConjugates G
    have huavg_red : hf.1.endHom uavg = LinearMap.id := by
      -- The averaged lift reduces to the averaged reduced endomorphism.
      calc
        hf.1.endHom uavg = (hf.1.endHom u0).sumOfConjugates G := by
          simpa [uavg] using hf.endHom_sumOfConjugates u0
        _ = ubar.sumOfConjugates G := by rw [hu0]
        _ = LinearMap.id := hubar
    have huavg_unit : IsUnit uavg :=
      hf.endomorphism_isUnit_of_endHom_eq_id uavg huavg_red
    have hbij : Function.Bijective (u0.sumOfConjugatesEquivariant G : P →ₗ[Λ[G]] P) := by
      simpa [uavg] using ((Module.End.isUnit_iff uavg).mp huavg_unit)
    let eavg : P ≃ₗ[Λ[G]] P := LinearEquiv.ofBijective (u0.sumOfConjugatesEquivariant G) hbij
    let u : Module.End Λ P := ((eavg.symm : P →ₗ[Λ[G]] P).restrictScalars Λ).comp u0
    have hu : u.sumOfConjugates G = LinearMap.id := by
      -- Route correction: use the equivariance of `eavg.symm` to pull the average through a
      -- composition, rather than averaging twice.
      calc
        u.sumOfConjugates G
            = ((eavg.symm : P →ₗ[Λ[G]] P).restrictScalars Λ).comp
                (u0.sumOfConjugates G) := by
                  simpa [u] using
                    (equivariant_comp_sumOfConjugates (Λ := Λ) (G := G)
                      (P := P) (Q := P) (f := eavg.symm) (π := u0))
        _ = LinearMap.id := by
              ext x
              change eavg.symm (eavg x) = x
              simp
    exact
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := Λ) (G := G) (P := P)).mpr ⟨inferInstance, u, hu⟩

/-- Lemma 14-14.4-2 (1): for a finite group `G` and a finite free `Λ`-module `P`, `P` is
projective over `Λ[G]` exactly when its canonical residue-field reduction
`IsLocalRing.ResidueField Λ ⊗[Λ] P` is projective over
`(IsLocalRing.ResidueField Λ)[G]`. -/
theorem projective_monoidAlgebra_iff_projective_residueFieldReduction [Module.Free Λ P] :
    Module.Projective Λ[G] P ↔
      Module.Projective (IsLocalRing.ResidueField Λ)[G]
        ((IsLocalRing.ResidueField Λ) ⊗[Λ] P) := by
  -- Specialize the residue-field comparison theorem to the canonical tensor-product reduction.
  simpa using
    (projective_monoidAlgebra_iff_projective_of_isResidueFieldReduction
      (P := P)
      (Pbar := (IsLocalRing.ResidueField Λ) ⊗[Λ] P)
      (f := TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1)
      (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := Λ) (G := G) (P := P)))

variable {P' : Type w₂} [AddCommGroup P'] [Module Λ P'] [Module Λ[G] P']
variable [IsScalarTower Λ Λ[G] P'] [Module.Finite Λ P']

-- Proof sketch: a `Λ[G]`-linear equivalence reduces to a `k_Λ[G]`-linear equivalence by base
-- change. Conversely, lift a `k_Λ[G]`-linear isomorphism between the reductions to a
-- `Λ[G]`-linear map using projectivity, then apply Nakayama's lemma to show that the lift is an
-- isomorphism.
variable {Pbar' : Type w₃} [AddCommGroup Pbar']
variable [Module (IsLocalRing.ResidueField Λ) Pbar'] [Module Λ Pbar']
variable [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Pbar']
variable [Module (IsLocalRing.ResidueField Λ)[G] Pbar']
variable [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Pbar']

/-- Helper for Lemma 14-14.4-2: for a module viewed through `Representation.ofModule'`, the
induced group-algebra action is the original scalar multiplication. -/
private theorem ofModule'_asAlgebraHom_apply
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M]
    (r : A[G]) (m : M) :
    ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials.
  refine MonoidAlgebra.induction_on
    (p := fun s : A[G] =>
      ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Lemma 14-14.4-2: the owner module of `Representation.ofModule' M` is canonically
the original `A[G]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    Nonempty ((Representation.ofModule' (k := A) (G := G) M).asModule ≃ₗ[A[G]] M) := by
  -- Use `asModuleEquiv` and then show it respects the original group-algebra action.
  let toFun : (Representation.ofModule' (k := A) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := A) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : A[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the original
    -- `A[G]`-action on `M`.
    calc
      (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := A) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply (G := G) A M r
                ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x))
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Lemma 14-14.4-2: `equivLinearMapAsModule` does not change the underlying function
for `Representation.ofModule'`. -/
private theorem Representation.IntertwiningMap.equivLinearMapAsModule_ofModule'_apply
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module A[G] N] [IsScalarTower A A[G] N]
    (u : Representation.IntertwiningMap (Representation.ofModule' (k := A) (G := G) M)
      (Representation.ofModule' (k := A) (G := G) N))
    (x : (Representation.ofModule' (k := A) (G := G) M).asModule) :
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule' (k := A) (G := G) M)
      (σ := Representation.ofModule' (k := A) (G := G) N) u) x = u x := by
  rfl

/-- Helper for Lemma 14-14.4-2: the inverse direction of `equivLinearMapAsModule` is also
definitionally the same underlying function for `Representation.ofModule'`. -/
private theorem Representation.IntertwiningMap.symm_equivLinearMapAsModule_ofModule'_apply
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module A[G] N] [IsScalarTower A A[G] N]
    (ℓ : (Representation.ofModule' (k := A) (G := G) M).asModule →ₗ[A[G]]
      (Representation.ofModule' (k := A) (G := G) N).asModule)
    (x : M) :
    ((Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule' (k := A) (G := G) M)
      (σ := Representation.ofModule' (k := A) (G := G) N)).symm ℓ)
        ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x) =
      ℓ ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x) := by
  rfl

/-- Helper for Lemma 14-14.4-2: lifting an equivariant `Λ`-linear map across a residue-field
reduction preserves the `MonoidAlgebra.of` action on the reduction. -/
private theorem LinearMap.IsResidueFieldReduction.lift_map_monoidAlgebra_of
    {Q : Type*} [AddCommGroup Q] [Module (IsLocalRing.ResidueField Λ) Q] [Module Λ Q]
    [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Q]
    [Module (IsLocalRing.ResidueField Λ)[G] Q]
    [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Q]
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[Λ] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of Λ G s • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g x)
    (s : G) (x : Pbar) :
    hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g x := by
  -- Induct on the scalar-extension presentation of `x`; on generators `f y` the claim is exactly
  -- the compatibility of `g` with `MonoidAlgebra.of`.
  induction x using hf.1.inductionOn with
  | zero =>
      simp
  | tmul y =>
      calc
        hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • f y)
            = hf.1.lift g (f (MonoidAlgebra.of Λ G s • y)) := by
                rw [hf.map_monoidAlgebra_of s y]
        _ = g (MonoidAlgebra.of Λ G s • y) := by
              simpa using hf.1.lift_eq g (MonoidAlgebra.of Λ G s • y)
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g y := hg s y
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g (f y) := by
              rw [hf.1.lift_eq g y]
  | smul a x hx =>
      calc
        hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • a • x)
            = hf.1.lift g (a • (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • x)) := by
                rw [smul_comm a (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s) x]
        _ = a • hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • x) := by
              rw [map_smul]
        _ = a • (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g x) := by
              rw [hx]
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • a • hf.1.lift g x := by
              rw [smul_comm a (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s) (hf.1.lift g x)]
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g (a • x) := by
              rw [map_smul]
  | add x y hx hy =>
      calc
        hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • (x + y))
            = hf.1.lift g
                (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • x +
                  MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • y) := by
                    rw [smul_add]
        _ = hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • x) +
              hf.1.lift g (MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • y) := by
                rw [map_add]
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g x +
              MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g y := by
                rw [hx, hy]
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s •
              (hf.1.lift g x + hf.1.lift g y) := by
                rw [smul_add]
        _ = MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • hf.1.lift g (x + y) := by
              rw [map_add]

/-- Helper for Lemma 14-14.4-2: any realization of the canonical residue-field reduction is
surjective on the underlying modules. -/
private theorem LinearMap.IsResidueFieldReduction.surjective
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G) :
    Function.Surjective f := by
  intro x
  -- Write `x` as the image of a pure tensor and then evaluate the base-change equivalence.
  obtain ⟨t, rfl⟩ := hf.1.equiv.surjective x
  have hres :
      Function.Surjective (algebraMap Λ (IsLocalRing.ResidueField Λ)) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective
    (R := Λ) (S := IsLocalRing.ResidueField Λ) (M := P) hres t
  refine ⟨y, ?_⟩
  calc
    f y = (1 : IsLocalRing.ResidueField Λ) • f y := by simp
    _ = hf.1.equiv ((TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1) y) := by
          symm
          simpa using hf.1.equiv_tmul (1 : IsLocalRing.ResidueField Λ) y
        _ = hf.1.equiv t := by rw [hy]

/-- Helper for Lemma 14-14.4-2: a finite projective `Λ[G]`-module over a local ring is free over
the base ring `Λ`. -/
private theorem free_of_projective_groupAlgebra_over_local
    (hP : Module.Projective Λ[G] P) : Module.Free Λ P := by
  -- Restrict scalars to `Λ`, use that projective modules are flat, and then apply the local-ring
  -- finite flat implies free criterion.
  let _ : Module.Projective Λ P :=
    projective_restrictScalars_of_projective_groupAlgebra
      (Λ := Λ) (G := G) (P := P) hP
  let _ : Module.Flat Λ P := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Lemma 14-14.4-2: after restricting the reduced `k_Λ[G]`-action along
`Λ[G] → k_Λ[G]`, the reduction map is `Λ[G]`-linear. -/
private theorem LinearMap.IsResidueFieldReduction.map_smul
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G)
    (a : Λ[G]) (x : P) :
    letI : Module Λ[G] Pbar :=
      Module.compHom Pbar
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    letI : IsScalarTower Λ Λ[G] Pbar :=
      IsScalarTower.of_algebraMap_smul fun c y ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
              (MonoidAlgebra.single (1 : G) c) • y =
            c • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
              algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
                (IsLocalRing.residue Λ c) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
              = (IsLocalRing.residue Λ c) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                      (IsLocalRing.residue Λ c) y)
          _ = c • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
    f (a • x) = a • f x := by
  letI : Module Λ[G] Pbar :=
    Module.compHom Pbar
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
            = (IsLocalRing.residue Λ c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
  -- Check linearity first on the group-like elements and then extend linearly in the group algebra.
  refine MonoidAlgebra.induction_on (p := fun b : Λ[G] => f (b • x) = b • f x) a ?_ ?_ ?_
  · intro g
    change
      f (MonoidAlgebra.of Λ G g • x) =
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.of Λ G g) •
          f x
    simpa [MonoidAlgebra.of_apply] using hf.map_monoidAlgebra_of g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    simpa [smul_smul] using congrArg (fun y => c • y) ha

/-- Helper for Lemma 14-14.4-2: the reduction map can be packaged as a `Λ[G]`-linear map after
restricting the reduced action along `Λ[G] → k_Λ[G]`. -/
private noncomputable def LinearMap.IsResidueFieldReduction.to_groupAlgebraLinearMap
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G) :
    letI : Module Λ[G] Pbar :=
      Module.compHom Pbar
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    letI : IsScalarTower Λ Λ[G] Pbar :=
      IsScalarTower.of_algebraMap_smul fun c y ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
              (MonoidAlgebra.single (1 : G) c) • y =
            c • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
              algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
                (IsLocalRing.residue Λ c) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
              = (IsLocalRing.residue Λ c) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                      (IsLocalRing.residue Λ c) y)
          _ = c • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
    P →ₗ[Λ[G]] Pbar :=
  letI : Module Λ[G] Pbar :=
    Module.compHom Pbar
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
            = (IsLocalRing.residue Λ c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
  { toFun := f
    map_add' := f.map_add
    map_smul' := hf.map_smul }

/-- Helper for Lemma 14-14.4-2: a lifted map is `k_Λ[G]`-linear once its defining source map is
equivariant on the generators `MonoidAlgebra.of`. -/
private theorem LinearMap.IsResidueFieldReduction.lift_map_smul
    {Q : Type*} [AddCommGroup Q] [Module (IsLocalRing.ResidueField Λ) Q] [Module Λ Q]
    [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Q]
    [Module (IsLocalRing.ResidueField Λ)[G] Q]
    [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Q]
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[Λ] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of Λ G s • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g x)
    (a : (IsLocalRing.ResidueField Λ)[G]) (x : Pbar) :
    hf.1.lift g (a • x) = a • hf.1.lift g x := by
  -- Extend the generator-equivariant identity linearly in the group algebra.
  refine MonoidAlgebra.induction_on
    (p := fun b : (IsLocalRing.ResidueField Λ)[G] =>
      hf.1.lift g (b • x) = b • hf.1.lift g x) a ?_ ?_ ?_
  · intro s
    simpa [MonoidAlgebra.of_apply] using hf.lift_map_monoidAlgebra_of hg s x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    simpa [smul_smul] using congrArg (fun y => c • y) ha

/-- Helper for Lemma 14-14.4-2: a lifted equivariant map can be packaged as a
`k_Λ[G]`-linear map. -/
private noncomputable def LinearMap.IsResidueFieldReduction.lift_groupAlgebraLinearMap
    {Q : Type*} [AddCommGroup Q] [Module (IsLocalRing.ResidueField Λ) Q] [Module Λ Q]
    [IsScalarTower Λ (IsLocalRing.ResidueField Λ) Q]
    [Module (IsLocalRing.ResidueField Λ)[G] Q]
    [IsScalarTower (IsLocalRing.ResidueField Λ) (IsLocalRing.ResidueField Λ)[G] Q]
    {f : P →ₗ[Λ] Pbar} (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[Λ] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of Λ G s • x) =
      MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g x) :
    Pbar →ₗ[(IsLocalRing.ResidueField Λ)[G]] Q :=
  { toFun := hf.1.lift g
    map_add' := (hf.1.lift g).map_add
    map_smul' := hf.lift_map_smul hg }

/-- Helper for Lemma 14-14.4-2: a `k_Λ[G]`-linear map is automatically `Λ[G]`-linear on modules
obtained by restricting scalars along `Λ[G] → k_Λ[G]`. -/
private theorem LinearMap.map_smul_of_restricted_groupAlgebra
    {Q : Type*} [AddCommGroup Q] [Module (IsLocalRing.ResidueField Λ) Q]
    [Module (IsLocalRing.ResidueField Λ)[G] Q]
    {Q' : Type*} [AddCommGroup Q'] [Module (IsLocalRing.ResidueField Λ) Q']
    [Module (IsLocalRing.ResidueField Λ)[G] Q']
    (g : Q →ₗ[(IsLocalRing.ResidueField Λ)[G]] Q')
    (a : Λ[G]) (x : Q) :
    letI : Module Λ[G] Q :=
      Module.compHom Q
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    letI : Module Λ[G] Q' :=
      Module.compHom Q'
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    g (a • x) = a • g x := by
  letI : Module Λ[G] Q :=
    Module.compHom Q
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : Module Λ[G] Q' :=
    Module.compHom Q'
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  -- The restricted `Λ[G]`-action is definitionally the `k_Λ[G]`-action through the coefficient
  -- map, so ordinary `k_Λ[G]`-linearity already gives the required identity.
  change
    g
        ((MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ))) a • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ))) a • g x
  simpa using
    g.map_smul
      ((MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ))) a) x

/-- Helper for Lemma 14-14.4-2: a `k_Λ[G]`-linear map can be viewed as a `Λ[G]`-linear map after
restricting scalars along `Λ[G] → k_Λ[G]`. -/
private noncomputable def LinearMap.restrict_groupAlgebraLinearMap
    {Q : Type*} [AddCommGroup Q] [Module (IsLocalRing.ResidueField Λ) Q]
    [Module (IsLocalRing.ResidueField Λ)[G] Q]
    {Q' : Type*} [AddCommGroup Q'] [Module (IsLocalRing.ResidueField Λ) Q']
    [Module (IsLocalRing.ResidueField Λ)[G] Q']
    (g : Q →ₗ[(IsLocalRing.ResidueField Λ)[G]] Q') :
    letI : Module Λ[G] Q :=
      Module.compHom Q
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    letI : Module Λ[G] Q' :=
      Module.compHom Q'
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
    Q →ₗ[Λ[G]] Q' :=
  letI : Module Λ[G] Q :=
    Module.compHom Q
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : Module Λ[G] Q' :=
    Module.compHom Q'
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  { toFun := g
    map_add' := g.map_add
    map_smul' := LinearMap.map_smul_of_restricted_groupAlgebra g }

/-- Any two `G`-equivariant realizations of the canonical residue-field reductions are isomorphic
exactly when the original projective `Λ[G]`-modules are isomorphic. -/
theorem projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
    (f : P →ₗ[Λ] Pbar) (hf : f.IsResidueFieldReduction G)
    (f' : P' →ₗ[Λ] Pbar') (hf' : f'.IsResidueFieldReduction G)
    (hP : Module.Projective Λ[G] P)
    (hP' : Module.Projective Λ[G] P') :
    Nonempty (P ≃ₗ[Λ[G]] P') ↔
      Nonempty (Pbar ≃ₗ[(IsLocalRing.ResidueField Λ)[G]] Pbar') := by
  letI : Module Λ[G] Pbar :=
    Module.compHom Pbar
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
            = (IsLocalRing.residue Λ c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
  letI : Module Λ[G] Pbar' :=
    Module.compHom Pbar'
      (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
  letI : IsScalarTower Λ Λ[G] Pbar' :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap Λ (IsLocalRing.ResidueField Λ)))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) =
            algebraMap (IsLocalRing.ResidueField Λ) ((IsLocalRing.ResidueField Λ)[G])
              (IsLocalRing.residue Λ c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue Λ c) • y
            = (IsLocalRing.residue Λ c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul ((IsLocalRing.ResidueField Λ)[G])
                    (IsLocalRing.residue Λ c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField Λ) c y)
  letI : Module.Free Λ P :=
    free_of_projective_groupAlgebra_over_local (Λ := Λ) (G := G) (P := P) hP
  letI : Module.Free Λ P' :=
    free_of_projective_groupAlgebra_over_local (Λ := Λ) (G := G) (P := P') hP'
  constructor
  · intro hPP'
    rcases hPP' with ⟨e⟩
    let g : P →ₗ[Λ] Pbar' := f'.comp (e.toLinearMap.restrictScalars Λ)
    have hg : ∀ s x, g (MonoidAlgebra.of Λ G s • x) =
        MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g x := by
      intro s x
      -- Reduce an actual `Λ[G]`-equivalence by composing with the target reduction map.
      change f' (e (MonoidAlgebra.of Λ G s • x)) =
        MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • f' (e x)
      rw [e.map_smul]
      simpa [MonoidAlgebra.of_apply] using hf'.map_monoidAlgebra_of s (e x)
    let g' : P' →ₗ[Λ] Pbar := f.comp (e.symm.toLinearMap.restrictScalars Λ)
    have hg' : ∀ s x, g' (MonoidAlgebra.of Λ G s • x) =
        MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • g' x := by
      intro s x
      -- The inverse equivalence reduces in the same way.
      change f (e.symm (MonoidAlgebra.of Λ G s • x)) =
        MonoidAlgebra.of (IsLocalRing.ResidueField Λ) G s • f (e.symm x)
      rw [e.symm.map_smul]
      simpa [MonoidAlgebra.of_apply] using hf.map_monoidAlgebra_of s (e.symm x)
    let ebarMap :
        Pbar →ₗ[(IsLocalRing.ResidueField Λ)[G]] Pbar' :=
      hf.lift_groupAlgebraLinearMap hg
    let ebarInv :
        Pbar' →ₗ[(IsLocalRing.ResidueField Λ)[G]] Pbar :=
      hf'.lift_groupAlgebraLinearMap hg'
    have hleft :
        ebarInv.comp ebarMap = LinearMap.id := by
      -- Compare the two reduced endomorphisms on the image of the reduction map `f`, first as
      -- `k_Λ`-linear maps and then forget back to `k_Λ[G]`-linearity.
      apply LinearMap.ext
      intro y
      have hleft' :
          (ebarInv.comp ebarMap).restrictScalars (IsLocalRing.ResidueField Λ) =
            (LinearMap.id :
              Pbar →ₗ[(IsLocalRing.ResidueField Λ)[G]] Pbar).restrictScalars
                (IsLocalRing.ResidueField Λ) := by
        apply hf.1.algHom_ext'
        ext x
        change ebarInv (ebarMap (f x)) = f x
        rw [show ebarMap (f x) = g x by
              change hf.1.lift g (f x) = g x
              simpa using hf.1.lift_eq g x]
        change ebarInv (f' (e x)) = f x
        rw [show ebarInv (f' (e x)) = g' (e x) by
              change hf'.1.lift g' (f' (e x)) = g' (e x)
              simpa using hf'.1.lift_eq g' (e x)]
        simp [g']
      exact LinearMap.congr_fun hleft' y
    have hright :
        ebarMap.comp ebarInv = LinearMap.id := by
      -- Symmetrically compare on the image of the target reduction map `f'`.
      apply LinearMap.ext
      intro y
      have hright' :
          (ebarMap.comp ebarInv).restrictScalars (IsLocalRing.ResidueField Λ) =
            (LinearMap.id :
              Pbar' →ₗ[(IsLocalRing.ResidueField Λ)[G]] Pbar').restrictScalars
                (IsLocalRing.ResidueField Λ) := by
        apply hf'.1.algHom_ext'
        ext x
        change ebarMap (ebarInv (f' x)) = f' x
        rw [show ebarInv (f' x) = g' x by
              change hf'.1.lift g' (f' x) = g' x
              simpa using hf'.1.lift_eq g' x]
        change ebarMap (f (e.symm x)) = f' x
        rw [show ebarMap (f (e.symm x)) = g (e.symm x) by
              change hf.1.lift g (f (e.symm x)) = g (e.symm x)
              simpa using hf.1.lift_eq g (e.symm x)]
        simp [g]
      exact LinearMap.congr_fun hright' y
    have hleftFun : Function.LeftInverse ebarInv ebarMap := by
      intro x
      exact LinearMap.congr_fun hleft x
    have hrightFun : Function.RightInverse ebarInv ebarMap := by
      intro x
      exact LinearMap.congr_fun hright x
    exact
      ⟨LinearEquiv.ofBijective ebarMap
        ⟨hleftFun.injective, hrightFun.surjective⟩⟩
  · intro hPbarEq
    rcases hPbarEq with ⟨ebar⟩
    let fGA : P →ₗ[Λ[G]] Pbar := hf.to_groupAlgebraLinearMap
    let f'GA : P' →ₗ[Λ[G]] Pbar' := hf'.to_groupAlgebraLinearMap
    let ebarGA : Pbar →ₗ[Λ[G]] Pbar' :=
      LinearMap.restrict_groupAlgebraLinearMap (Λ := Λ) (G := G) ebar.toLinearMap
    let ebarInvGA : Pbar' →ₗ[Λ[G]] Pbar :=
      LinearMap.restrict_groupAlgebraLinearMap (Λ := Λ) (G := G) ebar.symm.toLinearMap
    obtain ⟨w, hw⟩ :=
      Module.projective_lifting_property f'GA (ebarGA.comp fGA) hf'.surjective
    obtain ⟨w', hw'⟩ :=
      Module.projective_lifting_property fGA (ebarInvGA.comp f'GA) hf.surjective
    let u : Module.End Λ P :=
      (w'.restrictScalars Λ).comp (w.restrictScalars Λ)
    have hu_red : hf.1.endHom u = LinearMap.id := by
      -- The composite lift reduces to `ebar.symm ∘ ebar = 1`.
      apply hf.1.algHom_ext'
      ext x
      have hwx : f' (w x) = ebar (f x) := by
        have hwx' := LinearMap.congr_fun hw x
        simpa [fGA, f'GA, ebarGA] using hwx'
      calc
        (hf.1.endHom u) (f x) = f (w' (w x)) := by
          simpa [u] using hf.1.endHom_comp_apply u x
        _ = ebar.symm (f' (w x)) := by
          have hw'x := LinearMap.congr_fun hw' (w x)
          simpa [fGA, f'GA, ebarInvGA] using hw'x
        _ = ebar.symm (ebar (f x)) := by rw [hwx]
        _ = f x := by simp
        _ = (LinearMap.id : Pbar →ₗ[IsLocalRing.ResidueField Λ] Pbar) (f x) := rfl
    let u' : Module.End Λ P' :=
      (w.restrictScalars Λ).comp (w'.restrictScalars Λ)
    have hu'_red : hf'.1.endHom u' = LinearMap.id := by
      -- The symmetric lifted composite reduces to `ebar ∘ ebar.symm = 1`.
      apply hf'.1.algHom_ext'
      ext x
      have hw'x : f (w' x) = ebar.symm (f' x) := by
        have hw'x' := LinearMap.congr_fun hw' x
        simpa [fGA, f'GA, ebarInvGA] using hw'x'
      calc
        (hf'.1.endHom u') (f' x) = f' (w (w' x)) := by
          simpa [u'] using hf'.1.endHom_comp_apply u' x
        _ = ebar (f (w' x)) := by
          have hwx := LinearMap.congr_fun hw (w' x)
          simpa [fGA, f'GA, ebarGA] using hwx
        _ = ebar (ebar.symm (f' x)) := by rw [hw'x]
        _ = f' x := by simp
        _ = (LinearMap.id : Pbar' →ₗ[IsLocalRing.ResidueField Λ] Pbar') (f' x) := rfl
    have hu_unit : IsUnit u :=
      hf.endomorphism_isUnit_of_endHom_eq_id u hu_red
    have hu'_unit : IsUnit u' :=
      hf'.endomorphism_isUnit_of_endHom_eq_id u' hu'_red
    have hu_bij : Function.Bijective u :=
      (Module.End.isUnit_iff u).mp hu_unit
    have hu'_bij : Function.Bijective u' :=
      (Module.End.isUnit_iff u').mp hu'_unit
    have hw_injective : Function.Injective w := by
      intro x y hxy
      apply hu_bij.1
      simpa [u, hxy]
    have hw_surjective : Function.Surjective w := by
      intro y
      rcases hu'_bij.2 y with ⟨z, hz⟩
      refine ⟨w' z, ?_⟩
      simpa [u'] using hz
    exact ⟨LinearEquiv.ofBijective w ⟨hw_injective, hw_surjective⟩⟩

/-- Lemma 14-14.4-2 (2): for a finite group `G`, two finite projective `Λ[G]`-modules are
isomorphic if and only if their canonical residue-field reductions are isomorphic as
`(IsLocalRing.ResidueField Λ)[G]`-modules. -/
theorem projective_monoidAlgebra_nonempty_linearEquiv_iff_reduction_nonempty_linearEquiv
    (hP : Module.Projective Λ[G] P)
    (hP' : Module.Projective Λ[G] P') :
    Nonempty (P ≃ₗ[Λ[G]] P') ↔
      Nonempty
        (((IsLocalRing.ResidueField Λ) ⊗[Λ] P) ≃ₗ[(IsLocalRing.ResidueField Λ)[G]]
          ((IsLocalRing.ResidueField Λ) ⊗[Λ] P')) := by
  -- Specialize the general comparison theorem to the canonical tensor-product reductions.
  simpa using
    (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
      (P := P)
      (Pbar := (IsLocalRing.ResidueField Λ) ⊗[Λ] P)
      (f := TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P 1)
      (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := Λ) (G := G) (P := P))
      (P' := P')
      (Pbar' := (IsLocalRing.ResidueField Λ) ⊗[Λ] P')
      (f' := TensorProduct.mk Λ (IsLocalRing.ResidueField Λ) P' 1)
      (hf' := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := Λ) (G := G) (P := P'))
      hP hP')

end
end
