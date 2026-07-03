import Serre.Chap14.Exercise_14_14_4_6.EquivariantEndomorphismFreeness

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u w x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]
variable {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
variable [Module.Projective A[G] P] [Module.Finite A P]
variable {Pbar : Type x} [AddCommGroup Pbar] [Module (IsLocalRing.ResidueField A) Pbar]
variable [Module A Pbar] [IsScalarTower A (IsLocalRing.ResidueField A) Pbar]
variable [Module (IsLocalRing.ResidueField A)[G] Pbar]
variable [IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)[G] Pbar]

local notation "kA" => IsLocalRing.ResidueField A
local notation "EndAG" => (P →ₗ[A[G]] P)
local notation "ρA" => (Representation.ofModule' P : Representation A G P)
local notation "ρkA" => (Representation.ofModule' Pbar : Representation kA G Pbar)
local notation "EndA" => Representation.IntertwiningMap ρA ρA
local notation "EndkA" => Representation.IntertwiningMap ρkA ρkA
local notation "EndkAG" => (Pbar →ₗ[kA[G]] Pbar)

noncomputable local instance : Algebra A EndkA :=
  Algebra.compHom EndkA (algebraMap A kA)

noncomputable local instance : IsScalarTower A kA EndkA :=
  IsScalarTower.of_algebraMap_smul fun a u ↦ by
    ext x
    rfl

noncomputable local instance : Module A EndkAG :=
  Module.compHom EndkAG (algebraMap A kA)

noncomputable local instance : Algebra A EndkAG :=
  Algebra.compHom EndkAG (algebraMap A kA)

noncomputable local instance : IsScalarTower A kA EndkAG :=
  IsScalarTower.of_algebraMap_smul fun a u ↦ by
    ext x
    rfl

namespace LinearMap.IsResidueFieldReduction

omit [Module.Projective A[G] P] [Module.Finite A P] in
/-- Helper for Exercise 14-14.4-6: the reduced equivariant endomorphism has the same underlying
`kA`-linear map as the ordinary endomorphism obtained from `IsBaseChange.endHom`. -/
theorem endAlgHom_toLinearMap_eq_endHom
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndA) :
    (hf.endAlgHom u).toLinearMap = hf.1.endHom u.toLinearMap := by
  apply hf.1.algHom_ext'
  ext x
  rfl

omit [Module.Projective A[G] P] [Module.Finite A P] in
/-- Helper for Exercise 14-14.4-6: on the reduction image, `hf.endAlgHom` acts by applying the
original equivariant endomorphism before reducing. -/
theorem endAlgHom_comp_apply
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndA) (x : P) :
    hf.endAlgHom u (f x) = f (u x) := by
  change (hf.endAlgHom u).toLinearMap (f x) = f (u x)
  rw [endAlgHom_toLinearMap_eq_endHom hf u]
  simpa using hf.1.endHom_comp_apply u.toLinearMap x

/-- Helper for Exercise 14-14.4-6: after restricting scalars along
`A[G] → kA[G]`, a residue-field reduction map is `A[G]`-linear. -/
theorem map_smul_restricted_groupAlgebra
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (a : A[G]) (x : P) :
    letI : Module A[G] Pbar :=
      Module.compHom Pbar
        (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    letI : IsScalarTower A A[G] Pbar :=
      IsScalarTower.of_algebraMap_smul fun c y ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A kA))
              (MonoidAlgebra.single (1 : G) c) • y =
            c • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
              algebraMap kA (kA[G]) (IsLocalRing.residue A c) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
              = (IsLocalRing.residue A c) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul (kA[G])
                      (IsLocalRing.residue A c) y)
          _ = c • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul kA c y)
    f (a • x) = a • f x := by
  letI : Module A[G] Pbar :=
    Module.compHom Pbar
      (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  letI : IsScalarTower A A[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A kA))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap kA (kA[G]) (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (kA[G])
                    (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul kA c y)
  refine MonoidAlgebra.induction_on (p := fun b : A[G] => f (b • x) = b • f x) a ?_ ?_ ?_
  · intro g
    change
      f (MonoidAlgebra.of A G g • x) =
        (MonoidAlgebra.mapRingHom G (algebraMap A kA))
            (MonoidAlgebra.of A G g) •
          f x
    simpa [MonoidAlgebra.of_apply] using hf.map_monoidAlgebra_of g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    simpa [smul_smul] using congrArg (fun y => c • y) ha

/-- Helper for Exercise 14-14.4-6: any realization of the canonical residue-field reduction is
surjective on the underlying modules. -/
theorem surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    Function.Surjective f := by
  intro x
  obtain ⟨t, rfl⟩ := hf.1.equiv.surjective x
  have hres :
      Function.Surjective (algebraMap A kA) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective
    (R := A) (S := kA) (M := P) hres t
  refine ⟨y, ?_⟩
  calc
    f y = (1 : kA) • f y := by simp
    _ = hf.1.equiv ((TensorProduct.mk A kA P 1) y) := by
          symm
          simpa using hf.1.equiv_tmul (1 : kA) y
    _ = hf.1.equiv t := by rw [hy]

/-- Helper for Exercise 14-14.4-6: restricting scalars along `A[G] → kA[G]` turns a
`kA[G]`-linear map into an `A[G]`-linear map. -/
theorem map_smul_of_restricted_groupAlgebra
    {Q : Type*} [AddCommGroup Q] [Module kA Q] [Module kA[G] Q]
    {Q' : Type*} [AddCommGroup Q'] [Module kA Q'] [Module kA[G] Q']
    (g : Q →ₗ[kA[G]] Q')
    (a : A[G]) (x : Q) :
    letI : Module A[G] Q :=
      Module.compHom Q (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    letI : Module A[G] Q' :=
      Module.compHom Q' (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    g (a • x) = a • g x := by
  letI : Module A[G] Q :=
    Module.compHom Q (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  letI : Module A[G] Q' :=
    Module.compHom Q' (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  change
    g ((MonoidAlgebra.mapRingHom G (algebraMap A kA)) a • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap A kA)) a • g x
  simpa using g.map_smul ((MonoidAlgebra.mapRingHom G (algebraMap A kA)) a) x

/-- Helper for Exercise 14-14.4-6: package the restricted-scalar view of a `kA[G]`-linear map as
an actual `A[G]`-linear map. -/
noncomputable def restrict_groupAlgebraLinearMap
    {Q : Type*} [AddCommGroup Q] [Module kA Q] [Module kA[G] Q]
    {Q' : Type*} [AddCommGroup Q'] [Module kA Q'] [Module kA[G] Q']
    (g : Q →ₗ[kA[G]] Q') :
    letI : Module A[G] Q :=
      Module.compHom Q (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    letI : Module A[G] Q' :=
      Module.compHom Q' (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    Q →ₗ[A[G]] Q' :=
  letI : Module A[G] Q :=
    Module.compHom Q (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  letI : Module A[G] Q' :=
    Module.compHom Q' (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  { toFun := g
    map_add' := g.map_add
    map_smul' := map_smul_of_restricted_groupAlgebra (A := A) (G := G) g }

/-- Helper for Exercise 14-14.4-6: after restricting scalars along `A[G] → kA[G]`, an
equivariant endomorphism of `Pbar` is `A[G]`-linear. -/
theorem intertwiningMap_map_smul_restricted_groupAlgebra
    (u : EndkA)
    (a : A[G]) (x : Pbar) :
    letI : Module A[G] Pbar :=
      Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    u (a • x) = a • u x := by
  letI : Module A[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  letI : IsScalarTower A A[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A kA))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap kA (kA[G]) (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (kA[G])
                    (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul kA c y)
  refine MonoidAlgebra.induction_on (p := fun b : A[G] => u (b • x) = b • u x) a ?_ ?_ ?_
  · intro g
    change
      u ((MonoidAlgebra.mapRingHom G (algebraMap A kA)) (MonoidAlgebra.of A G g) • x) =
        (MonoidAlgebra.mapRingHom G (algebraMap A kA)) (MonoidAlgebra.of A G g) • u x
    simpa [Representation.ofModule'] using LinearMap.congr_fun (u.isIntertwining' g) x
  · intro b c hb hc
    simp [add_smul, hb, hc]
  · intro c b hb
    calc
      u ((c • b) • x) = u (c • (b • x)) := by rw [smul_assoc]
      _ = c • u (b • x) := by
            rw [← IsScalarTower.algebraMap_smul kA c (b • x)]
            rw [← IsScalarTower.algebraMap_smul kA c (u (b • x))]
            simpa using u.toLinearMap.map_smul (algebraMap A kA c) (b • x)
      _ = c • (b • u x) := by rw [hb]
      _ = (c • b) • u x := by rw [smul_assoc]

/-- Helper for Exercise 14-14.4-6: an equivariant endomorphism of `Pbar` becomes an actual
`A[G]`-linear endomorphism after restricting scalars. -/
noncomputable def intertwiningMap_restrict_groupAlgebraLinearMap
    (u : EndkA) :
    letI : Module A[G] Pbar :=
      Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    Pbar →ₗ[A[G]] Pbar :=
  letI : Module A[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  { toFun := u
    map_add' := u.map_add
    map_smul' := intertwiningMap_map_smul_restricted_groupAlgebra (A := A) (G := G) u }

/-- Helper for Exercise 14-14.4-6: an `A[G]`-linear endomorphism of `P` commutes with the
`Representation.ofModule'` action. -/
theorem groupAlgebraLinearMap_isIntertwining
    (u : P →ₗ[A[G]] P)
    (g : G) (x : P) :
    ((u.restrictScalars A) : P →ₗ[A] P) (((Representation.ofModule' P : Representation A G P) g) x) =
      ((Representation.ofModule' P : Representation A G P) g)
        (((u.restrictScalars A) : P →ₗ[A] P) x) := by
  simpa [Representation.ofModule', MonoidAlgebra.of_apply] using
    u.map_smul (MonoidAlgebra.of A G g) x

/-- Helper for Exercise 14-14.4-6: an `A[G]`-linear endomorphism of `P` gives an equivariant
endomorphism of `Representation.ofModule' P`. -/
noncomputable def groupAlgebraLinearMap_toIntertwiningEnd
    (u : P →ₗ[A[G]] P) :
    EndA :=
  ((u.restrictScalars A) : P →ₗ[A] P).intertwiningMap_of_isIntertwiningMap
    (Representation.ofModule' P : Representation A G P)
    (Representation.ofModule' P : Representation A G P)
    (groupAlgebraLinearMap_isIntertwining (A := A) (G := G) u)

/-- Helper for Exercise 14-14.4-6: if `g : P → Q` is equivariant on group generators, then the
lift of `g` along a residue-field reduction is equivariant on those generators as well. -/
theorem lift_map_monoidAlgebra_of
    {Q : Type*} [AddCommGroup Q] [Module kA Q] [Module A Q]
    [IsScalarTower A kA Q] [Module kA[G] Q]
    [IsScalarTower kA kA[G] Q]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[A] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of A G s • x) =
      MonoidAlgebra.of kA G s • g x)
    (s : G) (y : Pbar) :
    hf.1.lift g (MonoidAlgebra.of kA G s • y) =
      MonoidAlgebra.of kA G s • hf.1.lift g y := by
  obtain ⟨x, rfl⟩ := hf.surjective y
  calc
    hf.1.lift g (MonoidAlgebra.of kA G s • f x)
        = hf.1.lift g (f (MonoidAlgebra.of A G s • x)) := by
            rw [hf.map_monoidAlgebra_of]
    _ = g (MonoidAlgebra.of A G s • x) := by
          simpa using hf.1.lift_eq g (MonoidAlgebra.of A G s • x)
    _ = MonoidAlgebra.of kA G s • g x := hg s x
    _ = MonoidAlgebra.of kA G s • hf.1.lift g (f x) := by
          rw [hf.1.lift_eq g x]

/-- Helper for Exercise 14-14.4-6: a lifted map is `kA[G]`-linear once its source map is
equivariant on the generators `MonoidAlgebra.of`. -/
theorem lift_map_smul
    {Q : Type*} [AddCommGroup Q] [Module kA Q] [Module A Q]
    [IsScalarTower A kA Q] [Module kA[G] Q]
    [IsScalarTower kA kA[G] Q]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[A] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of A G s • x) =
      MonoidAlgebra.of kA G s • g x)
    (a : kA[G]) (y : Pbar) :
    hf.1.lift g (a • y) = a • hf.1.lift g y := by
  refine MonoidAlgebra.induction_on
    (p := fun b : kA[G] => hf.1.lift g (b • y) = b • hf.1.lift g y) a ?_ ?_ ?_
  · intro s
    simpa [MonoidAlgebra.of_apply] using lift_map_monoidAlgebra_of (A := A) (G := G) hf hg s y
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    simpa [smul_smul] using congrArg (fun z => c • z) ha

/-- Helper for Exercise 14-14.4-6: an `A`-linear map out of `P` whose source action is
group-equivariant lifts to a `kA[G]`-linear map out of `Pbar`. -/
noncomputable def lift_groupAlgebraLinearMap
    {Q : Type*} [AddCommGroup Q] [Module kA Q] [Module A Q]
    [IsScalarTower A kA Q] [Module kA[G] Q]
    [IsScalarTower kA kA[G] Q]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {g : P →ₗ[A] Q}
    (hg : ∀ s x, g (MonoidAlgebra.of A G s • x) =
      MonoidAlgebra.of kA G s • g x) :
    Pbar →ₗ[kA[G]] Q :=
  { toFun := hf.1.lift g
    map_add' := (hf.1.lift g).map_add
    map_smul' := lift_map_smul (A := A) (G := G) hf hg }

/-- Helper for Exercise 14-14.4-6: composing an `A[G]`-linear endomorphism with the reduction map
is still equivariant on the monoid generators. -/
theorem reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndAG) (s : G) (x : P) :
    (f.comp (u.restrictScalars A)) (MonoidAlgebra.of A G s • x) =
      MonoidAlgebra.of kA G s • (f.comp (u.restrictScalars A)) x := by
  change f (u (MonoidAlgebra.of A G s • x)) =
      MonoidAlgebra.of kA G s • f (u x)
  rw [u.map_smul]
  simpa [MonoidAlgebra.of_apply] using hf.map_monoidAlgebra_of s (u x)

/-- Helper for Exercise 14-14.4-6: the ordinary base-change lift on `f ∘ u` produces a
`kA[G]`-linear endomorphism of `Pbar`. -/
theorem endHom_restrict_groupAlgebraLinearMap_map_add
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u v : EndAG) :
    lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp ((u + v).restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf (u + v)) =
      lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp (u.restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf u) +
      lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp (v.restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf v) := by
  ext y
  obtain ⟨x, rfl⟩ := hf.surjective y
  change
    hf.1.lift (f.comp ((u + v).restrictScalars A)) (f x) =
      (hf.1.lift (f.comp (u.restrictScalars A)) +
        hf.1.lift (f.comp (v.restrictScalars A))) (f x)
  simp only [LinearMap.add_apply]
  calc
    hf.1.lift (f.comp ((u + v).restrictScalars A)) (f x) = f ((u + v) x) := by
      simpa [LinearMap.comp_apply] using
        hf.1.lift_eq (f.comp ((u + v).restrictScalars A)) x
    _ = f (u x) + f (v x) := by simp
    _ = (f.comp (u.restrictScalars A)) x + (f.comp (v.restrictScalars A)) x := by rfl
    _ = hf.1.lift (f.comp (u.restrictScalars A)) (f x) +
          hf.1.lift (f.comp (v.restrictScalars A)) (f x) := by
            rw [← hf.1.lift_eq (f.comp (u.restrictScalars A)) x,
              ← hf.1.lift_eq (f.comp (v.restrictScalars A)) x]

/-- Helper for Exercise 14-14.4-6: the transported lift on `f ∘ u` is `A`-linear in `u`. -/
theorem endHom_restrict_groupAlgebraLinearMap_map_smul
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (a : A) (u : EndAG) :
    lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp ((a • u).restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf (a • u)) =
      a •
        lift_groupAlgebraLinearMap (A := A) (G := G) hf
          (g := f.comp (u.restrictScalars A))
          (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
            (A := A) (G := G) hf u) := by
  ext y
  obtain ⟨x, rfl⟩ := hf.surjective y
  calc
    lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp ((a • u).restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf (a • u)) (f x)
        = hf.1.lift (f.comp ((a • u).restrictScalars A)) (f x) := by
            rfl
    _ = f ((a • u) x) := by
      simpa [LinearMap.comp_apply] using
        hf.1.lift_eq (f.comp ((a • u).restrictScalars A)) x
    _ = (algebraMap A kA a) • f (u x) := by
          calc
            f ((a • u) x) = a • f (u x) := by
              simp [LinearMap.smul_apply]
            _ = (algebraMap A kA a) • f (u x) := by
                  symm
                  simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                    (IsScalarTower.algebraMap_smul kA a (f (u x)))
    _ = (algebraMap A kA a) • hf.1.lift (f.comp (u.restrictScalars A)) (f x) := by
          rw [hf.1.lift_eq (f.comp (u.restrictScalars A)) x]
          simp [LinearMap.comp_apply]
    _ = (a •
        lift_groupAlgebraLinearMap (A := A) (G := G) hf
          (g := f.comp (u.restrictScalars A))
          (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
            (A := A) (G := G) hf u)) (f x) := by
              rfl

/-- Helper for Exercise 14-14.4-6: the ordinary endomorphism base change restricts to
`A[G]`-linear endomorphisms. -/
noncomputable def endHom_restrict_groupAlgebraLinearMap
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    EndAG →ₗ[A] EndkAG :=
  { toFun := fun u ↦
      lift_groupAlgebraLinearMap (A := A) (G := G) hf
        (g := f.comp (u.restrictScalars A))
        (reduction_comp_groupAlgebraLinearMap_map_monoidAlgebra_of
          (A := A) (G := G) hf u)
    map_add' := endHom_restrict_groupAlgebraLinearMap_map_add (A := A) (G := G) hf
    map_smul' := endHom_restrict_groupAlgebraLinearMap_map_smul (A := A) (G := G) hf }

/-- Helper for Exercise 14-14.4-6: the restricted ordinary base-change map agrees with
composition by `u` on the reduction image. -/
theorem endHom_restrict_groupAlgebraLinearMap_comp_apply
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndAG) (x : P) :
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u (f x) = f (u x) := by
  simpa [endHom_restrict_groupAlgebraLinearMap,
    lift_groupAlgebraLinearMap, LinearMap.comp_apply] using
    hf.1.lift_eq (f.comp (u.restrictScalars A)) x

/-- Helper for Exercise 14-14.4-6: after identifying equivariant endomorphisms with
group-algebra-linear endomorphisms on source and target, `hf.endAlgHom` agrees on the reduction
image with the expected transport square. -/
theorem endAlgHom_transport_comp_apply
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndA) :
    ∀ x : P,
      ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom u) (f x) =
        f ((ofModule'_equivAlgEnd (G := G) A P u) x) := by
  intro x
  calc
    ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom u) (f x) =
        hf.endAlgHom u (f x) := by
          rw [ofModule'_equivAlgEnd_apply_apply]
    _ = f (u x) := by exact endAlgHom_comp_apply hf u x
    _ = f ((ofModule'_equivAlgEnd (G := G) A P u) x) := by
          rw [ofModule'_equivAlgEnd_apply_apply]

/-- Helper for Exercise 14-14.4-6: after identifying equivariant endomorphisms with
`A[G]`-linear endomorphisms, `hf.endAlgHom` is the restricted ordinary base-change map. -/
theorem endHom_restrict_groupAlgebraLinearMap_eq_transport
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndAG) :
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u =
      ofModule'_equivAlgEnd (G := G) kA Pbar
        (hf.endAlgHom ((ofModule'_equivAlgEnd (G := G) A P).symm u)) := by
  ext y
  obtain ⟨x, rfl⟩ := hf.surjective y
  calc
    endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u (f x) = f (u x) := by
      exact endHom_restrict_groupAlgebraLinearMap_comp_apply (A := A) (G := G) hf u x
    _ =
        f (((ofModule'_equivAlgEnd (G := G) A P)
          ((ofModule'_equivAlgEnd (G := G) A P).symm u)) x) := by
            simp
    _ =
        ofModule'_equivAlgEnd (G := G) kA Pbar
          (hf.endAlgHom ((ofModule'_equivAlgEnd (G := G) A P).symm u)) (f x) := by
            symm
            exact endAlgHom_transport_comp_apply hf
              ((ofModule'_equivAlgEnd (G := G) A P).symm u) x

/-- Helper for Exercise 14-14.4-6: transporting `hf.endAlgHom` across the canonical
`Representation.ofModule'` identifications gives an actual `A`-algebra hom on
`A[G]`-linear endomorphisms. -/
noncomputable def endHom_restrict_groupAlgebraAlgHom
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    Module.End A[G] P →ₐ[A] Module.End kA[G] Pbar :=
  (AlgEquiv.restrictScalars A
      (ofModule'_equivAlgEnd (G := G) kA Pbar)).toAlgHom.comp <|
    hf.endAlgHom.comp <|
      (ofModule'_equivAlgEnd (G := G) A P).symm.toAlgHom

/-- Helper for Exercise 14-14.4-6: the transported algebra hom on `A[G]`-linear endomorphisms has
the expected underlying `A`-linear map. -/
theorem endHom_restrict_groupAlgebraAlgHom_toLinearMap
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    (endHom_restrict_groupAlgebraAlgHom (A := A) (G := G) hf).toLinearMap =
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf := by
  ext u x
  change
    (ofModule'_equivAlgEnd (G := G) kA Pbar
      (hf.endAlgHom ((ofModule'_equivAlgEnd (G := G) A P).symm u))) x =
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u x
  simpa using
    congrArg (fun v : Module.End kA[G] Pbar => v x)
      (endHom_restrict_groupAlgebraLinearMap_eq_transport (A := A) (G := G) hf u).symm

/-- Helper for Exercise 14-14.4-6: after identifying equivariant endomorphisms with
`A[G]`-linear endomorphisms, the reduced equivariant endomorphism is exactly the ordinary
base-changed endomorphism on the underlying `kA`-module. -/
theorem endAlgHom_eq_transport_endHom
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (u : EndA) :
    ((ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom u)).restrictScalars kA :
        Pbar →ₗ[kA] Pbar) =
      hf.1.endHom
        (((ofModule'_equivAlgEnd (G := G) A P u).restrictScalars A : P →ₗ[A] P)) := by
  apply hf.1.algHom_ext'
  ext x
  calc
    ((ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom u)).restrictScalars kA) (f x) =
        ofModule'_equivAlgEnd (G := G) kA Pbar (hf.endAlgHom u) (f x) := rfl
    _ = f ((ofModule'_equivAlgEnd (G := G) A P u) x) := by
          exact endAlgHom_transport_comp_apply hf u x
    _ = hf.1.endHom
          (((ofModule'_equivAlgEnd (G := G) A P u).restrictScalars A : P →ₗ[A] P)) (f x) := by
          symm
          simpa using
            hf.1.endHom_comp_apply
              (((ofModule'_equivAlgEnd (G := G) A P u).restrictScalars A : P →ₗ[A] P)) x

/-- Helper for Exercise 14-14.4-6: projectivity of `P` lifts every reduced equivariant
endomorphism of `Pbar`. -/
theorem endAlgHom_surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    Function.Surjective hf.endAlgHom := by
  letI : Module A[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  letI : IsScalarTower A A[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A kA))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap kA (kA[G]) (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (kA[G])
                    (IsLocalRing.residue A c) y)
        _ = c • y := by
            simpa [IsLocalRing.ResidueField.algebraMap_eq] using
              (IsScalarTower.algebraMap_smul kA c y)
  let fAG : P →ₗ[A[G]] Pbar :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := hf.map_smul_restricted_groupAlgebra }
  have hsurjAG : Function.Surjective fAG := by
    intro x
    obtain ⟨y, hy⟩ := hf.surjective x
    exact ⟨y, hy⟩
  intro uBar
  let uBarAG : Pbar →ₗ[A[G]] Pbar :=
    intertwiningMap_restrict_groupAlgebraLinearMap (A := A) (G := G) uBar
  obtain ⟨uLift, huLift⟩ :=
    Module.projective_lifting_property fAG (uBarAG.comp fAG) hsurjAG
  let u : EndA := groupAlgebraLinearMap_toIntertwiningEnd (A := A) (G := G) uLift
  refine ⟨u, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply hf.1.algHom_ext'
  ext x
  have hpoint : f (uLift x) = uBar (f x) := by
    simpa [fAG, uBarAG] using LinearMap.congr_fun huLift x
  calc
    (hf.endAlgHom u) (f x) = f (u x) := by
      exact endAlgHom_comp_apply hf u x
    _ = f (uLift x) := by
      rfl
    _ = uBar (f x) := hpoint

/-- Helper for Exercise 14-14.4-6: after transporting source and target by the canonical
`Representation.ofModule'` identifications, the reduction map on equivariant endomorphisms is
still surjective. -/
theorem transported_groupAlgebraEnd_surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    Function.Surjective
      (fun u : Module.End A[G] P ↦
        ofModule'_equivAlgEnd (G := G) kA Pbar
          (hf.endAlgHom ((ofModule'_equivAlgEnd (G := G) A P).symm u))) := by
  intro uBar
  obtain ⟨vBar, rfl⟩ :=
    (ofModule'_equivAlgEnd (G := G) kA Pbar).surjective uBar
  obtain ⟨v, hv⟩ := endAlgHom_surjective hf vBar
  refine ⟨ofModule'_equivAlgEnd (G := G) A P v, ?_⟩
  simp [hv]

/-- Helper for Exercise 14-14.4-6: the restricted ordinary base-change map on `A[G]`-linear
endomorphisms is surjective. -/
theorem endHom_restrict_groupAlgebraLinearMap_surjective
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    Function.Surjective (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) := by
  intro uBar
  obtain ⟨u, hu⟩ := transported_groupAlgebraEnd_surjective (A := A) (G := G) hf uBar
  refine ⟨u, ?_⟩
  simpa [endHom_restrict_groupAlgebraLinearMap_eq_transport (A := A) (G := G) hf u] using hu

/-- Helper for Exercise 14-14.4-6: once the restricted ordinary base-change map on
`A[G]`-linear endomorphisms is known to be a residue-field base change, the same is true for the
transported map on equivariant endomorphisms. -/
theorem endAlgHom_isBaseChange_iff_restricted
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    IsBaseChange kA hf.endAlgHom.toLinearMap ↔
      IsBaseChange kA (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) := by
  let eSource : EndA ≃ₗ[A] EndAG :=
    (ofModule'_equivAlgEnd (G := G) A P).toLinearEquiv
  let eTarget : EndkA ≃ₗ[kA] EndkAG :=
    (ofModule'_equivAlgEnd (G := G) kA Pbar).toLinearEquiv
  have hcomm :
      endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf ∘ₗ eSource =
        (LinearEquiv.restrictScalars A eTarget) ∘ₗ hf.endAlgHom.toLinearMap := by
    ext u x
    simpa [eSource, eTarget] using
      congrArg (fun v : EndkAG => v x)
        (endHom_restrict_groupAlgebraLinearMap_eq_transport (A := A) (G := G) hf
          (eSource u))
  constructor
  · intro hEnd
    have heTarget : IsBaseChange kA eTarget.toLinearMap :=
      IsBaseChange.ofEquiv eTarget
    have hcomp :
        IsBaseChange kA
          ((LinearEquiv.restrictScalars A eTarget).toLinearMap ∘ₗ hf.endAlgHom.toLinearMap) := by
      simpa using
        (IsBaseChange.comp (R := A) (S := kA) (T := kA) hEnd heTarget)
    have hcomp' :
        IsBaseChange kA
          (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf ∘ₗ eSource.toLinearMap) := by
      simpa [hcomm] using hcomp
    have heSource : IsBaseChange A eSource.toLinearMap :=
      IsBaseChange.ofEquiv eSource
    exact
      (IsBaseChange.comp_iff
        (R := A) (S := A) (T := kA) (f := eSource.toLinearMap)
        (h := endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) heSource).1 hcomp'
  · intro hRestr
    have heSource : IsBaseChange A eSource.toLinearMap :=
      IsBaseChange.ofEquiv eSource
    have hcomp' :
        IsBaseChange kA
          (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf ∘ₗ eSource.toLinearMap) := by
      simpa using
        (IsBaseChange.comp
          (R := A) (S := A) (T := kA) heSource hRestr)
    have hcomp :
        IsBaseChange kA
          ((LinearEquiv.restrictScalars A eTarget).toLinearMap ∘ₗ hf.endAlgHom.toLinearMap) := by
      simpa [hcomm] using hcomp'
    have heTargetSymm : IsBaseChange kA eTarget.symm.toLinearMap :=
      IsBaseChange.ofEquiv eTarget.symm
    simpa using
      (IsBaseChange.comp
        (R := A) (S := kA) (T := kA) hcomp heTargetSymm)

/-- Helper for Exercise 14-14.4-6: once the restricted ordinary base-change map on
`A[G]`-linear endomorphisms is known to be a residue-field base change, the same is true for the
transported map on equivariant endomorphisms. -/
theorem endAlgHom_isBaseChange_of_restricted
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (hbase :
      IsBaseChange kA (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf)) :
    IsBaseChange kA hf.endAlgHom.toLinearMap := by
  exact (endAlgHom_isBaseChange_iff_restricted (A := A) (G := G) hf).2 hbase

end LinearMap.IsResidueFieldReduction

end
