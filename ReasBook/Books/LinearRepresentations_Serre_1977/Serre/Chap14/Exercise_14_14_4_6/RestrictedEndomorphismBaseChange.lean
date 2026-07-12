import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6.EndomorphismReductionTransport

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u v w x

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type v} [Group G]
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

/-- Helper for Exercise 14-14.4-6: restricting scalars along `A[G] → kA[G]` gives a canonical
`A[G]`-module structure on any `kA[G]`-module. -/
noncomputable abbrev restricted_groupAlgebraModule
    (Qbar : Type*) [AddCommGroup Qbar] [Module kA Qbar] [Module kA[G] Qbar] :
    Module A[G] Qbar :=
  Module.compHom Qbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))

/-- Helper for Exercise 14-14.4-6: after restricting scalars from `kA[G]` to `A[G]`, the original
`A`-action is the scalar tower coming from `A → A[G]`. -/
theorem restricted_groupAlgebra_isScalarTower
    (Qbar : Type*) [AddCommGroup Qbar] [Module kA Qbar] [Module A Qbar]
    [IsScalarTower A kA Qbar] [Module kA[G] Qbar] [IsScalarTower kA kA[G] Qbar] :
    letI : Module A[G] Qbar := restricted_groupAlgebraModule (A := A) (G := G) Qbar
    IsScalarTower A A[G] Qbar := by
  letI : Module A[G] Qbar := restricted_groupAlgebraModule (A := A) (G := G) Qbar
  exact IsScalarTower.of_algebraMap_smul fun c y ↦ by
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

/-- Helper for Exercise 14-14.4-6: after restricting scalars from `kA[G]` to `A[G]`, the
`kA`-action still commutes with the `A[G]`-action. -/
theorem restricted_groupAlgebra_smulCommClass
    (Qbar : Type*) [AddCommGroup Qbar] [Module kA Qbar] [Module kA[G] Qbar]
    [IsScalarTower kA kA[G] Qbar] :
    letI : Module A[G] Qbar := restricted_groupAlgebraModule (A := A) (G := G) Qbar
    SMulCommClass A[G] kA Qbar := by
  letI : Module A[G] Qbar := restricted_groupAlgebraModule (A := A) (G := G) Qbar
  refine ⟨fun a c y ↦ ?_⟩
  change
    (MonoidAlgebra.mapRingHom G (algebraMap A kA) a) • (c • y) =
      c • ((MonoidAlgebra.mapRingHom G (algebraMap A kA) a) • y)
  simpa using smul_comm (MonoidAlgebra.mapRingHom G (algebraMap A kA) a) c y

/-- Helper for Exercise 14-14.4-6: after restricting scalars along `A[G] → kA[G]`, the reduction
map itself is `A[G]`-linear. -/
noncomputable def residueFieldReduction_groupAlgebraLinearMap
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    letI : Module A[G] Pbar :=
      Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
    P →ₗ[A[G]] Pbar :=
  letI : Module A[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A kA))
  { toFun := f
    map_add' := f.map_add
    map_smul' := hf.map_smul_restricted_groupAlgebra }

/-- Helper for Exercise 14-14.4-6: reducing each component of a finite tuple is a residue-field
base change. This is the ambient finite-product step needed before descending along the retract
coming from projectivity of `P`. -/
theorem finitePow_residueFieldReduction_isBaseChange
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    (n : Nat) :
    IsBaseChange kA (LinearMap.compLeft f (Fin n)) := by
  simpa using (IsBaseChange.finitePow (S := kA) (ι := Fin n) hf.1)

/-- Helper for Exercise 14-14.4-6: coefficientwise reduction on `A[G]` is the linear-combination
map attached to the canonical `kA[G]` basis. -/
theorem groupAlgebra_reduction_eq_basis_linearCombination :
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
        A[G] →ₗ[A] kA[G])) =
      Finsupp.linearCombination A (fun g : G => (MonoidAlgebra.basis G kA) g) := by
  apply (MonoidAlgebra.basis G A).ext
  intro g
  rw [MonoidAlgebra.basis_apply]
  change
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
        A[G] →ₗ[A] kA[G]) (Finsupp.single g (1 : A))) =
      (Finsupp.linearCombination A (fun g' : G => (MonoidAlgebra.basis G kA) g'))
        (Finsupp.single g (1 : A))
  rw [Finsupp.linearCombination_single, MonoidAlgebra.basis_apply]
  simp [MonoidAlgebra.mapAlgHom_single, IsLocalRing.ResidueField.algebraMap_eq]

/-- Helper for Exercise 14-14.4-6: the coefficientwise reduction map on the free rank-one
`A[G]`-module is itself a residue-field reduction. -/
theorem groupAlgebra_reduction_isResidueFieldReduction :
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
        A[G] →ₗ[A] kA[G])).IsResidueFieldReduction G := by
  have hbase :
      IsBaseChange kA
        (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
          A[G] →ₗ[A] kA[G])) := by
    rw [groupAlgebra_reduction_eq_basis_linearCombination (A := A) (G := G)]
    exact IsBaseChange.of_basis (A := A) (MonoidAlgebra.basis G kA)
  constructor
  · exact hbase
  · refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    change
      ((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap
        (MonoidAlgebra.of A G g • x)) =
          (MonoidAlgebra.mapRingHom G (algebraMap A kA)
            (MonoidAlgebra.of A G g)) •
            ((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap x)
    simpa [MonoidAlgebra.of_apply, smul_eq_mul] using
      (MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).map_mul
        (MonoidAlgebra.of A G g) x

/-- Helper for Exercise 14-14.4-6: the coefficientwise reduction map on a finite free ambient
module `(Fin n → A[G])` is a residue-field reduction. -/
theorem finite_free_groupAlgebra_residueFieldReduction
    (n : Nat) :
    (LinearMap.compLeft
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
        A[G] →ₗ[A] kA[G])) (Fin n)).IsResidueFieldReduction G := by
  have hred :
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
          A[G] →ₗ[A] kA[G])).IsResidueFieldReduction G :=
    groupAlgebra_reduction_isResidueFieldReduction (A := A) (G := G)
  constructor
  · simpa using IsBaseChange.finitePow (S := kA) (ι := Fin n) hred.1
  · refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    funext i
    change
      ((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap
        (MonoidAlgebra.of A G g • x i)) =
          (MonoidAlgebra.mapRingHom G (algebraMap A kA)
            (MonoidAlgebra.of A G g)) •
            ((LinearMap.compLeft
              (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A kA)).toLinearMap :
                A[G] →ₗ[A] kA[G])) (Fin n)) x i)
    simpa [LinearMap.compLeft_apply, MonoidAlgebra.of_apply, smul_eq_mul] using
      hred.map_monoidAlgebra_of g (x i)

/-- Helper for Exercise 14-14.4-6: the ordinary base-change map on `A[G]`-linear endomorphisms of
`P` is itself a residue-field base change. -/
theorem restricted_groupAlgebraEnd_isBaseChange
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G) :
    IsBaseChange kA (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) := by
  letI : Module A[G] Pbar := restricted_groupAlgebraModule (A := A) (G := G) Pbar
  letI : IsScalarTower A A[G] Pbar :=
    restricted_groupAlgebra_isScalarTower (A := A) (G := G) Pbar
  letI : SMulCommClass A[G] kA Pbar :=
    restricted_groupAlgebra_smulCommClass (A := A) (G := G) Pbar
  letI : Module.Finite A[G] P := Module.Finite.of_restrictScalars_finite A A[G] P
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' (A[G]) P
  letI : Module.Free A[G] (Fin n → A[G]) :=
    Module.Free.of_basis (Pi.basisFun (A[G]) (Fin n))
  letI : Module.Finite A[G] (Fin n → A[G]) :=
    Module.Finite.of_basis (Pi.basisFun (A[G]) (Fin n))
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).1
    (inferInstance : Module.Projective A[G] P)
  let toAmbient : EndAG →ₗ[A] Fin n → P :=
    { toFun := fun u j ↦ (u.comp s) (Pi.single j 1)
      map_add' := by
        intro u v
        ext j
        rfl
      map_smul' := by
        intro a u
        ext j
        rfl }
  let fromAmbient : (Fin n → P) →ₗ[A] EndAG :=
    { toFun := fun x ↦ ((Pi.basisFun (A[G]) (Fin n)).constr A x).comp i
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro a x
        ext z
        simp }
  let toAmbientBar : EndkAG →ₗ[kA] Fin n → Pbar :=
    { toFun := fun u j ↦ u (f (s (Pi.single j 1)))
      map_add' := by
        intro u v
        ext j
        rfl
      map_smul' := by
        intro a u
        ext j
        rfl }
  have hsplit : fromAmbient.comp toAmbient = LinearMap.id := by
    ext u x
    change (((Pi.basisFun (A[G]) (Fin n)).constr A (toAmbient u)).comp i) x = u x
    have hconstr :
        (Pi.basisFun (A[G]) (Fin n)).constr A (toAmbient u) = u.comp s := by
      refine (Pi.basisFun (A[G]) (Fin n)).constr_eq A ?_
      intro j
      simp [toAmbient]
    calc
      (((Pi.basisFun (A[G]) (Fin n)).constr A (toAmbient u)).comp i) x
          = ((u.comp s).comp i) x := by
              rw [hconstr]
      _ = u x := by
            simp [LinearMap.comp_assoc, hi]
  have hcomm :
      (toAmbientBar.restrictScalars A).comp
          (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) =
        (LinearMap.compLeft f (Fin n)) ∘ₗ toAmbient := by
    ext u j
    exact endHom_restrict_groupAlgebraLinearMap_comp_apply (A := A) (G := G) hf u
      (s (Pi.single j 1))
  have hAmbient : IsBaseChange kA (LinearMap.compLeft f (Fin n)) :=
    finitePow_residueFieldReduction_isBaseChange (A := A) (G := G) hf n
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  let liftAmbient : (Fin n → Pbar) →ₗ[kA] Q :=
    hAmbient.lift (g.comp fromAmbient)
  let liftRestricted : EndkAG →ₗ[kA] Q :=
    liftAmbient.comp toAmbientBar
  have hlift :
      (liftRestricted.restrictScalars A).comp
          (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf) = g := by
    ext u
    calc
      liftRestricted (endHom_restrict_groupAlgebraLinearMap (A := A) (G := G) hf u)
          = liftAmbient ((LinearMap.compLeft f (Fin n)) (toAmbient u)) := by
              simpa [liftRestricted] using congrArg (fun m : Fin n → Pbar => liftAmbient m)
                (LinearMap.congr_fun hcomm u)
      _ = (g.comp fromAmbient) (toAmbient u) := by
            simpa [liftAmbient] using hAmbient.lift_eq (g.comp fromAmbient) (toAmbient u)
      _ = g u := by
            simpa [LinearMap.comp_apply] using congrArg g (LinearMap.congr_fun hsplit u)
  refine ⟨liftRestricted, hlift, ?_⟩
  intro g' hg'
  ext uBar
  obtain ⟨u, rfl⟩ :=
    endHom_restrict_groupAlgebraLinearMap_surjective (A := A) (G := G) hf uBar
  have hg_eval := congrArg (fun l : EndAG →ₗ[A] Q => l u) hg'
  have hlift_eval := congrArg (fun l : EndAG →ₗ[A] Q => l u) hlift
  simpa using hg_eval.trans hlift_eval.symm

end LinearMap.IsResidueFieldReduction

end
