import Mathlib
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import StacksProject_2024.stacks_project.Chap15.Lemma_15_28_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open ModuleCat
open scoped TensorProduct
open scoped KoszulComplex

namespace RingTheory.Sequence

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

variable {M N : Type u} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: module-valued regularity predicates defined by Koszul homology and their
  behavior under flat base change;
* sampled owner API: `IsH1RegularOn`, `IsKoszulRegularOn`, `IsBaseChange`, `TensorProduct.isBaseChange`,
  and the earlier chapter base-change pattern `IsQuasiRegular.of_flat_of_isBaseChange`;
* owner abstraction: the source-facing owners are `IsH1RegularOn` and `IsKoszulRegularOn`, while
  `IsBaseChange S f` is the core/canonical owner for the chosen base-change realization;
* primitive data vs derived API: the primitive content here is the owner-level transport across an
  arbitrary `IsBaseChange S f`; the tensor-product statements are derived bridge/view
  specializations obtained from `TensorProduct.isBaseChange`.
-/

/-- Helper for Lemma 15.30.5: the Koszul complex on `s` with coefficients tensored with `M`. -/
private abbrev tensor_koszul_complex (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] {r : ℕ} (s : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (K^•(s))

/-- Helper for Lemma 15.30.5: scalar extension on `ModuleCat` along `R → S`. -/
private abbrev extendScalarsFunctor :
    ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap R S)

/-- Helper for Lemma 15.30.5: scalar extension on chain complexes over `ModuleCat`. -/
private abbrev extendScalarsChainComplex :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex (ModuleCat.{u} S) ℕ :=
  (extendScalarsFunctor (R := R) (S := S)).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Helper for Lemma 15.30.5: the restricted scalar action on `S` is canonically the usual one. -/
private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.30.5: after restricting scalars from `S`, the induced `R`- and
`S`-actions on `S` form the expected scalar tower. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Lemma 15.30.5: the unit element in the restricted-scalars copy of `S`. -/
private abbrev restrictScalarsSelfOne :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  (1 : S)

/-- Helper for Lemma 15.30.5: the scalar-extension functor sends `M` to the canonical module
`S ⊗[R] M`. -/
private noncomputable def extendScalarsModuleIso
    (M : Type u) [AddCommGroup M] [Module R M] :
    (extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M) ≅
      ModuleCat.of S (S ⊗[R] M) := by
  -- Expand the change-of-rings functor and collapse the restricted-scalar factor on `S`.
  simpa [extendScalarsFunctor, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv (R := R) (S := S))
      (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Lemma 15.30.5: extending scalars after tensoring with `M` agrees functorially with
tensoring by the base-changed module after extending scalars. -/
private noncomputable def extendScalarsTensorLeftNatIso
    (M : ModuleCat.{u} R) :
    tensorLeft M ⋙ extendScalarsFunctor (R := R) (S := S) ≅
      extendScalarsFunctor (R := R) (S := S) ⋙
        tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj M) :=
  NatIso.ofComponents
    (fun X ↦ (Functor.Monoidal.μIso (extendScalarsFunctor (R := R) (S := S)) M X).symm)
    (by
      intro X Y g
      exact
        (Functor.OplaxMonoidal.δ_natural_right
          (extendScalarsFunctor (R := R) (S := S)) M g).symm)

-- Route correction: the remaining base-change comparison is now split into a verified degreewise
-- exterior-power bridge for the free module `Fin r → R`, leaving only differential compatibility
-- as the unresolved chain-level step.

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the coordinatewise algebra map on `Fin r → R` is a base change to
`Fin r → S`. -/
private theorem finite_pow_isBaseChange {r : ℕ} :
    IsBaseChange S ((Algebra.linearMap R S).compLeft (Fin r)) := by
  -- Base change on finite powers is the `IsBaseChange.finitePow` specialization of
  -- the scalar-extension map `R → S`.
  simpa using IsBaseChange.finitePow (S := S) (ι := Fin r)
    (IsBaseChange.linearMap (R := R) (S := S))

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: transporting the standard basis of `Fin r → R` along the canonical
base-change map recovers the standard basis of `Fin r → S`. -/
private theorem finite_pow_baseChange_basis_eq {r : ℕ} :
    IsBaseChange.basis (Pi.basisFun R (Fin r))
        (finite_pow_isBaseChange (R := R) (S := S) (r := r)) =
      Pi.basisFun S (Fin r) := by
  ext i j
  -- Both bases have the same `j`-th coordinate on the `i`-th basis vector.
  rw [IsBaseChange.basis_apply]
  by_cases h : j = i
  · subst h
    simp [LinearMap.compLeft_apply, Pi.basisFun]
  · simp [LinearMap.compLeft_apply, Pi.basisFun, h]

/-- Helper for Lemma 15.30.5: the degree-`n` exterior power of `Fin r → S` is the scalar
extension of the degree-`n` exterior power of `Fin r → R`. -/
private noncomputable def exterior_power_fin_base_change_equiv {r n : ℕ} :
    S ⊗[R] (⋀[R]^n (Fin r → R)) ≃ₗ[S] ⋀[S]^n (Fin r → S) :=
  let eR := (Pi.basisFun R (Fin r)).exteriorPower n
  let eS := (Pi.basisFun S (Fin r)).exteriorPower n
  (LinearEquiv.baseChange R S _ _ eR.repr) ≪≫ₗ
    (IsBaseChange.finsuppPow (ι := ↑(Set.powersetCard (Fin r) n))
      (IsBaseChange.linearMap (R := R) (S := S))).equiv ≪≫ₗ
    eS.repr.symm

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the exterior-power base-change equivalence sends the canonical
generator `1 ⊗ ιMulti` to the corresponding generator after applying `algebraMap R S`
coordinatewise. -/
private theorem exterior_power_fin_base_change_equiv_tmul_ιMulti {r n : ℕ}
    (m : Fin n → Fin r) :
    exterior_power_fin_base_change_equiv (R := R) (S := S) (r := r) (n := n)
      (1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R))) =
      exteriorPower.ιMulti S n (fun i ↦ Pi.single (m i) (1 : S)) := by
  classical
  let eS := (Pi.basisFun S (Fin r)).exteriorPower n
  apply eS.repr.injective
  ext s
  -- Compare both sides after expanding the scalar-extension equivalence on basis coordinates.
  simp only [exterior_power_fin_base_change_equiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul]
  rw [LinearEquiv.apply_symm_apply]
  -- The remaining coordinate is the determinant of the same `0/1` incidence matrix over `R` and
  -- `S`, so `RingHom.map_det` transports it across `algebraMap R S`.
  suffices hcoeff :
      ((Finsupp.mapRange.linearMap (Algebra.linearMap R S))
          (((Module.Basis.exteriorPower n (Pi.basisFun R (Fin r))).repr
            ((exteriorPower.ιMulti R n) fun i ↦ Pi.single (m i) (1 : R))))) s =
        (eS.repr ((exteriorPower.ιMulti S n) fun i ↦ Pi.single (m i) (1 : S))) s by
    simpa only [one_smul] using hcoeff
  let A : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j ↦ if (Set.powersetCard.ofFinEmbEquiv.symm s) j = m i then (1 : R) else 0
  have hcoeff_R :
      (((Module.Basis.exteriorPower n (Pi.basisFun R (Fin r))).repr
          ((exteriorPower.ιMulti R n) fun i ↦ Pi.single (m i) (1 : R))) s) = A.det := by
    simpa [A, exteriorPower.basis_repr_apply, Pi.single_apply]
  have hcoeff_S :
      (eS.repr ((exteriorPower.ιMulti S n) fun i ↦ Pi.single (m i) (1 : S))) s =
        (Matrix.of fun i j ↦ if (Set.powersetCard.ofFinEmbEquiv.symm s) j = m i then
          (1 : S) else 0).det := by
    simpa [A, eS, exteriorPower.basis_repr_apply, Pi.single_apply]
  have hA : RingHom.mapMatrix (algebraMap R S) A =
      Matrix.of fun i j ↦ if (Set.powersetCard.ofFinEmbEquiv.symm s) j = m i then (1 : S) else 0 := by
    ext i j
    simp [A]
  calc
    ((Finsupp.mapRange.linearMap (Algebra.linearMap R S))
          (((Module.Basis.exteriorPower n (Pi.basisFun R (Fin r))).repr
            ((exteriorPower.ιMulti R n) fun i ↦ Pi.single (m i) (1 : R)))))
        s = algebraMap R S A.det := by
          simp [hcoeff_R]
    _ = (Matrix.of fun i j ↦ if (Set.powersetCard.ofFinEmbEquiv.symm s) j = m i then
          (1 : S) else 0).det := by
          simpa [A, hA] using RingHom.map_det (algebraMap R S) A
    _ = (eS.repr ((exteriorPower.ιMulti S n) fun i ↦ Pi.single (m i) (1 : S))) s := by
          rw [hcoeff_S]

/-- Helper for Lemma 15.30.5: the degree-`n` exterior power of `Fin r → S`, viewed in
`ModuleCat S`, identifies with the scalar extension of the corresponding exterior power over `R`. -/
private noncomputable def exterior_power_fin_base_change_iso {r n : ℕ} :
    ModuleCat.of S (⋀[S]^n (Fin r → S)) ≅
      ModuleCat.of S (S ⊗[R] (⋀[R]^n (Fin r → R))) :=
  (exterior_power_fin_base_change_equiv (R := R) (S := S) (r := r) (n := n)).symm.toModuleIso

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the inverse component of the exterior-power base-change
isomorphism sends the canonical `ιMulti` generator over `S` back to `1 ⊗ ιMulti` over `R`. -/
private theorem exterior_power_fin_base_change_iso_hom_apply_ιMulti {r n : ℕ}
    (m : Fin n → Fin r) :
    (exterior_power_fin_base_change_iso (R := R) (S := S) (r := r) (n := n)).hom
      (exteriorPower.ιMulti S n (fun i ↦ Pi.single (m i) (1 : S))) =
      1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R)) := by
  -- Apply the forward equivalence so the goal becomes the already verified generator formula.
  change
    (exterior_power_fin_base_change_equiv (R := R) (S := S) (r := r) (n := n)).symm
      (exteriorPower.ιMulti S n (fun i ↦ Pi.single (m i) (1 : S))) =
      1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R))
  apply (exterior_power_fin_base_change_equiv (R := R) (S := S) (r := r) (n := n)).injective
  -- The forward direction is exactly `exterior_power_fin_base_change_equiv_tmul_ιMulti`.
  simpa using
    (exterior_power_fin_base_change_equiv_tmul_ιMulti (R := R) (S := S) (r := r) (n := n) m).symm

/-- Helper for Lemma 15.30.5: flat scalar extension preserves vanishing of homology for chain
complexes of modules. -/
theorem isZero_homology_extendScalars_of_flat {C : ChainComplex (ModuleCat.{u} R) ℕ} {i : ℕ}
    (hC : IsZero (C.homology i)) :
    IsZero (((extendScalarsChainComplex (R := R) (S := S)).obj C).homology i) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := extendScalarsFunctor (R := R) (S := S)
  let C' : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ) := C
  let FC : HomologicalComplex (ModuleCat.{u} S) (ComplexShape.down ℕ) :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C'
  have hflat : (algebraMap R S).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  letI : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  letI : F.PreservesHomology := inferInstance
  let e1 :=
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} S) (ComplexShape.down ℕ) i).app FC
  let e2 := (ShortComplex.homologyFunctorIso (F := F)).app (C'.sc i)
  let e3 :=
    F.mapIso
      ((HomologicalComplex.homologyFunctorIso (ModuleCat.{u} R) (ComplexShape.down ℕ) i).app C')
  -- Flat scalar extension preserves homology up to the canonical exact-functor comparison.
  exact IsZero.of_iso (CategoryTheory.Functor.map_isZero F hC) ((e1.trans e2).trans e3.symm)

/-- Helper for Lemma 15.30.5: scalar-extending `koszulLinearForm s` along `R → S` gives the
intermediate linear form on `S ⊗[R] (Fin r → R)` used in the base-change comparison. -/
private noncomputable def finite_pow_scalar_extension_linearForm {r : ℕ} (s : Fin r → R) :
    (S ⊗[R] (Fin r → R)) →ₗ[S] S :=
  (koszulLinearForm (fun i ↦ algebraMap R S (s i))).comp
    (finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.toLinearMap

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the scalar-extended Koszul linear form has the expected pure-tensor
formula. -/
private theorem finite_pow_scalar_extension_linearForm_apply_tmul {r : ℕ} (s : Fin r → R)
    (a : S) (m : Fin r → R) :
    finite_pow_scalar_extension_linearForm (R := R) (S := S) s (a ⊗ₜ[R] m) =
      a * algebraMap R S (koszulLinearForm s m) := by
  -- Route correction: use the verified `IsBaseChange.equiv_tmul` formula first, and only then
  -- evaluate the image-family linear form on the transported pure tensor.
  have htmul :=
      congrArg (koszulLinearForm (fun i ↦ algebraMap R S (s i)))
        (IsBaseChange.equiv_tmul
          (h := finite_pow_isBaseChange (R := R) (S := S) (r := r)) a m)
  simpa [finite_pow_scalar_extension_linearForm, koszulLinearForm,
    Module.piEquiv_apply_apply, mul_comm, mul_left_comm, mul_assoc] using htmul

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the scalar-extended Koszul linear form sends the transported basis
vector to the corresponding image coefficient. -/
private theorem finite_pow_scalar_extension_linearForm_apply_basis_vector {r : ℕ} (s : Fin r → R)
    (i : Fin r) :
    finite_pow_scalar_extension_linearForm (R := R) (S := S) s
      ((1 : S) ⊗ₜ[R] Pi.single i (1 : R)) =
      algebraMap R S (s i) := by
  -- Specialize the pure-tensor formula to the standard basis vector and evaluate the source
  -- linear form on `Pi.single`.
  calc
    finite_pow_scalar_extension_linearForm (R := R) (S := S) s
        ((1 : S) ⊗ₜ[R] Pi.single i (1 : R)) =
      (1 : S) * algebraMap R S (koszulLinearForm s (Pi.single i (1 : R))) := by
        simpa using
          finite_pow_scalar_extension_linearForm_apply_tmul
            (R := R) (S := S) s (1 : S) (Pi.single i (1 : R))
    _ = algebraMap R S (koszulLinearForm s (Pi.single i (1 : R))) := by
      simp
    _ = algebraMap R S (s i) := by
      have hsingle :
          ∑ x, ((Pi.single i (1 : R) : Fin r → R) x) * s x = s i := by
        classical
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji]
        · simp
      congr 1
      rw [koszulLinearForm, Module.piEquiv_apply_apply]
      exact hsingle

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: after identifying `S ⊗[R] (Fin r → R)` with `Fin r → S`, the
image-family linear form agrees with the scalar extension of `koszulLinearForm s`. -/
private theorem koszulLinearForm_image_comp_finite_pow_equiv {r : ℕ} (s : Fin r → R) :
    (koszulLinearForm (fun i ↦ algebraMap R S (s i))).comp
        (finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.toLinearMap =
      finite_pow_scalar_extension_linearForm (R := R) (S := S) s := by
  rfl

namespace KoszulComplex

/-- Helper for Lemma 15.30.5: a compatible linear equivalence induces an isomorphism of Koszul
complexes via `KoszulComplex.map`. -/
private noncomputable def map_iso_of_linearEquiv
    {E E' : Type u} [AddCommGroup E] [Module S E] [AddCommGroup E'] [Module S E']
    {φ : E →ₗ[S] S} {φ' : E' →ₗ[S] S}
    (e : E ≃ₗ[S] E') (hφ : φ'.comp e.toLinearMap = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := KoszulComplex.map e.toLinearMap hφ
  inv :=
    -- The inverse comparison uses the inverse linear equivalence with the transported
    -- compatibility of linear forms.
    KoszulComplex.map e.symm.toLinearMap <| by
      apply LinearMap.ext
      intro x
      simpa using (LinearMap.congr_fun hφ (e.symm x)).symm
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- Check the degreewise composite on exterior-power generators.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom e.symm.toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom e.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using
      congrArg (fun ψ : E ≃ₗ[S] E => ψ (m i)) e.left_inv
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- The reverse composite is identical after the same generator-level simplification.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom e.toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom e.symm.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using
      congrArg (fun ψ : E' ≃ₗ[S] E' => ψ (m i)) e.right_inv

end KoszulComplex

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the `Fin r → S` Koszul complex is first compared with the
intermediate Koszul complex on the scalar-extended free module by `KoszulComplex.map`. -/
private noncomputable def koszul_complex_image_iso_intermediate {r : ℕ} (s : Fin r → R) :
    K^•(fun i ↦ algebraMap R S (s i)) ≅
      koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s) :=
  -- Route correction: package the `Fin r → S` to `S ⊗[R] (Fin r → R)` comparison once via the
  -- generic `KoszulComplex.map`-along-an-equivalence isomorphism, then reverse it.
  (KoszulComplex.map_iso_of_linearEquiv
      (φ := finite_pow_scalar_extension_linearForm (R := R) (S := S) s)
      (φ' := koszulLinearForm (fun i ↦ algebraMap R S (s i)))
      ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv)
      (koszulLinearForm_image_comp_finite_pow_equiv (R := R) (S := S) s)).symm

/-- Helper for Lemma 15.30.5: the free-module base-change equivalence induces a degreewise
linear equivalence on exterior powers. -/
private noncomputable def exterior_power_fin_scalar_extension_equiv {r n : ℕ} :
    ⋀[S]^n (S ⊗[R] (Fin r → R)) ≃ₗ[S] ⋀[S]^n (Fin r → S) :=
  let e := (finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv
  LinearEquiv.ofLinear
    (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by
      apply exteriorPower.linearMap_ext
      ext m
      rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
      rw [LinearMap.compAlternatingMap_apply]
      rw [LinearMap.id_apply]
      refine congrArg
        (fun v : Fin n → Fin r → S ↦
          ((exteriorPower.ιMulti S n v : ⋀[S]^n (Fin r → S)) :
            ExteriorAlgebra S (Fin r → S))) ?_
      ext i
      simpa using congrArg (fun ψ : S ⊗[R] (Fin r → R) ≃ₗ[S] S ⊗[R] (Fin r → R) => ψ (m i))
        e.left_inv)
    (by
      apply exteriorPower.linearMap_ext
      ext m
      rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
      rw [LinearMap.compAlternatingMap_apply]
      rw [LinearMap.id_apply]
      refine congrArg
        (fun v : Fin n → S ⊗[R] (Fin r → R) ↦
          ((exteriorPower.ιMulti S n v : ⋀[S]^n (S ⊗[R] (Fin r → R))) :
            ExteriorAlgebra S (S ⊗[R] (Fin r → R)))) ?_
      ext i
      simpa using congrArg (fun ψ : (Fin r → S) ≃ₗ[S] (Fin r → S) => ψ (m i)) e.right_inv)

/-- Helper for Lemma 15.30.5: the pure scalar-extension comparison on the degree-`n` exterior
powers is the concrete exterior-power equivalence followed by the verified `Fin r → S`
base-change iso. -/
private noncomputable def exterior_power_fin_scalar_extension_component_iso {r n : ℕ} :
    ModuleCat.of S (⋀[S]^n (S ⊗[R] (Fin r → R))) ≅
      ModuleCat.of S (S ⊗[R] (⋀[R]^n (Fin r → R))) :=
  (exterior_power_fin_scalar_extension_equiv (R := R) (S := S) (r := r) (n := n)).toModuleIso ≪≫
    exterior_power_fin_base_change_iso (R := R) (S := S) (r := r) (n := n)

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the scalar-extension component iso sends the canonical
`ιMulti`-generator in `⋀[S]^n (S ⊗[R] (Fin r → R))` to `1 ⊗ ιMulti` in the scalar-extended
exterior power over `R`. -/
private theorem exterior_power_fin_scalar_extension_component_iso_hom_apply_ιMulti {r n : ℕ}
    (m : Fin n → Fin r) :
    (exterior_power_fin_scalar_extension_component_iso (R := R) (S := S) (r := r) (n := n)).hom
      (exteriorPower.ιMulti S n
        (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R))) =
      1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R)) := by
  -- First transport the generator to `Fin r → S`, then apply the established `Fin r → S`
  -- exterior-power base-change formula.
  change
    (exterior_power_fin_base_change_iso (R := R) (S := S) (r := r) (n := n)).hom
      ((exterior_power_fin_scalar_extension_equiv (R := R) (S := S) (r := r) (n := n))
        (exteriorPower.ιMulti S n
          (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)))) =
    1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R))
  change
    (exterior_power_fin_base_change_iso (R := R) (S := S) (r := r) (n := n)).hom
      (exteriorPower.map n
        ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.toLinearMap)
        (exteriorPower.ιMulti S n
          (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)))) =
    1 ⊗ₜ[R] exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R))
  rw [exteriorPower.map_apply_ιMulti]
  have hgen :
      ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv ∘
          fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)) =
        fun i ↦ Pi.single (m i) (1 : S) := by
    ext i j
    simp [IsBaseChange.equiv_tmul, LinearMap.compLeft_apply, Pi.single_apply]
  simpa [IsBaseChange.equiv_tmul] using
    hgen ▸
      exterior_power_fin_base_change_iso_hom_apply_ιMulti
        (R := R) (S := S) (r := r) (n := n) m

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the basis on `S ⊗[R] (Fin r → R)` obtained by transporting the
standard basis of `Fin r → S` along the inverse base-change equivalence is the expected
pure-tensor basis. -/
private theorem finite_pow_scalar_extension_basis_apply {r : ℕ} (i : Fin r) :
    ((Pi.basisFun S (Fin r)).map
        ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm)) i =
      (1 : S) ⊗ₜ[R] Pi.single i (1 : R) := by
  -- Apply the forward base-change equivalence so the claim becomes the standard pure-tensor
  -- formula for the transported coordinate basis vector.
  apply ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv).injective
  ext j
  simp [Module.Basis.map_apply, IsBaseChange.equiv_tmul, Pi.basisFun, Pi.single_apply]

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the exterior-power basis on
`⋀[S]^n (S ⊗[R] (Fin r → R))` induced from the transported coordinate basis is the explicit
`ιMulti` pure-tensor basis. -/
private theorem exterior_power_fin_scalar_extension_basis_apply {r n : ℕ}
    (t : Set.powersetCard (Fin r) n) :
    (Module.Basis.exteriorPower n
        ((Pi.basisFun S (Fin r)).map
          ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm))) t =
      exteriorPower.ιMulti S n
        (fun i ↦
          (1 : S) ⊗ₜ[R]
            Pi.single ((Set.powersetCard.ofFinEmbEquiv.symm t) i) (1 : R)) := by
  -- Unfold the exterior-power basis element to the corresponding `ιMulti` family and then
  -- rewrite each transported basis vector to its pure-tensor form.
  apply Subtype.ext
  calc
    ((Module.Basis.exteriorPower n
        ((Pi.basisFun S (Fin r)).map
          ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm))) t :
        ExteriorAlgebra S (S ⊗[R] (Fin r → R))) =
        ExteriorAlgebra.ιMulti_family S n
          (⇑((Pi.basisFun S (Fin r)).map
            ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm))) t := by
        simpa using
          (ExteriorAlgebra.basis_apply_powersetCard
            (b := (Pi.basisFun S (Fin r)).map
              ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm))
            (s := t)).symm
    _ = ((exteriorPower.ιMulti S n
          (fun i ↦
            (1 : S) ⊗ₜ[R]
              Pi.single ((Set.powersetCard.ofFinEmbEquiv.symm t) i) (1 : R)) :
            ⋀[S]^n (S ⊗[R] (Fin r → R))) :
          ExteriorAlgebra S (S ⊗[R] (Fin r → R))) := by
        simp only [ExteriorAlgebra.ιMulti_family]
        congr 1
        ext i
        simpa using
          finite_pow_scalar_extension_basis_apply
            (R := R) (S := S) (r := r) ((Set.powersetCard.ofFinEmbEquiv.symm t) i)

/-- Helper for Lemma 15.30.5: the transported coordinate basis induces the canonical basis used
to compare the scalar-extended exterior powers degreewise. -/
private noncomputable abbrev exterior_power_fin_scalar_extension_basis {r n : ℕ} :
    Module.Basis (Set.powersetCard (Fin r) n) S
      (⋀[S]^n (S ⊗[R] (Fin r → R))) :=
  Module.Basis.exteriorPower n
    ((Pi.basisFun S (Fin r)).map
      ((finite_pow_isBaseChange (R := R) (S := S) (r := r)).equiv.symm))

/-- Helper for Lemma 15.30.5: the concrete exterior-power scalar-extension iso is exactly the
degree-`n` component comparison between the intermediate Koszul complex and the scalar extension
of `K^•(s)`. -/
private noncomputable def koszul_complex_scalar_extension_component_iso {r : ℕ}
    (s : Fin r → R) (n : ℕ) :
    (koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).X n ≅
      ((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).X n :=
  exterior_power_fin_scalar_extension_component_iso (R := R) (S := S) (r := r) (n := n) ≪≫
    (by
      simpa [koszulComplex, extendScalarsChainComplex, extendScalarsFunctor, ModuleCat.exteriorPower]
        using
          (extendScalarsModuleIso (R := R) (S := S) (⋀[R]^n (Fin r → R))).symm)

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the full component iso to the scalar-extended source complex sends
the displayed `ιMulti` generator to the expected pure tensor over `R`. -/
private theorem koszul_complex_scalar_extension_component_iso_hom_apply_ιMulti
    {r n : ℕ} (s : Fin r → R) (m : Fin n → Fin r) :
    (koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom
      (exteriorPower.ιMulti S n
        (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R))) =
      restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
        exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R)) := by
  -- Expose the two factors in the component comparison: first the exterior-power bridge, then the
  -- scalar-extension module identification.
  change
    (extendScalarsModuleIso (R := R) (S := S) (⋀[R]^n (Fin r → R))).inv
      ((exterior_power_fin_scalar_extension_component_iso
          (R := R) (S := S) (r := r) (n := n)).hom
        (exteriorPower.ιMulti S n
          (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)))) =
      restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
        exteriorPower.ιMulti R n (fun i ↦ Pi.single (m i) (1 : R))
  rw [exterior_power_fin_scalar_extension_component_iso_hom_apply_ιMulti]
  -- The remaining factor is the canonical identification of scalar extension with `S ⊗[R] -`.
  rfl

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the intermediate Koszul differential on the pure-tensor
`ιMulti`-generator is the expected alternating deletion sum with coefficients
`algebraMap R S (s (m k))`. -/
private theorem koszul_differential_scalar_extension_apply_ιMulti
    {r n : ℕ} (s : Fin r → R) (m : Fin (n + 1) → Fin r) :
    koszulDifferentialLinearMap
        (finite_pow_scalar_extension_linearForm (R := R) (S := S) s) n
        (exteriorPower.ιMulti S (n + 1)
          (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R))) =
      ∑ k : Fin (n + 1),
        ((-1 : S) ^ (k : ℕ) * algebraMap R S (s (m k))) •
          exteriorPower.ιMulti S n
            (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m (Fin.succAbove k i)) (1 : R)) := by
  -- Replace the differential by the canonical alternating deletion formula and then simplify the
  -- coefficients on each basis vector of the scalar-extended free module.
  simpa [finite_pow_scalar_extension_linearForm_apply_basis_vector]
    using
      (koszulDifferentialLinearMap_apply_ιMulti_eq_sum
        (R := S)
        (E := S ⊗[R] (Fin r → R))
        (φ := finite_pow_scalar_extension_linearForm (R := R) (S := S) s)
        (n := n)
        (v := fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)))

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: in any Koszul complex, the degree-`n + 1 → n` differential is the
underlying Koszul differential linear map. -/
private theorem koszul_complex_differential_hom_eq_linearMap
    {A E : Type u} [CommRing A] [AddCommGroup E] [Module A E]
    (φ : E →ₗ[A] A) (n : ℕ) :
    ModuleCat.Hom.hom ((koszulComplex φ).d (n + 1) n) =
      koszulDifferentialLinearMap φ n := by
  -- Unfold the Koszul complex once so the categorical differential becomes the defining linear
  -- map on exterior powers.
  have hd :
      (koszulComplex φ).d (n + 1) n = ModuleCat.ofHom (koszulDifferentialLinearMap φ n) := by
    simpa [koszulComplex, koszulDifferential] using
      (ChainComplex.of_d ((ModuleCat.of A E).exteriorPower) (koszulDifferential φ) _ n)
  rw [hd]
  rfl

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: scalar extension of the source Koszul differential sends
`1 ⊗ ιMulti` to the same alternating deletion sum on the tensor side. -/
private theorem extendScalars_koszul_differential_apply_tmul_ιMulti
    {r n : ℕ} (s : Fin r → R) (m : Fin (n + 1) → Fin r) :
    ModuleCat.Hom.hom
        (((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n)
        (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R (n + 1)
          (fun i ↦ Pi.single (m i) (1 : R))) =
      ∑ k : Fin (n + 1),
        ((-1 : S) ^ (k : ℕ) * algebraMap R S (s (m k))) •
          (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R n
            (fun i ↦ Pi.single (m (Fin.succAbove k i)) (1 : R))) := by
  -- Rewrite the mapped differential as the base change of the source differential and then push
  -- the pure tensor through the explicit alternating deletion sum termwise.
  calc
    ModuleCat.Hom.hom
        (((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n)
        (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R (n + 1)
          (fun i ↦ Pi.single (m i) (1 : R))) =
      restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
        koszulDifferentialLinearMap (koszulLinearForm s) n
          (exteriorPower.ιMulti R (n + 1) (fun i ↦ Pi.single (m i) (1 : R))) := by
        have hbase :
            ModuleCat.Hom.hom
                (((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n)
                (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R (n + 1)
                  (fun i ↦ Pi.single (m i) (1 : R))) =
              restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
                ModuleCat.Hom.hom (koszulDifferential (koszulLinearForm s) n)
                  (exteriorPower.ιMulti R (n + 1) (fun i ↦ Pi.single (m i) (1 : R))) := by
          letI : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
          simpa only [restrictScalarsSelfOne, extendScalarsChainComplex,
            CategoryTheory.Functor.mapHomologicalComplex_obj_d, ModuleCat.extendScalars,
            ModuleCat.ExtendScalars.obj', ModuleCat.ExtendScalars.map', koszulComplex,
            koszulDifferential, ModuleCat.hom_ofHom,
            koszul_complex_differential_hom_eq_linearMap (φ := koszulLinearForm s)] using
            (LinearMap.baseChange_tmul
              (f := (koszulDifferentialLinearMap (koszulLinearForm s) n :
                ↑((K^•(s)).X (n + 1)) →ₗ[R] ↑((K^•(s)).X n)))
              (a := (1 : S))
              (x := exteriorPower.ιMulti R (n + 1) (fun i ↦ Pi.single (m i) (1 : R))))
        simpa [koszulDifferential] using hbase
    _ =
      restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
        ∑ k : Fin (n + 1),
          ((-1 : R) ^ (k : ℕ) * s (m k)) •
            exteriorPower.ιMulti R n
              (fun i ↦ Pi.single (m (Fin.succAbove k i)) (1 : R)) := by
        exact congrArg (fun x ↦ restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] x) <| by
          simpa [koszulLinearForm, Module.piEquiv_apply_apply, Pi.single_apply] using
            (koszulDifferentialLinearMap_apply_ιMulti_eq_sum
              (R := R)
              (E := Fin r → R)
              (φ := koszulLinearForm s)
              (n := n)
              (v := fun i ↦ Pi.single (m i) (1 : R)))
    _ =
      ∑ k : Fin (n + 1),
        ((-1 : S) ^ (k : ℕ) * algebraMap R S (s (m k))) •
          (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R n
            (fun i ↦ Pi.single (m (Fin.succAbove k i)) (1 : R))) := by
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [TensorProduct.tmul_smul]
        change
          ((algebraMap R S (((-1 : R) ^ (k : ℕ) * s (m k)))) •
              (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
                exteriorPower.ιMulti R n
                  (fun i ↦ (Pi.single (m (Fin.succAbove k i)) (1 : R) : Fin r → R)))) =
            (((-1 : S) ^ (k : ℕ) * algebraMap R S (s (m k))) •
              (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
                exteriorPower.ιMulti R n
                  (fun i ↦ (Pi.single (m (Fin.succAbove k i)) (1 : R) : Fin r → R))))
        congr 1
        simp [map_mul, map_pow]

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: evaluating the remaining scalar-extension square on a transported
exterior-power basis vector reduces the chain-map check to a single explicit generator
computation. -/
private theorem exterior_power_fin_scalar_extension_differential_on_basis
    {r : ℕ} (s : Fin r → R) (n : ℕ) (t : Set.powersetCard (Fin r) (n + 1)) :
    ModuleCat.Hom.hom
        ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s (n + 1)).hom ≫
          ((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n)
        (exterior_power_fin_scalar_extension_basis (R := R) (S := S) (r := r) (n := n + 1) t) =
      ModuleCat.Hom.hom
        ((koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).d (n + 1) n ≫
          (koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
        (exterior_power_fin_scalar_extension_basis (R := R) (S := S) (r := r) (n := n + 1) t) := by
  -- Rewrite the transported basis vector to the explicit pure-tensor `ιMulti` generator, so both
  -- branches can be normalized by the same alternating deletion formula.
  set m : Fin (n + 1) → Fin r := fun i ↦ (Set.powersetCard.ofFinEmbEquiv.symm t) i
  have hbasis :
      exterior_power_fin_scalar_extension_basis (R := R) (S := S) (r := r) (n := n + 1) t =
        exteriorPower.ιMulti S (n + 1)
          (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R)) := by
    simpa [m] using
      exterior_power_fin_scalar_extension_basis_apply
        (R := R) (S := S) (r := r) (n := n + 1) t
  -- Normalize both branches to the same alternating deletion sum on the explicit generator.
  rw [hbasis]
  -- Expose the two composites as "apply the first map, then the second" and rewrite each branch
  -- to the same alternating deletion sum.
  simp only [ConcreteCategory.comp_apply]
  let coeff : Fin (n + 1) → S :=
    fun k ↦ ((-1 : S) ^ (k : ℕ) * algebraMap R S (s (m k)))
  let basisS : Fin (n + 1) →
      ↑((koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).X n) :=
    fun k ↦
      exteriorPower.ιMulti S n
        (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m (Fin.succAbove k i)) (1 : R))
  let basisR : Fin (n + 1) →
      ↑((((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).X n)) :=
    fun k ↦
      restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
        exteriorPower.ιMulti R n
          (fun i ↦ Pi.single (m (Fin.succAbove k i)) (1 : R))
  let termS : Fin (n + 1) →
      ↑((koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).X n) :=
    fun k ↦ coeff k • basisS k
  let termR : Fin (n + 1) →
      ↑((((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).X n)) :=
    fun k ↦ coeff k • basisR k
  rw [koszul_complex_scalar_extension_component_iso_hom_apply_ιMulti]
  change
    ModuleCat.Hom.hom
        (((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n)
        (restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R] exteriorPower.ιMulti R (n + 1)
          (fun i ↦ Pi.single (m i) (1 : R))) =
      ModuleCat.Hom.hom
        ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
        (ModuleCat.Hom.hom
          ((koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).d
            (n + 1) n)
          (exteriorPower.ιMulti S (n + 1)
            (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m i) (1 : R))))
  rw [extendScalars_koszul_differential_apply_tmul_ιMulti]
  rw [koszul_complex_differential_hom_eq_linearMap
    (φ := finite_pow_scalar_extension_linearForm (R := R) (S := S) s)]
  symm
  have hdiff := congrArg
      (ModuleCat.Hom.hom
        ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom))
      (koszul_differential_scalar_extension_apply_ιMulti (R := R) (S := S) s m)
  refine hdiff.trans ?_
  -- The remaining comparison is termwise: the component iso sends each truncated `ιMulti`
  -- generator to the matching pure tensor.
  calc
    ModuleCat.Hom.hom
        ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
        (∑ k : Fin (n + 1), termS k) =
      ∑ k : Fin (n + 1),
        ModuleCat.Hom.hom
          ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
          (termS k) := by
        exact
          map_sum
            (ModuleCat.Hom.hom
              ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom))
            termS Finset.univ
    _ = ∑ k : Fin (n + 1), termR k := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        calc
          ModuleCat.Hom.hom
              ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
              (termS k) =
            coeff k •
              ModuleCat.Hom.hom
                ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
                (basisS k) := by
              change
                ModuleCat.Hom.hom
                    ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
                    (coeff k • basisS k) =
                  coeff k •
                    ModuleCat.Hom.hom
                      ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
                      (basisS k)
              simpa using
                (ModuleCat.Hom.hom
                  ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)).map_smul
                  (coeff k) (basisS k)
          _ = coeff k • basisR k := by
              congr 1
              change
                ModuleCat.Hom.hom
                    ((koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom)
                    (exteriorPower.ιMulti S n
                      (fun i ↦ (1 : S) ⊗ₜ[R] Pi.single (m (Fin.succAbove k i)) (1 : R))) =
                  restrictScalarsSelfOne (R := R) (S := S) ⊗ₜ[R]
                    exteriorPower.ιMulti R n
                      (fun i ↦ Pi.single (m (Fin.succAbove k i)) (1 : R))
              simpa [basisS, basisR] using
                koszul_complex_scalar_extension_component_iso_hom_apply_ιMulti
                  (R := R) (S := S) s (fun i ↦ m (Fin.succAbove k i))
          _ = termR k := by
              simp [termR]

omit [Module.Flat R S] in
/-- Helper for Lemma 15.30.5: the scalar-extension component isos commute with the Koszul
differences in adjacent degrees. This is the remaining generator-level square in the source
proof after the `Fin r → S` identification has been separated off. -/
private theorem exterior_power_fin_scalar_extension_component_iso_comm_koszulDifferential
    {r : ℕ} (s : Fin r → R) (n : ℕ) :
    (koszul_complex_scalar_extension_component_iso (R := R) (S := S) s (n + 1)).hom ≫
        ((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))).d (n + 1) n =
      (koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s)).d (n + 1) n ≫
        (koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n).hom := by
  -- Proof comment: the source proof has already reduced the chain-map check to generators, so we
  -- finish by extensionality on the transported exterior-power basis and defer only that single
  -- basis computation.
  apply ModuleCat.hom_ext
  exact Module.Basis.ext
    (exterior_power_fin_scalar_extension_basis (R := R) (S := S) (r := r) (n := n + 1))
    (fun t ↦
      exterior_power_fin_scalar_extension_differential_on_basis
        (R := R) (S := S) s n t)

/-- Helper for Lemma 15.30.5: the remaining scalar-extension comparison is the pure
scalar-extension half of the source proof, after separating off the `Fin r → S` identification. -/
private noncomputable def koszul_complex_scalar_extension_iso_extendScalars {r : ℕ}
    (s : Fin r → R) :
    koszulComplex (finite_pow_scalar_extension_linearForm (R := R) (S := S) s) ≅
      (extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s)) :=
  -- Package the verified degreewise component isos; the only remaining input is the adjacent
  -- differential square proved separately on generators.
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ koszul_complex_scalar_extension_component_iso (R := R) (S := S) s n)
    (fun i j hij ↦ by
      rcases i with _ | n1
      · cases hij
      · have hj : j = n1 := by
          simpa [ComplexShape.down] using hij
        subst j
        simpa using
          exterior_power_fin_scalar_extension_component_iso_comm_koszulDifferential
            (R := R) (S := S) s n1)

/-- Helper for Lemma 15.30.5: the bare Koszul complex on the image family is the scalar extension
of the bare Koszul complex on the source family. -/
private noncomputable def koszul_complex_image_iso_extendScalars {r : ℕ} (s : Fin r → R) :
    K^•(fun i ↦ algebraMap R S (s i)) ≅
      (extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s)) :=
  -- Route correction: first move from `Fin r → S` to the scalar-extended free module by
  -- `KoszulComplex.map`, then prove the remaining pure scalar-extension comparison separately.
  koszul_complex_image_iso_intermediate (R := R) (S := S) s ≪≫
    koszul_complex_scalar_extension_iso_extendScalars (R := R) (S := S) s

/-- Helper for Lemma 15.30.5: tensoring after scalar extension is definitionally the same as
first extending scalars and then tensoring with the base-changed coefficient module. -/
private def tensorExtendScalars_mapHomologicalComplex_obj_iso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)))
        (ComplexShape.down ℕ)).obj
      ((extendScalarsChainComplex (R := R) (S := S)).obj K)) ≅
      ((Functor.mapHomologicalComplex
          ((extendScalarsFunctor (R := R) (S := S)) ⋙
            tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)))
          (ComplexShape.down ℕ)).obj K) :=
  eqToIso rfl

/-- Helper for Lemma 15.30.5: extending scalars after tensoring is definitionally the same as
mapping the tensor-left chain complex through scalar extension. -/
private def extendScalarsTensor_mapHomologicalComplex_obj_iso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor (R := R) (S := S)))
        (ComplexShape.down ℕ)).obj K) ≅
      ((extendScalarsChainComplex (R := R) (S := S)).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
  eqToIso rfl

/-- Helper for Lemma 15.30.5: after identifying the coefficient module with its scalar extension,
tensoring a chain complex over `S` agrees with scalar extension of tensoring over `R`. -/
private noncomputable def tensor_extendScalars_reassociation_iso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)))
        (ComplexShape.down ℕ)).obj
      ((extendScalarsChainComplex (R := R) (S := S)).obj K)) ≅
      (extendScalarsChainComplex (R := R) (S := S)).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  let tensorCommIso :
      tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor (R := R) (S := S)) ≅
        (extendScalarsFunctor (R := R) (S := S)) ⋙
          tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)) :=
    extendScalarsTensorLeftNatIso (R := R) (S := S) (ModuleCat.of R M)
  let tensorCommCpxIso :
      ((Functor.mapHomologicalComplex
          ((extendScalarsFunctor (R := R) (S := S)) ⋙
            tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)))
          (ComplexShape.down ℕ)).obj K) ≅
        ((Functor.mapHomologicalComplex
          (tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor (R := R) (S := S)))
          (ComplexShape.down ℕ)).obj K) :=
    ((NatIso.mapHomologicalComplex tensorCommIso (ComplexShape.down ℕ)).app K).symm
  -- Reassociate by commuting scalar extension past tensoring before collapsing the definitional
  -- equalities on chain-complex objects.
  (tensorExtendScalars_mapHomologicalComplex_obj_iso (R := R) (S := S) (M := M) K) ≪≫
    tensorCommCpxIso ≪≫
    (extendScalarsTensor_mapHomologicalComplex_obj_iso (R := R) (S := S) (M := M) K)

/-- Helper for Lemma 15.30.5: after bare base change of the Koszul complex, tensoring with `N`
matches scalar extension of tensoring with `M`. -/
private noncomputable def tensor_koszul_complex_coeff_iso_extendScalars {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) {r : ℕ} (s : Fin r → R) :
    ((tensorLeft (ModuleCat.of S N)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s))) ≅
      (extendScalarsChainComplex (R := R) (S := S)).obj (tensor_koszul_complex R M s) :=
  let tensorLeftIso :
      tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)) ≅
        tensorLeft (ModuleCat.of S N) :=
    let tensorLeftCoeffIso :
        tensorLeft ((extendScalarsFunctor (R := R) (S := S)).obj (ModuleCat.of R M)) ≅
          tensorLeft (ModuleCat.of S (S ⊗[R] M)) :=
      (tensoringLeft (ModuleCat S)).mapIso (extendScalarsModuleIso (R := R) (S := S) M)
    tensorLeftCoeffIso ≪≫ (tensoringLeft (ModuleCat S)).mapIso (hf.equiv.toModuleIso)
  -- Replace `N` by the canonical base-changed module `S ⊗[R] M`, then commute scalar extension
  -- past tensoring using the functorial reassociation bridge above.
  (((NatIso.mapHomologicalComplex tensorLeftIso (ComplexShape.down ℕ)).app
      ((extendScalarsChainComplex (R := R) (S := S)).obj (K^•(s)))).symm) ≪≫
    (tensor_extendScalars_reassociation_iso (R := R) (S := S) (M := M) (K := K^•(s)))

/-- Helper for Lemma 15.30.5: the tensor Koszul complex on the image family is canonically the
scalar extension of the source tensor Koszul complex along a base-change map. -/
noncomputable def tensor_koszul_complex_image_iso_extendScalars {f : M →ₗ[R] N}
    (hf : IsBaseChange S f)
    {r : ℕ} (s : Fin r → R) :
    tensor_koszul_complex S N (fun i ↦ algebraMap R S (s i)) ≅
      (extendScalarsChainComplex (R := R) (S := S)).obj (tensor_koszul_complex R M s) :=
  -- First tensor the bare Koszul comparison with the target coefficients.
  (((tensorLeft (ModuleCat.of S N)).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (koszul_complex_image_iso_extendScalars (R := R) (S := S) s)) ≪≫
    -- Then compare those coefficients with scalar extension of the source coefficients.
    tensor_koszul_complex_coeff_iso_extendScalars (R := R) (S := S) (M := M) (N := N) hf s

/-- Helper for Lemma 15.30.5: vanishing of Koszul homology survives flat base change once the
source and target tensor Koszul complexes are identified. -/
theorem isZero_koszul_tensor_homology_image_of_isBaseChange {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) {r : ℕ} {s : Fin r → R} {i : ℕ}
    (hzero : IsZero ((tensor_koszul_complex R M s).homology i)) :
    IsZero ((tensor_koszul_complex S N (fun j ↦ algebraMap R S (s j))).homology i) := by
  -- First transport vanishing across flat scalar extension of the source complex.
  have hbase :
      IsZero (((extendScalarsChainComplex (R := R) (S := S)).obj
        (tensor_koszul_complex R M s)).homology i) :=
    isZero_homology_extendScalars_of_flat (R := R) (S := S) (C := tensor_koszul_complex R M s)
      (i := i) hzero
  -- Then move from scalar extension to the target image-family complex through the comparison iso.
  let e := tensor_koszul_complex_image_iso_extendScalars (R := R) (S := S) (M := M) (N := N)
    hf s
  exact IsZero.of_iso hbase (HomologicalComplex.homologyMapIso e i)

namespace IsH1RegularOn

-- Proof sketch: identify the Koszul complex on the image family `algebraMap R S ∘ f` with the
-- base change of the Koszul complex on `f` along the owner map `M →ₗ[R] N`. Since `S` is flat over
-- `R`, tensoring with `S` preserves the vanishing of first homology, so `H₁`-regularity descends
-- across any canonical base-change realization.
/-- Lemma 15.30.5 (1), owner form: `H_1`-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsH1RegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn N (fun i ↦ algebraMap R S (s i)) := by
  have hzero : IsZero ((tensor_koszul_complex R M s).homology 1) := by
    simpa [IsH1RegularOn, tensor_koszul_complex] using hreg
  -- Unfold once and apply the shared degree-one homology transport helper.
  simpa [IsH1RegularOn, tensor_koszul_complex] using
    isZero_koszul_tensor_homology_image_of_isBaseChange
      (R := R) (S := S) (M := M) (N := N) (i := 1) hf hzero

/-- Lemma 15.30.5 (1): if `s` is an `M`-`H_1`-regular sequence over `R`, then its image in `S` is
an `S ⊗[R] M`-`H_1`-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: identify `(K^•(s) ⊗ M)` after applying the owner base-change map
-- `M →ₗ[R] N` with the tensor Koszul complex over `S` on the image family `algebraMap R S ∘ s`.
-- Flatness makes homology commute with this base change, so vanishing of all positive homology
-- groups is preserved across any canonical base-change realization.
/-- Lemma 15.30.5 (2), owner form: Koszul-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsKoszulRegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn N (fun i ↦ algebraMap R S (s i)) := by
  intro i hi
  have hzero : IsZero ((tensor_koszul_complex R M s).homology i) := by
    simpa [IsKoszulRegularOn, tensor_koszul_complex] using hreg i hi
  -- Unfold once and reuse the same homology-transport lemma in every positive degree.
  simpa [IsKoszulRegularOn, tensor_koszul_complex] using
    isZero_koszul_tensor_homology_image_of_isBaseChange
      (R := R) (S := S) (M := M) (N := N) (i := i) hf hzero

/-- Lemma 15.30.5 (2): if `s` is an `M`-Koszul-regular sequence over `R`, then its image in `S`
is an `S ⊗[R] M`-Koszul-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsKoszulRegularOn

end RingTheory.Sequence
