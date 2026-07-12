import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import StacksProject_2024.Chap15.Lemma_15_85_5
import StacksProject_2024.Chap15.Lemma_15_85_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure
open scoped ChangeOfRings
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
  { __ := AddEquiv.refl R'
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R R' ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/- Domain-style sampling for Lemma 15.85.7:
- primary domain: two-term representatives in `D(R)` and their behavior under derived base
  change, together with the Ext-annihilation TFAE from Lemma `15.85.5`;
- sampled owner declarations in this domain:
  `IsTwoTermRepresentative`,
  `IsTwoTermRepresentative.truncGE_derivedTensorWithAlgebra`,
  `two_term_ext1_annihilated_tfae`,
  `Ideal.map`;
- best owner abstraction: the primitive source datum is still the source-facing condition
  `admits_two_term_free_representative_with_ideal_factorization K I`, but the supporting
  representative/base-change mechanism should run through the chapter owner
  `IsTwoTermRepresentative` and its scalar-extension theorem, while the three-way comparison is
  already owned by `two_term_ext1_annihilated_tfae`;
- primitive data vs. derived API: the primitive witness is a free two-term representative of `K`
  with the scalar-factorization property for `I`; the truncation target
  `(t.truncGE (-1)).obj (K ⊗[R]^L[R'])`, the mapped ideal `Ideal.map (algebraMap R R') I`, and the
  TFAE package are derived API built from those owners.

Source/core/bridge triage:
- `source-facing`: the base-changed equivalence of the three conditions from Lemma `15.85.5`,
  together with the assertion that condition `(2)` holds after base change;
- `core/canonical`: `IsTwoTermRepresentative`, its theorem
  `truncGE_derivedTensorWithAlgebra`, and the owner TFAE theorem
  `two_term_ext1_annihilated_tfae`;
- `bridge/view`: the specific free representative extracted from `hcond` and its scalar-extended
  cochain complex.

Accordingly, this file keeps the source-facing theorem but rewrites its proof entirely through the
existing owner abstractions rather than introducing a parallel local wrapper for the base-changed
representative package.
-/

-- Proof sketch: choose a two-term free representative `P` for `K` from `hcond`. Apply
-- Lemma `15.85.6` to identify the scalar-extended complex `P ⊗_R R'` with
-- `τ_{\ge -1}(K ⊗_R^L R')`. The extended complex is still supported in degrees `-1` and `0`, its
-- degree-zero term stays free after base change, and the factorization identities for elements of
-- `I` extend `R'`-linearly to every element of `Ideal.map (algebraMap R R') I`, giving condition
-- `(2)` of Lemma `15.85.5` for the base-changed object. Applying Lemma `15.85.5` to that target
-- then recovers the full three-condition package.
variable (R') in
/-- Lemma 15.85.7: if `K` satisfies condition `(2)` of Lemma `15.85.5` with respect to `(R, I)`,
then for `τ_{\ge -1}(K ⊗_R^{\mathbf L} R')` the three conditions of Lemma `15.85.5` with respect
to `(R', Ideal.map (algebraMap R R') I)` are equivalent, and condition `(2)` holds. -/
theorem truncGE_derivedTensorWithAlgebra_two_term_ext1_annihilated_tfae
    (K : DModR) (I : Ideal R)
    (hcond : admits_two_term_free_representative_with_ideal_factorization K I) :
    let K' := (t.truncGE (-1)).obj (K ⊗[R]^L[R'])
    let I' := Ideal.map (algebraMap R R') I
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K' I',
      admits_two_term_free_representative_with_ideal_factorization K' I',
      all_two_term_projective_representatives_have_ideal_factorization K' I'
    ] ∧
      admits_two_term_free_representative_with_ideal_factorization K' I' := by
  classical
  dsimp
  rcases hcond with ⟨P, hP, hfree0, hfactor⟩
  let K' := (t.truncGE (-1)).obj (K ⊗[R]^L[R'])
  let I' := Ideal.map (algebraMap R R') I
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let Pbase : CpxR' := (F.mapHomologicalComplex (up ℤ)).obj P
  have hflat0 : Module.Flat R (P.X 0) := Module.Flat.of_free
  have hPbase : IsTwoTermRepresentative K' Pbase := by
    simpa [K', Pbase, F] using
      IsTwoTermRepresentative.truncGE_derivedTensorWithAlgebra hP hflat0
  have hfree0' : Module.Free R' (Pbase.X 0) := by
    let e : (Pbase.X 0 : ModuleCat R') ≃ₗ[R'] TensorProduct R R' (P.X 0) := by
      simpa [Pbase, F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          restrictScalarsSelfEquiv
          (LinearEquiv.refl R (P.X 0)))
    exact Module.Free.of_equiv' (inferInstance : Module.Free R' (TensorProduct R R' (P.X 0)))
      e.symm
  have hfactor_gen :
      ∀ a : I,
        smulFactorsThroughDifferentialAtNegOne Pbase (algebraMap R R' (a : R)) := by
    intro a
    rcases hfactor a with ⟨g, hg⟩
    refine ⟨F.map g, ?_⟩
    change F.map (P.d (-1) 0) ≫ F.map g =
      ModuleCat.ofHom
        (LinearMap.lsmul R' ((F.obj (P.X (-1)) : ModuleCat R')) (algebraMap R R' (a : R)))
    rw [← F.map_comp, hg]
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change
      (F.map
          (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))))
        ((1 : R') ⊗ₜ[R] m) =
        (algebraMap R R' (a : R)) •
          (((1 : R') ⊗ₜ[R] m : F.obj (P.X (-1))))
    have hmap :
        (F.map
            (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))))
          ((1 : R') ⊗ₜ[R] m) =
          (((1 : R') ⊗ₜ[R] ((a : R) • m) :
            F.obj (P.X (-1)))) := by
      convert
        ModuleCat.ExtendScalars.map_tmul (algebraMap R R')
          (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))) (1 : R') m using 1
    rw [hmap]
    simpa [LinearMap.lsmul_apply] using
      (TensorProduct.tmul_smul (algebraMap R R' (a : R))
        (1 : ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')))
        m)
  have hfactor_zero :
      smulFactorsThroughDifferentialAtNegOne Pbase (0 : R') := by
    refine ⟨0, ?_⟩
    ext m
    simp
  have hfactor_add {a b : R'} :
      smulFactorsThroughDifferentialAtNegOne Pbase a →
      smulFactorsThroughDifferentialAtNegOne Pbase b →
      smulFactorsThroughDifferentialAtNegOne Pbase (a + b) := by
    rintro ⟨ga, hga⟩ ⟨gb, hgb⟩
    refine ⟨ga + gb, ?_⟩
    ext m
    simp [hga, hgb, LinearMap.lsmul_apply]
  have hfactor_smul (c : R') {a : R'} :
      smulFactorsThroughDifferentialAtNegOne Pbase a →
      smulFactorsThroughDifferentialAtNegOne Pbase (c * a) := by
    rintro ⟨g, hg⟩
    refine ⟨c • g, ?_⟩
    ext m
    have hgm :
        ModuleCat.Hom.hom g (ModuleCat.Hom.hom (Pbase.d (-1) 0) m) = a • m := by
      simpa [LinearMap.lsmul_apply] using congrArg (fun f ↦ ModuleCat.Hom.hom f m) hg
    simp [hgm, LinearMap.lsmul_apply, mul_smul]
  have hmap_generators :
      Set.range (fun a : I ↦ algebraMap R R' (a : R)) = (algebraMap R R') '' (I : Set R) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hI' :
      Ideal.span (Set.range (fun a : I ↦ algebraMap R R' (a : R))) = I' := by
    calc
      Ideal.span (Set.range (fun a : I ↦ algebraMap R R' (a : R)))
          = Ideal.span ((algebraMap R R') '' (I : Set R)) := by
            rw [hmap_generators]
      _ = Ideal.map (algebraMap R R') (Ideal.span (I : Set R)) := by
            rw [Ideal.map_span]
      _ = I' := by
            simpa [I', Ideal.span_eq]
  have hfactor' :
      ∀ a : I',
        smulFactorsThroughDifferentialAtNegOne Pbase (a : R') := by
    intro a
    have ha :
        (a : R') ∈ Ideal.span (Set.range (fun b : I ↦ algebraMap R R' (b : R))) := by
      simpa [hI'] using a.2
    refine Submodule.span_induction
      (fun x hx ↦ by
        rcases hx with ⟨b, rfl⟩
        exact hfactor_gen b)
      hfactor_zero
      (fun x y _ _ hx hy ↦ hfactor_add hx hy)
      (fun c x _ hx ↦ hfactor_smul c hx)
      ha
  have hcond' : admits_two_term_free_representative_with_ideal_factorization K' I' := by
    refine ⟨Pbase, hPbase, hfree0', hfactor'⟩
  rcases hPbase.1 with ⟨e⟩
  have hK'GE : K'.IsGE (-1) := by
    have : (DerivedCategory.Q.obj Pbase).IsGE (-1) := by
      let _ : Pbase.IsStrictlyGE (-1) := hPbase.2.1
      rw [DerivedCategory.isGE_Q_obj_iff]
      infer_instance
    exact t.isGE_of_iso e (-1)
  have hK'LE : K'.IsLE 0 := by
    have : (DerivedCategory.Q.obj Pbase).IsLE 0 := by
      let _ : Pbase.IsStrictlyLE 0 := hPbase.2.2
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    exact t.isLE_of_iso e 0
  refine ⟨?_, hcond'⟩
  simpa [K', I'] using two_term_ext1_annihilated_tfae K' I' hK'GE hK'LE

end

end CategoryTheory
