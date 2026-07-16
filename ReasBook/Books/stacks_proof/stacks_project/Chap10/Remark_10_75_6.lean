import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_75_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory

universe u

section

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Remark 10 75 6: `fromLeftDerivedZero'` is natural in the functor
variable for a fixed projective resolution. -/
private theorem projectiveResolution_fromLeftDerivedZero'_comp_app
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Proof comment: cancel the opcycles projection and use naturality of `α` on the augmentation.
  rw [← cancel_epi (HomologicalComplex.pOpcycles _ _)]
  have hPrefixF :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
        P.fromLeftDerivedZero' F =
      F.map (P.π.f 0) := by
    simpa using
      CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := F)
  have h₁ :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' F ≫ α.app X =
        F.map (P.π.f 0) ≫ α.app X := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ α.app X) hPrefixF
  have h₂ :
      F.map (P.π.f 0) ≫ α.app X =
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) := by
    simpa using α.naturality (P.π.f 0)
  have h₃ :
      α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
    have hPrefixG :
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' G =
        G.map (P.π.f 0) := by
      simpa using
        CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := G)
    have hOpcycles :
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 =
          α.app (P.complex.X 0) ≫
            ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 := by
      simpa using
        HomologicalComplex.p_opcyclesMap
          (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)
          (i := 0)
    have h₃a :
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
          α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) := by
      simpa [Category.assoc] using congrArg (fun k ↦ α.app (P.complex.X 0) ≫ k)
        hPrefixG.symm
    have h₃b :
        α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) =
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
            P.fromLeftDerivedZero' G := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ P.fromLeftDerivedZero' G)
        hOpcycles.symm
    exact h₃a.trans h₃b
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Chap10 Remark 10 75 6: the inverse source comparison, followed by the degree-zero
derived map and the target comparison, recovers the original natural transformation component. -/
private theorem leftDerivedZeroIsoSelf_inv_app_leftDerived_app_from
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    (α : F ⟶ G) (X : ModuleCat R) :
    F.leftDerivedZeroIsoSelf.inv.app X ≫ (NatTrans.leftDerived α 0).app X ≫
        G.fromLeftDerivedZero.app X = α.app X := by
  -- Proof comment: first prove the naturality square for the forward degree-zero comparisons.
  have hComp :
      (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
        F.fromLeftDerivedZero.app X ≫ α.app X := by
    let P : CategoryTheory.ProjectiveResolution X := CategoryTheory.projectiveResolution X
    rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq α P 0,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P G,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hIsoHomology :
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
            (ChainComplex.isoHomologyι₀
              (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom =
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 := by
      -- Proof comment: replace the homology map in degree zero by the induced opcycles map.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (ChainComplex.isoHomologyι₀
              (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                k ≫
                  (ChainComplex.isoHomologyι₀
                    (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom)
          (ChainComplex.isoHomologyι₀_inv_naturality
            (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex))
    calc
      (P.isoLeftDerivedObj F 0).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
          (ChainComplex.isoHomologyι₀
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' G =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (P.isoLeftDerivedObj F 0).hom ≫ k ≫ P.fromLeftDerivedZero' G)
                hIsoHomology
      _ =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' F ≫ α.app X := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (P.isoLeftDerivedObj F 0).hom ≫
                    (ChainComplex.isoHomologyι₀
                      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                    k)
                (projectiveResolution_fromLeftDerivedZero'_comp_app (R := R) (α := α) P).symm
  -- Proof comment: precompose with the inverse comparison to cancel the source comparison.
  calc
    F.leftDerivedZeroIsoSelf.inv.app X ≫ (NatTrans.leftDerived α 0).app X ≫
        G.fromLeftDerivedZero.app X =
      F.leftDerivedZeroIsoSelf.inv.app X ≫
        ((NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X) := by
        rfl
    _ = F.leftDerivedZeroIsoSelf.inv.app X ≫ (F.fromLeftDerivedZero.app X ≫ α.app X) := by
        rw [hComp]
    _ = α.app X := by
        simp

/-- Helper for Chap10 Remark 10 75 6: the component of `tor_flip_iso` in degree `0` is the
left-derived morphism induced by the tensor-product braiding. -/
private theorem tor_flip_iso_hom_app_app_zero (M : ModuleCat R) :
    ((tor_flip_iso (ModuleCat R) 0).app M).hom.app M =
      (NatTrans.leftDerived ((BraidedCategory.tensorLeftIsoTensorRight M).hom) 0).app M := by
  -- Proof comment: this is the component computation built into the public Tor flip.
  rfl

/-- Chap10 Remark 10 75 6: in degree `0`, the diagonal component of the symmetry from
Lemma `10.75.5` identifies, via the canonical degree-`0` comparisons with tensor product in the
two variables, with the usual tensor-product braiding on `M ⊗[R] M`. -/
theorem tor_zero_self_flip_via_tensor_braiding (M : ModuleCat R) :
    ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
        ((tor_flip_iso (ModuleCat R) 0).app M).hom.app M ≫
        (tensorRight M).fromLeftDerivedZero.app M =
      (β_ M M).hom := by
  -- Proof comment: replace the Tor flip by the derived braiding, then cancel the degree-zero
  -- comparison maps around that derived natural transformation.
  rw [tor_flip_iso_hom_app_app_zero]
  exact leftDerivedZeroIsoSelf_inv_app_leftDerived_app_from
    ((BraidedCategory.tensorLeftIsoTensorRight M).hom) M

end

section

variable {k : Type u} [Field k]

private theorem rankTwoTensor_swap_ne :
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) ≠
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) := by
  intro h
  let fst : (k × k) →ₗ[k] k := LinearMap.fst k k k
  let snd : (k × k) →ₗ[k] k := LinearMap.snd k k k
  have h' := congr_arg
    ((TensorProduct.map fst snd) :
      TensorProduct k (k × k) (k × k) →ₗ[k] TensorProduct k k k) h
  simp [fst, snd] at h'

/-- For the free rank-`2` module over a field, the diagonal symmetry on `Tor₀` is not the
identity. -/
theorem tor_zero_self_flip_not_identity_on_free_rankTwo :
    ((tensorLeft (ModuleCat.of k (k × k))).leftDerivedZeroIsoSelf.inv.app (ModuleCat.of k (k × k)))
        ≫
        ((tor_flip_iso (ModuleCat k) 0).app (ModuleCat.of k (k × k))).hom.app
          (ModuleCat.of k (k × k))
        ≫
        (tensorRight (ModuleCat.of k (k × k))).fromLeftDerivedZero.app (ModuleCat.of k (k × k)) ≠
      𝟙 ((ModuleCat.of k (k × k)) ⊗ (ModuleCat.of k (k × k))) := by
  let M : ModuleCat k := ModuleCat.of k (k × k)
  rw [tor_zero_self_flip_via_tensor_braiding M]
  intro hβ
  have hxy := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hβ)
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1))
  have hswap :
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) =
        (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) := by
    simpa [M] using hxy
  exact rankTwoTensor_swap_ne hswap.symm

/-- Consequence for Chap10 Remark 10 75 6: the canonical endomorphism of `Tor_i^R(M, M)` coming
from the symmetry of Lemma `10.75.5` is generally not the identity after the canonical degree-`0`
identifications with tensor product; this already fails in degree `0`. -/
@[stacks 00M4]
theorem tor_zero_self_flip_not_universally_identity :
    ¬ ∀ M : ModuleCat k,
      ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
          ((tor_flip_iso (ModuleCat k) 0).app M).hom.app M ≫
          (tensorRight M).fromLeftDerivedZero.app M =
        𝟙 (M ⊗ M) := by
  intro h
  exact tor_zero_self_flip_not_identity_on_free_rankTwo (h (ModuleCat.of k (k × k)))

end
