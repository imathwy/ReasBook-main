import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Limits

section

variable (R : Type u) [CommRing R]

private abbrev algForget : AlgCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

private abbrev commAlgForget : CommAlgCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  forget₂ (CommAlgCat.{max u v} R) (AlgCat.{max u v} R) ⋙
    forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

namespace TensorAlgebra

/-- The category-theoretic tensor algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (TensorAlgebra R M)
  map {_ N} f :=
    AlgCat.ofHom <| TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f.hom)
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

private noncomputable def homEquiv (M : ModuleCat.{max u v} R) (A : AlgCat.{max u v} R) :
    ((functor R).obj M ⟶ A) ≃ (M ⟶ (algForget R).obj A) where
  toFun f := ModuleCat.ofHom <| f.hom.toLinearMap ∘ₗ (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M)
  invFun f := AlgCat.ofHom <| TensorAlgebra.lift R (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact TensorAlgebra.lift_comp_ι f.hom
  right_inv f := by
    apply ModuleCat.hom_ext
    exact TensorAlgebra.ι_comp_lift (show M →ₗ[R] A from f.hom)

noncomputable instance : (functor R).IsLeftAdjoint :=
  (Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply AlgCat.hom_ext
        apply TensorAlgebra.hom_ext
        ext x
        dsimp
        calc
          (TensorAlgebra.lift R ((show X →ₗ[R] Y from g.hom).comp f.hom)) (TensorAlgebra.ι R x) =
              g.hom (f.hom x) := by
                rw [TensorAlgebra.lift_ι_apply]
                rfl
          _ =
              ((TensorAlgebra.lift R (show X →ₗ[R] Y from g.hom)).comp
                (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f.hom))) (TensorAlgebra.ι R x) := by
              rw [AlgHom.comp_apply, TensorAlgebra.lift_ι_apply]
              change g.hom (f.hom x) = (TensorAlgebra.lift R (show X →ₗ[R] Y from g.hom))
                (TensorAlgebra.ι R (f.hom x))
              rw [TensorAlgebra.lift_ι_apply]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        apply ModuleCat.hom_ext
        ext x
        rfl }).isLeftAdjoint

end TensorAlgebra

namespace SymmetricAlgebra

/-- The category-theoretic symmetric algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ CommAlgCat.{max u v} R where
  obj M := CommAlgCat.of R (SymmetricAlgebra R M)
  map {_ N} f :=
    CommAlgCat.ofHom <|
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R N).comp f.hom)
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

private noncomputable def homEquiv (M : ModuleCat.{max u v} R) (A : CommAlgCat.{max u v} R) :
    ((functor R).obj M ⟶ A) ≃ (M ⟶ (commAlgForget R).obj A) where
  toFun f := ModuleCat.ofHom <| f.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M
  invFun f := CommAlgCat.ofHom <| SymmetricAlgebra.lift (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    change
      SymmetricAlgebra.lift
          (f.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M)
          ((SymmetricAlgebra.ι R M) x) =
        f.hom ((SymmetricAlgebra.ι R M) x)
    exact SymmetricAlgebra.lift_ι_apply _ x
  right_inv f := by
    apply ModuleCat.hom_ext
    exact SymmetricAlgebra.lift_comp_ι (show M →ₗ[R] A from f.hom)

private theorem homEquiv_naturality_left_aux
    {X' X : ModuleCat.{max u v} R} {Y : CommAlgCat.{max u v} R}
    (f : X' ⟶ X) (g : (functor R).obj X ⟶ Y) :
    homEquiv R X' Y ((functor R).map f ≫ g) = f ≫ homEquiv R X Y g := by
  apply ModuleCat.hom_ext
  ext x
  change
    g.hom (((functor R).map f).hom ((SymmetricAlgebra.ι R X') x)) =
      g.hom ((SymmetricAlgebra.ι R X) (f.hom x))
  rw [show ((functor R).map f).hom =
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι R X).comp f.hom) by rfl]
  exact congrArg g.hom (SymmetricAlgebra.lift_ι_apply ((SymmetricAlgebra.ι R X).comp f.hom) x)

private theorem homEquiv_naturality_right_aux
    {X : ModuleCat.{max u v} R} {Y Y' : CommAlgCat.{max u v} R}
    (g : (functor R).obj X ⟶ Y) (h : Y ⟶ Y') :
    homEquiv R X Y' (g ≫ h) =
      homEquiv R X Y g ≫ (commAlgForget R).map h := by
  apply ModuleCat.hom_ext
  ext x
  rfl

noncomputable instance : (functor R).IsLeftAdjoint :=
  (Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [Equiv.symm_apply_eq]
        calc
          f ≫ g = f ≫ (homEquiv R X Y) ((homEquiv R X Y).symm g) := by
            exact congrArg (fun k ↦ f ≫ k) ((homEquiv R X Y).apply_symm_apply g).symm
          _ = (homEquiv R X' Y) ((functor R).map f ≫ (homEquiv R X Y).symm g) := by
            symm
            exact homEquiv_naturality_left_aux R f ((homEquiv R X Y).symm g)
      homEquiv_naturality_right := by
        intro X Y Y' g h
        exact homEquiv_naturality_right_aux R g h }).isLeftAdjoint

end SymmetricAlgebra

namespace ExteriorAlgebra

/-- The category-theoretic exterior algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (ExteriorAlgebra R M)
  map {_ _} f := AlgCat.ofHom <| ExteriorAlgebra.map f.hom
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

end ExteriorAlgebra

variable {I : Type v} [Preorder I] [IsDirectedOrder I]

/-- Lemma 10.13.5 (1): the tensor algebra construction commutes with colimits of directed systems
of `R`-modules. -/
instance tensor_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (TensorAlgebra.functor R) :=
  inferInstance

/-- Lemma 10.13.5 (2): the symmetric algebra construction commutes with colimits of directed
systems of `R`-modules. -/
instance symmetric_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (SymmetricAlgebra.functor R) :=
  inferInstance

-- Proof sketch: the exterior algebra is the quotient of the tensor algebra by the alternating
-- square-zero relations, so the same reduction to Lemma `10.12.9` applies.
/-- Lemma 10.13.5 (3): the exterior algebra construction commutes with colimits of directed
systems of `R`-modules. -/
instance exterior_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (ExteriorAlgebra.functor R) where
  preservesColimit {F} := by
    sorry

end
