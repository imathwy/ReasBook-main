import Mathlib
import StacksProject_2024.Chap10.Lemma_10_78_9
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open ModuleCat

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling for Lemma 15.66.3:
- primary domain: tensor-Hom comparison maps in `ModuleCat R` and their derived `Ext`
  analogues;
- sampled owner declarations:
  `TensorProduct.rTensorHomToHomRTensor`,
  `TensorProduct.rTensorHomEquivHomRTensor`,
  `CategoryTheory.Abelian.Ext.linearEquiv₀`,
  `CategoryTheory.Abelian.Ext.bilinearCompOfLinear`;
- best owner abstraction: the `Hom` comparison is owned by
  `TensorProduct.rTensorHomToHomRTensor`, while the `Ext` comparison is the derived bilinear
  postcomposition map built from `Ext.bilinearCompOfLinear`;
- primitive data: the ring `R`, the modules `M`, `N`, `L`, and the cohomological degree `i`;
- derived API: the `ModuleCat` packaging `homTensorComparisonHom`, the `Ext` comparison morphism
  `extTensorComparisonHom`, and the source-facing isomorphism theorems below;
- source/core/bridge triage:
  `source-facing`: the isomorphism statements of Lemma `15.66.3`;
  `core/canonical`: `TensorProduct.rTensorHomToHomRTensor` and `Ext.bilinearCompOfLinear`;
  `bridge/view`: the `ModuleCat` repackaging of the `Hom` comparison through
    `ModuleCat.homLinearEquiv`.
-/

/-- The degree-zero `Ext` class of the canonical map `n ↦ n ⊗ l`. -/
private noncomputable def tensorToExtZeroLinear
    (N L : ModuleCat.{u} R) :
    L →ₗ[R] Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 :=
  (((Ext.linearEquiv₀ :
      Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 ≃ₗ[R]
        (N ⟶ ModuleCat.of R (TensorProduct R N L))).symm.toLinearMap).comp
    (((homLinearEquiv :
        (N ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (N →ₗ[R] TensorProduct R N L)).symm.toLinearMap).comp
      ((TensorProduct.mk R N L).flip)))

/-- The canonical comparison map `Ext^i_R(M, N) ⊗_R L → Ext^i_R(M, N ⊗_R L)`. -/
noncomputable def extTensorComparisonHom
    (M N L : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.of R (TensorProduct R (Ext.{u} M N i) L) ⟶
      ModuleCat.of R (Ext.{u} M (ModuleCat.of R (TensorProduct R N L)) i) :=
  ModuleCat.ofHom <|
    TensorProduct.lift <|
      LinearMap.compl₂
        (Ext.bilinearCompOfLinear R M N (ModuleCat.of R (TensorProduct R N L)) i 0 i
          (add_zero i))
        (tensorToExtZeroLinear N L)

/-- The canonical comparison map `Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)`. -/
noncomputable def homTensorComparisonHom
    (M N L : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R (M ⟶ N) L) ⟶
      ModuleCat.of R (M ⟶ ModuleCat.of R (TensorProduct R N L)) :=
  ModuleCat.ofHom <|
    ((homLinearEquiv :
        (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (M →ₗ[R] TensorProduct R N L)).symm.toLinearMap) ∘ₗ
      TensorProduct.rTensorHomToHomRTensor (.id R) M N L ∘ₗ
      (LinearEquiv.rTensor L homLinearEquiv).toLinearMap

/-- The owner comparison `rTensorHomToHomRTensor` is bijective for a finitely presented module and
a flat tensor factor. -/
theorem rTensorHomToHomRTensor_bijective_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M N L) := sorry

-- Proof sketch: identify `Hom_R(M, N)` with `Ext^0_R(M, N)`, express the comparison as the
-- degree-zero instance of the `Ext`-tensor comparison, and use finite presentation of `M`
-- together with flatness of `L` to show that this comparison is an isomorphism.
/-- Lemma 15.66.3 (1): if `M` is finitely presented and `L` is flat, then the canonical map
`\operatorname{Hom}_R(M, N) \otimes_R L \to \operatorname{Hom}_R(M, N \otimes_R L)` is an
isomorphism. -/
theorem homTensorComparison_isIso_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    IsIso (homTensorComparisonHom M N L) := sorry

-- Proof sketch: choose a finite-free resolution of the `(-m)`-pseudo-coherent module `M` in the
-- relevant range, compare the Hom complexes before and after tensoring with the flat module `L`,
-- and pass to cohomology in degree `i < m`.
/-- Lemma 15.66.3 (2): if `M` is `(-m)`-pseudo-coherent and `L` is flat, then the canonical map
`\operatorname{Ext}^i_R(M, N) \otimes_R L \to \operatorname{Ext}^i_R(M, N \otimes_R L)` is an
isomorphism for `i < m`. -/
theorem extTensorComparison_isIso_of_isMPseudoCoherent
    (M N L : ModuleCat.{u} R) (m i : ℕ) [Module.Flat R L]
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (extTensorComparisonHom M N L i) := sorry

end

end CategoryTheory
