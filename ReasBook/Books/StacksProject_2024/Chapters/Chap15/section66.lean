import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Module.FinitePresentation

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_66_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

private noncomputable abbrev derivedExtFunctor
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R)) (n : ℤ) :
    ModuleCat R ⥤ ModuleCat (End K)ᵐᵒᵖ :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ) ⋙ shiftFunctor _ n ⋙ preadditiveCoyonedaObj K

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.66.1:
- primary domain: fixed-degree derived `Ext` against degree-zero modules and its behavior on
  filtered colimits;
- sampled owner declarations:
  `derivedExtFunctor`,
  `preadditiveCoyonedaObj`,
  `DerivedCategory.singleFunctor`,
  `shiftFunctor`,
  `colimit.post`,
  `PreservesFilteredColimitsOfSize`;
- best owner abstraction: the primitive owner is the `ModuleCat (End K)ᵐᵒᵖ`-valued functor
  `derivedExtFunctor K n`, obtained canonically from `preadditiveCoyonedaObj K` along `single₀`
  and `shiftFunctor`; the public source-facing owners are its two thin bridges
  `derivedExtToModuleFunctor K n` and, in the commutative ring specialization below,
  `derivedExtModuleFunctor K n`. The filtered-colimit comparison is the canonical
  `colimit.post F (derivedExtToModuleFunctor K n)`, so separate public pointwise map wrappers or
  comparison-map wrappers are redundant;
- primitive vs. derived:
  primitive data are the functor `derivedExtFunctor K n` and the filtered-colimit comparison map
  for its additive-group bridge;
  derived API is the induced pointwise postcomposition map on shifted Homs, exposed through the
  functorial `.map` fields of the additive and `A`-linear bridges.

Source/core/bridge triage:
- `source-facing`: the filtered-colimit comparison and the two pseudo-coherence criteria stated in
  this file;
- `core/canonical`: `preadditiveCoyonedaObj`, `DerivedCategory.singleFunctor`, `shiftFunctor`,
  `colimit.post`, and the functorial colimit API;
- `bridge/view`: the pointwise `.map` fields induced on shifted Homs by module morphisms.
-/

/-- The functor `M ↦ Ext^n_R(K, M)` on `R`-modules, with `K` fixed in `D(R)`, obtained from the
canonical `ModuleCat (End K)ᵐᵒᵖ`-valued owner by forgetting to abelian groups. -/
noncomputable abbrev derivedExtToModuleFunctor
    (K : DMod) (n : ℤ) :
    ModuleCat R ⥤ AddCommGrpCat :=
  derivedExtFunctor K n ⋙ forget₂ _ AddCommGrpCat

-- Proof sketch: choose the bounded finite-free approximation from
-- `K.IsMPseudoCoherent m`, compare `Ext^n_R(K, -)` with `Ext^n_R(E, -)` for `n < -m`
-- and with a subfunctor of `Ext^{-m}_R(E, -)` in degree `-m`, then use that finite free terms
-- make `Hom` commute with filtered colimits and filtered colimits are exact in `ModuleCat R`.
/-- Lemma 15.66.1 (1): if `M = colim_i M_i` is a filtered colimit of `R`-modules and `K` is
`m`-pseudo-coherent in `D(R)`, then the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Ext}^n_R(K, M_i) \to \operatorname{Ext}^n_R(K, M)` is an
isomorphism for `n < -m`. -/
theorem derivedExtFilteredColimitComparison_isIso_of_isMPseudoCoherent
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DMod) (m n : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat R) (hn : n < -m) :
    IsIso (colimit.post F (derivedExtToModuleFunctor K n)) := sorry

-- Proof sketch: use the same bounded finite-free approximation of `K` and the long exact Ext
-- sequence to identify `Ext^{-m}_R(K, -)` with a subfunctor of `Ext^{-m}_R(E, -)`; the latter
-- commutes with filtered colimits because `E` is represented by a bounded finite-free complex,
-- and exactness of filtered colimits makes the comparison map monic.
/-- Lemma 15.66.1 (2): if `M = colim_i M_i` is a filtered colimit of `R`-modules and `K` is
`m`-pseudo-coherent in `D(R)`, then the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Ext}^{-m}_R(K, M_i) \to
\operatorname{Ext}^{-m}_R(K, M)` is injective. -/
theorem derivedExtFilteredColimitComparison_mono_at_neg_of_isMPseudoCoherent
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DMod) (m : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat R) :
    Mono (colimit.post F (derivedExtToModuleFunctor K (-m))) := sorry

end

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The `A`-linear Ext functor `M ↦ Ext^i_A(K, M)` on `A`-modules. This is the canonical
`ModuleCat A`-valued bridge of `derivedExtToModuleFunctor`. -/
noncomputable abbrev derivedExtModuleFunctor
    (K : DMod) (i : ℤ) :
    ModuleCat A ⥤ ModuleCat A :=
  derivedExtFunctor K i ⋙
    ModuleCat.restrictScalars (algebraMap A (End K)ᵐᵒᵖ)

end

end CategoryTheory

/-! ### Lemma_15_66_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)

-- Source/core/bridge triage:
-- * source-facing: the filtered-colimit Ext criterion for an object of `D^-(R)`.
-- * core/canonical:
--   `PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)`.
-- * bridge/view: the canonical comparison map `colimit.post F (derivedExtToModuleFunctor K.obj n)`.
--
-- Primitive data are the degree-`n` Ext functors `derivedExtToModuleFunctor K.obj n`; the
-- comparison morphisms are derived API attached to those functors.

-- Proof sketch: the forward implication combines Lemma `15.66.1` with the canonical owner
-- equivalence between preserving filtered colimits and invertibility of the filtered-colimit
-- comparison morphisms. For the converse, induct on the top nonvanishing cohomological degree of
-- `K`; use the degree `-t` injectivity criterion to show `H^t(K)` is finite via Lemma `10.11.1`,
-- kill it by a finite free module, transfer the filtered-colimit `Ext` criterion to the cone, and
-- then apply the induction hypothesis together with Lemmas `15.65.7` and `15.65.2`.
/-- Lemma 15.66.2: an object `K` of `D^-(R)` is `m`-pseudo-coherent if and only if for every
filtered diagram of `R`-modules the canonical comparison map
`\operatorname{colim}_i \operatorname{Ext}^n_R(K, M_i) \to
\operatorname{Ext}^n_R(K, \operatorname{colim}_i M_i)` is an isomorphism for `n < -m`,
equivalently the functor `Ext^n_R(K, -)` preserves filtered colimits in those degrees, and is
injective in degree `-m`. -/
theorem boundedAbove_isMPseudoCoherent_iff_filteredColimitExt
    (K : DModMinus) (m : ℤ) :
    K.obj.IsMPseudoCoherent m ↔
      (∀ n : ℤ, n < -m →
        PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)) ∧
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
        (F : J ⥤ ModuleCat R),
          Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))) := sorry

end

end CategoryTheory

/-! ### Lemma_15_66_3 (from Chap15) -/
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

/-! ### Lemma_15_66_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']

/- Domain-style sampling for Lemma 15.66.4:
- primary domain: flat base change for `Hom` and `Ext` in `ModuleCat`;
- sampled owner declarations:
  `homTensorComparisonHom`,
  `extTensorComparisonHom`,
  `moduleCatExtFlatBaseChangeAdjointComparison`,
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv`;
- best owner abstraction: this file is a `bridge/view` layer. The public source-facing maps are the
  textbook base-change comparisons, while their factors should reuse the chapter owners from
  Lemmas `15.66.3` and `10.73.1` directly;
- primitive data: the ring map `R → R'`, the modules `M`, `N`, and the degree `i`;
- derived API: the tensor-symmetry bridge identifying `N ⊗_R R'` with the owner object
  `R' ⊗_R N`, and the resulting source-facing comparison maps below.
-/

-- Proof sketch: pseudo-coherence implies `m`-pseudo-coherence for every `m`, by applying the
-- bounded-above finite-projective characterization to the degree-zero complex of the module.
/-- A pseudo-coherent module is `m`-pseudo-coherent for every integer bound `m`. -/
private theorem moduleCat_isMPseudoCoherent_of_isPseudoCoherent
    (M : ModuleCat.{u} R) (m : ℤ) (hM : M.IsPseudoCoherent) :
    M.IsMPseudoCoherent m := sorry

local notation "extScalars" => ModuleCat.extendScalars (algebraMap R R')

local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R R')

/-- The scalar-extension module `R'`, viewed as an `R`-module, agrees with `ModuleCat.of R R'`. -/
private def baseChangeRingLinearEquiv :
    ModuleCat.of R R' ≃ₗ[R] ↑((resScalars).obj (ModuleCat.of R' R')) := by
  refine
    { toFun := fun x ↦ by simpa using x
      invFun := fun x ↦ by simpa using x
      map_add' := by intro x y; rfl
      map_smul' := by
        intro r x
        have h1 : r • x = (algebraMap R R') r * x := by
          rw [Algebra.smul_def]
        have h2 :
            (RingHom.id R) r •
                (show ↑((resScalars).obj (ModuleCat.of R' R')) from x) =
              (algebraMap R R') r * x := by
          simpa using
            (ModuleCat.restrictScalars.smul_def' (algebraMap R R') r
              (show ModuleCat.of R' R' from x))
        exact h1.trans h2.symm
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }

/-- The canonical tensor-symmetry bridge from `N ⊗_R R'` to the restriction of scalars of the
owner object `R' ⊗_R N`. -/
private def tensorRightBaseChangeIso (N : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
      (resScalars).obj ((extScalars).obj N) := by
  refine LinearEquiv.toModuleIso ?_
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    ((TensorProduct.comm R N (ModuleCat.of R R')).trans
      (TensorProduct.congr baseChangeRingLinearEquiv (LinearEquiv.refl R N)))

/-- The source tensor factors `A ⊗_R R'` and `A ⊗_R ModuleCat.of R R'` are definitionally the same
`R`-module, but this equivalence gives a clean bijection for function-level composition. -/
private def tensorRightLinearEquiv (A : Type u) [AddCommMonoid A] [Module R A] :
    TensorProduct R A R' ≃ₗ[R] TensorProduct R A (ModuleCat.of R R') := by
  simpa using (LinearEquiv.refl R (TensorProduct R A R'))

/-- Postcomposition with the tensor-symmetry bridge is a bijection on `Hom`. -/
private theorem hom_postcompose_bijective_tensorRightBaseChangeIso
    (M N : ModuleCat.{u} R) :
    Function.Bijective
      (fun f : M ⟶ ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ↦
        f ≫ (tensorRightBaseChangeIso N).hom) := by
  refine ⟨?_, ?_⟩
  · intro f g h
    simpa using congrArg (fun k ↦ k ≫ (tensorRightBaseChangeIso N).inv) h
  · intro f
    exact ⟨f ≫ (tensorRightBaseChangeIso N).inv, by simp⟩

/-- Postcomposition with the tensor-symmetry bridge as an additive map on `Hom`. -/
private def homPostcomposeTensorRightBaseChangeAddHom
    (M N : ModuleCat.{u} R) :
    (M ⟶ ModuleCat.of R (TensorProduct R N (ModuleCat.of R R'))) →+
      (M ⟶ (resScalars).obj ((extScalars).obj N)) where
  toFun f := f ≫ (tensorRightBaseChangeIso N).hom
  map_zero' := by
    ext x
    simp
  map_add' _ _ := by
    ext x
    simp

/-- Postcomposition with the degree-zero `Ext` class of the tensor-symmetry bridge is a bijection
on `Ext^i`. -/
private theorem ext_postcomp_bijective_tensorRightBaseChangeIso
    (M N : ModuleCat.{u} R) (i : ℕ) :
    let e :
        ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
          (resScalars).obj ((extScalars).obj N) :=
      tensorRightBaseChangeIso N
    Function.Bijective ((Ext.mk₀ e.hom).postcomp M (add_zero i)) := by
  dsimp
  let e :
      ModuleCat.of R (TensorProduct R N (ModuleCat.of R R')) ≅
        (resScalars).obj ((extScalars).obj N) :=
    tensorRightBaseChangeIso N
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (((Ext.mk₀ e.inv).postcomp M (add_zero i))) hxy
    simpa [AddMonoidHom.comp_apply, Ext.comp_assoc_of_third_deg_zero, e] using h
  · intro x
    refine ⟨((Ext.mk₀ e.inv).postcomp M (add_zero i)) x, ?_⟩
    have h := congrArg (fun t ↦ x.comp (Ext.mk₀ t) (add_zero i)) e.inv_hom_id
    simp [e] at h ⊢

private noncomputable def homBaseChangeAdjointAddHom
    (M N : ModuleCat.{u} R) :
    (M ⟶ (resScalars).obj ((extScalars).obj N)) →+
      ((extScalars).obj M ⟶ (extScalars).obj N) where
  toFun f :=
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)).symm f
  map_zero' := by
    let e := (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)
    apply e.injective
    change e (e.symm 0) = e 0
    rw [e.apply_symm_apply]
    ext x
    rfl
  map_add' f g := by
    let e := (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
      ((extScalars).obj N)
    apply e.injective
    change e (e.symm (f + g)) = e (e.symm f + e.symm g)
    rw [e.apply_symm_apply]
    ext x
    have hf : (e.symm f) ((1 : R') ⊗ₜ[R] x) = f x := by
      exact congrArg (fun k ↦ k x) (e.apply_symm_apply f)
    have hg : (e.symm g) ((1 : R') ⊗ₜ[R] x) = g x := by
      exact congrArg (fun k ↦ k x) (e.apply_symm_apply g)
    change f x + g x =
      (e.symm f) ((1 : R') ⊗ₜ[R] x) + (e.symm g) ((1 : R') ⊗ₜ[R] x)
    rw [hf, hg]
    rfl

-- Proof sketch: take the canonical tensor comparison
-- `Hom_R(M, N) ⊗_R R' → Hom_R(M, N ⊗_R R')`, transport across the tensor-symmetry bridge to the
-- owner object `R' ⊗_R N`, and then apply the inverse of the tensor-Hom adjunction
-- `(ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv`.
/-- The textbook base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`,
expressed as the composite of the owner tensor comparison from Lemma `15.66.3`, the canonical
tensor-symmetry bridge, and the tensor-Hom adjunction from Lemma `10.14.3`, packaged as an
additive map. -/
private noncomputable def moduleCatHomTensorBaseChangeComparisonAddHom
    (M N : ModuleCat.{u} R) :
    TensorProduct R (M ⟶ N) R' →+
      ((extScalars).obj M ⟶ (extScalars).obj N) :=
  (homBaseChangeAdjointAddHom M N).comp <|
    (homPostcomposeTensorRightBaseChangeAddHom M N).comp <|
    (homTensorComparisonHom M N (ModuleCat.of R R')).hom.toAddMonoidHom.comp <|
    (tensorRightLinearEquiv (M ⟶ N)).toAddEquiv.toAddMonoidHom

private theorem moduleCatHomTensorBaseChangeComparison_map_smul
    (M N : ModuleCat.{u} R) (r : R')
    (x : TensorProduct R R' (M ⟶ N)) :
    moduleCatHomTensorBaseChangeComparisonAddHom M N
        (TensorProduct.comm R R' (M ⟶ N) (r • x)) =
      r • moduleCatHomTensorBaseChangeComparisonAddHom M N
        (TensorProduct.comm R R' (M ⟶ N) x) := sorry

/-- The canonical owner-object form
`R' ⊗_R Hom_R(M, N) → Hom_{R'}(R' ⊗_R M, R' ⊗_R N)` of the textbook base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`. -/
noncomputable def moduleCatHomTensorBaseChangeComparison
    (R' : Type u) [CommRing R'] [Algebra R R'] (M N : ModuleCat.{u} R) :
    ModuleCat.of R' (TensorProduct R R' (M ⟶ N)) ⟶
      ModuleCat.of R' (((ModuleCat.extendScalars (algebraMap R R')).obj M ⟶
        (ModuleCat.extendScalars (algebraMap R R')).obj N)) := by
  let hAdd :
      TensorProduct R (M ⟶ N) R' →+
        ((ModuleCat.extendScalars (algebraMap R R')).obj M ⟶
          (ModuleCat.extendScalars (algebraMap R R')).obj N) :=
    moduleCatHomTensorBaseChangeComparisonAddHom M N
  exact ModuleCat.ofHom
    { toFun := hAdd ∘ TensorProduct.comm R R' (M ⟶ N)
      map_add' := by
        intro x y
        simp [hAdd]
      map_smul' := by
        intro r x
        simpa [hAdd] using moduleCatHomTensorBaseChangeComparison_map_smul M N r x }

-- Proof sketch: the source-facing textbook map is the composite of the owner tensor comparison,
-- the tensor-symmetry bridge, and the inverse tensor-Hom adjunction. Under finite presentation,
-- the tensor comparison is bijective, while the other two factors are canonical equivalences.
/-- Lemma 15.66.4 (1): for a flat ring map `R → R'`, if `M` is finitely presented, then the
canonical base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective. -/
theorem moduleCat_homTensorBaseChange_bijective_of_finitePresentation
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hf : (algebraMap R R').Flat) :
    Function.Bijective (moduleCatHomTensorBaseChangeComparison R' M N) := by
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  have hTensor : Function.Bijective (homTensorComparisonHom M N (ModuleCat.of R R')).hom := by
    let f := homTensorComparisonHom M N (ModuleCat.of R R')
    letI : IsIso f := homTensorComparison_isIso_of_finitePresentation M N (ModuleCat.of R R')
    simpa using ConcreteCategory.bijective_of_isIso f
  have hAdd :
      Function.Bijective
        ((moduleCatHomTensorBaseChangeComparisonAddHom M N :
          TensorProduct R (M ⟶ N) R' → ((extScalars).obj M ⟶ (extScalars).obj N))) := by
    simpa [moduleCatHomTensorBaseChangeComparisonAddHom] using
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv M
          ((extScalars).obj N)).symm.bijective).comp
        ((hom_postcompose_bijective_tensorRightBaseChangeIso M N).comp
          (hTensor.comp (tensorRightLinearEquiv (M ⟶ N)).bijective))
  simpa [moduleCatHomTensorBaseChangeComparison, moduleCatHomTensorBaseChangeComparisonAddHom]
    using hAdd.comp (TensorProduct.comm R R' (M ⟶ N)).bijective

/-- Lemma 15.66.4 (1): for a flat ring map `R → R'`, if `M` is finitely presented, then the
canonical base-change comparison
`Hom_R(M, N) ⊗_R R' → Hom_{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism in `ModuleCat R'`. -/
theorem moduleCat_homTensorBaseChange_isIso_of_finitePresentation
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hf : (algebraMap R R').Flat) :
    IsIso (moduleCatHomTensorBaseChangeComparison R' M N) := by
  let e :=
    LinearEquiv.ofBijective
      (moduleCatHomTensorBaseChangeComparison R' M N).hom
      (moduleCat_homTensorBaseChange_bijective_of_finitePresentation M N hf)
  have he :
      e.toModuleIso.hom = moduleCatHomTensorBaseChangeComparison R' M N := by
    ext x
    rfl
  rw [← he]
  infer_instance

-- Proof sketch: compose the tensor comparison
-- `Ext^i_R(M, N) ⊗_R R' → Ext^i_R(M, N ⊗_R R')` with the adjoint flat base-change comparison
-- `Ext^i_R(M, N ⊗_R R') → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`.
/-- The textbook base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`,
expressed as the composite of the owner maps from Lemmas `15.66.3` and `10.73.1`, packaged as
an additive map. -/
private noncomputable def moduleCatExtTensorBaseChangeComparisonAddHom
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) :
    TensorProduct R (Ext.{u} M N i) R' →+
      Ext.{u} ((extScalars).obj M) ((extScalars).obj N) i :=
  (moduleCatExtFlatBaseChangeAdjointComparison
      M
      ((extScalars).obj N)
      hf
      i).comp <|
    ((Ext.mk₀ (tensorRightBaseChangeIso N).hom).postcomp M (add_zero i)).comp <|
    (extTensorComparisonHom M N (ModuleCat.of R R') i).hom.toAddMonoidHom.comp <|
    (tensorRightLinearEquiv (Ext.{u} M N i)).toAddEquiv.toAddMonoidHom

private theorem moduleCatExtTensorBaseChangeComparison_map_smul
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) (r : R')
    (x : TensorProduct R R' (Ext.{u} M N i)) :
    moduleCatExtTensorBaseChangeComparisonAddHom M N hf i
        (TensorProduct.comm R R' (Ext.{u} M N i) (r • x)) =
      r • moduleCatExtTensorBaseChangeComparisonAddHom M N hf i
        (TensorProduct.comm R R' (Ext.{u} M N i) x) := sorry

/-- The canonical owner-object form
`R' ⊗_R Ext^i_R(M, N) → Ext^i_{R'}(R' ⊗_R M, R' ⊗_R N)` of the textbook base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`. -/
noncomputable def moduleCatExtTensorBaseChangeComparison
    (M N : ModuleCat.{u} R) (hf : (algebraMap R R').Flat) (i : ℕ) :
    ModuleCat.of R' (TensorProduct R R' (Ext.{u} M N i)) ⟶
      ModuleCat.of R' (Ext.{u} ((extScalars).obj M) ((extScalars).obj N) i) :=
  ModuleCat.ofHom
    { toFun := moduleCatExtTensorBaseChangeComparisonAddHom M N hf i ∘
        TensorProduct.comm R R' (Ext.{u} M N i)
      map_add' := by
        intro x y
        let hAdd := moduleCatExtTensorBaseChangeComparisonAddHom M N hf i ∘
          TensorProduct.comm R R' (Ext.{u} M N i)
        simp
      map_smul' := by
        intro r x
        exact moduleCatExtTensorBaseChangeComparison_map_smul M N hf i r x }

-- Proof sketch: compose the tensor comparison
-- `Ext^i_R(M, N) ⊗_R R' → Ext^i_R(M, N ⊗_R R')` with the adjoint flat base-change comparison
-- `Ext^i_R(M, N ⊗_R R') → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`.
/-- Companion factorization result for Lemma 15.66.4 (2): each owner map appearing in the
construction of `moduleCatExtTensorBaseChangeComparison` is bijective. -/
private theorem moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    Function.Bijective (extTensorComparisonHom M N (ModuleCat.of R R') i).hom ∧
      Function.Bijective
        (moduleCatExtFlatBaseChangeAdjointComparison
          M
          ((extScalars).obj N)
          hf
          i) := by
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  constructor
  · let f := extTensorComparisonHom M N (ModuleCat.of R R') i
    letI : IsIso f := extTensorComparison_isIso_of_isMPseudoCoherent
      M N (ModuleCat.of R R') m i hM hi
    simpa using ConcreteCategory.bijective_of_isIso f
  · simpa using moduleCat_ext_flat_baseChange_adjoint_bijective
      M ((extScalars).obj N) hf i

-- Proof sketch: the source-facing textbook map is the composite of the two owner maps from the
-- previous theorem.
/-- Lemma 15.66.4 (2): for a flat ring map `R → R'`, if `M` is `(-m)`-pseudo-coherent, then the
canonical base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective for every `i < m`. -/
theorem moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    Function.Bijective (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  rcases
      moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
        M N m i hf hM hi with
    ⟨hTensor, hAdj⟩
  have hAdd :
      Function.Bijective (moduleCatExtTensorBaseChangeComparisonAddHom M N hf i) := by
    simpa [moduleCatExtTensorBaseChangeComparisonAddHom] using
      hAdj.comp
      ((ext_postcomp_bijective_tensorRightBaseChangeIso M N i).comp
        (hTensor.comp (tensorRightLinearEquiv (Ext.{u} M N i)).bijective))
  simpa [moduleCatExtTensorBaseChangeComparison, moduleCatExtTensorBaseChangeComparisonAddHom]
    using hAdd.comp (TensorProduct.comm R R' (Ext.{u} M N i)).bijective

/-- Lemma 15.66.4 (2): for a flat ring map `R → R'`, if `M` is `(-m)`-pseudo-coherent, then the
canonical base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism in `ModuleCat R'` for every `i < m`. -/
theorem moduleCat_extTensorBaseChange_isIso_of_isMPseudoCoherent
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R R').Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  let e :=
    LinearEquiv.ofBijective
      (moduleCatExtTensorBaseChangeComparison M N hf i).hom
      (moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent M N m i hf hM hi)
  have he :
      e.toModuleIso.hom = moduleCatExtTensorBaseChangeComparison M N hf i := by
    ext x
    rfl
  rw [← he]
  infer_instance

-- Proof sketch: over a Noetherian ring, a finite module is pseudo-coherent; then it is
-- `(-(i + 1))`-pseudo-coherent, and the previous theorem applies with `m = i + 1`.
/-- Companion factorization result for Lemma 15.66.4 (3): under the Noetherian finite hypotheses,
each owner map appearing in `moduleCatExtTensorBaseChangeComparison` is bijective in every
degree. -/
private theorem moduleCat_extTensorBaseChange_factorization_bijective_of_isNoetherianRing_of_finite
    [IsNoetherianRing R] (M N : ModuleCat.{u} R) [Module.Finite R M]
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (extTensorComparisonHom M N (ModuleCat.of R R') i).hom ∧
      Function.Bijective
        (moduleCatExtFlatBaseChangeAdjointComparison
          M
          ((extScalars).obj N)
          hf
          i) := by
  have hM : M.IsPseudoCoherent :=
    by
      have hM' : (ModuleCat.of R M).IsPseudoCoherent :=
        (Module.isPseudoCoherent_iff_finite).2 inferInstance
      simpa using hM'
  exact moduleCat_extTensorBaseChange_factorization_bijective_of_isMPseudoCoherent
    M N (i + 1) i hf
    (moduleCat_isMPseudoCoherent_of_isPseudoCoherent M (-(i + 1 : ℤ)) hM)
    (Nat.lt_succ_self i)

-- Proof sketch: combine the previous Noetherian finite reduction with part `(2)`.
/-- Lemma 15.66.4 (3): if `R` is Noetherian and `M` is finite, then for every `i` the canonical
base-change comparison
`Ext^i_R(M, N) ⊗_R R' → Ext^i_{R'}(M ⊗_R R', N ⊗_R R')`
is bijective. -/
theorem moduleCat_extTensorBaseChange_bijective_of_isNoetherianRing_of_finite
    [IsNoetherianRing R] (M N : ModuleCat.{u} R) [Module.Finite R M]
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtTensorBaseChangeComparison M N hf i) := by
  have hM : M.IsPseudoCoherent :=
    by
      have hM' : (ModuleCat.of R M).IsPseudoCoherent :=
        (Module.isPseudoCoherent_iff_finite).2 inferInstance
      simpa using hM'
  exact moduleCat_extTensorBaseChange_bijective_of_isMPseudoCoherent
    M N (i + 1) i hf
    (moduleCat_isMPseudoCoherent_of_isPseudoCoherent M (-(i + 1 : ℤ)) hM)
    (Nat.lt_succ_self i)

end

end CategoryTheory

/-! ### Lemma_15_66_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local instance (A : Type u) :
    HasProductsOfShape A (DerivedCategory (ModuleCat.{u} R)) :=
  derivedCategory_hasProductsOfShape

-- Domain-style sampling for pseudo-coherence via tensor-product/product comparison:
-- - primary domain: source-facing product-comparison maps for the functor
--   `Q ↦ Q[0] ⊗_R^L K`;
-- - inspected declarations:
--   * `ModuleCat.single0Functor`
--   * `CategoryTheory.derivedTensorProduct`
--   * `Limits.piComparison`
--   * constant-family specializations of `piComparison` already used elsewhere in Chapter 15;
-- - best owner abstraction:
--   in this module-category specialization, the canonical construction is the comparison morphism
--   `piComparison` for `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`; the
--   constant-family and free-family maps in the source are specializations of this owner.
--
-- Source/core/bridge triage:
-- - `source-facing`: the three product-comparison conditions and the TFAE statements phrased in
--   terms of those maps;
-- - `core/canonical`: `piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)`;
-- - `bridge/view`: the constant-family and `R^A` specializations of that `piComparison`.
--
-- Primitive data is the composite functor `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`;
-- the comparison maps and their homology conditions are derived API.

-- Proof sketch: represent `K` by a bounded-above termwise finite free complex, compute derived
-- tensor products by ordinary tensor products with that complex, and use Algebra,
-- Proposition `10.89.3` together with the description of products in `D(R)` to identify the
-- three product-preservation conditions.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (1): for a bounded-above derived
`R`-complex `K`, the following are equivalent: `K` is pseudo-coherent; for every family of
`R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K` is an isomorphism;
the same holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isPseudoCoherent_tfae_derivedTensorProduct_preservesProducts
    (K : D⁻((ModuleCat.{u} R))) :
    List.TFAE [
      K.obj.IsPseudoCoherent,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) fun _ : A ↦ Q),
      ∀ A : Type u,
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
          fun _ : A ↦ ModuleCat.of R R)
    ] := sorry

-- Proof sketch: the forward implications are obtained from the pseudo-coherent finite free model
-- as above. For the converse, apply the free-family criterion to the top nonvanishing cohomology
-- module, deduce finiteness from Algebra, Proposition `10.89.2`, kill that cohomology by a finite
-- free complex, and conclude by induction using Lemmas `15.65.2` and `15.65.5`.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (2): given `m ∈ ℤ` and a bounded-
above derived `R`-complex `K`, the following are equivalent: `K` is `m`-pseudo-coherent; for
every family of `R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K`
induces cohomology isomorphisms in degrees `> m` and an epimorphism in degree `m`; the same
holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isMPseudoCoherent_tfae_derivedTensorProduct_preservesProductsUpTo
    (K : D⁻((ModuleCat.{u} R))) (m : ℤ) :
    List.TFAE [
      K.obj.IsMPseudoCoherent m,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q)),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q)),
      ∀ A : Type u,
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))
    ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_66_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.66.6:
- primary domain: pseudo-coherent objects in a derived category and the degree-`i` homology map
  induced by a morphism into an object concentrated in degree `i`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the source-facing content is the existence theorem below; the canonical
  owners are pseudo-coherence, homology, and single-degree objects in `DerivedCategory`. The map
  `H^i(K) ⟶ M` induced by `α : K ⟶ M[-i]` is bridge/view data obtained directly from the owner
  comparison `singleFunctorCompHomologyFunctorIso`; the reusable bridge is exposed below as
  `DerivedCategory.homologyToSingle`, and the source-facing theorem should use that bridge rather
  than repeat the raw composite;
- primitive vs. derived:
  primitive data are `K`, `M`, and the morphism
  `α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) i).obj M`;
  derived API is the induced homology comparison `homologyToSingle i α`.
- source/core/bridge triage:
  `source-facing`: the existence theorem `exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and
    `singleFunctorCompHomologyFunctorIso`;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat R)

namespace DerivedCategory

/-- The canonical map `H^i(K) ⟶ M` induced by a morphism `K ⟶ M[-i]`, expressed via the owner
comparison `singleFunctorCompHomologyFunctorIso`. -/
abbrev homologyToSingle {K : DMod} {M : ModuleCat R} (i : ℤ)
    (α : K ⟶ (single i).obj M) : (H i).obj K ⟶ M :=
  (H i).map α ≫ ((singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom

end DerivedCategory

-- Proof sketch: choose a bounded-above termwise finite-free representative of `K` from
-- pseudo-coherence. Let `M` be the cokernel of the differential `P^(i - 1) ⟶ P^i`; finite
-- presentation follows because both terms are finite free. The canonical morphism from `K` to the
-- degree-`i` single object on `M` induces the natural map `H^i(K) ⟶ M`, and on the chosen
-- representative this map is the inclusion of cocycles modulo boundaries into the cokernel, hence
-- is monic.
/-- Lemma 15.66.6: if `K` is pseudo-coherent in `D(R)`, then for every `i : ℤ` there exists a
finitely presented `R`-module `M` and a morphism from `K` to the degree-`i` single object on `M`
(equivalently, to `M[-i]`) whose induced map `H^i(K) ⟶ M`, formalized as
`DerivedCategory.homologyToSingle i α`, is injective. -/
lemma exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    ∃ (M : ModuleCat R) (_ : Module.FinitePresentation R M) (α : K ⟶ (single i).obj M),
      Mono (homologyToSingle i α) :=
  sorry

end

end CategoryTheory

/-! ### Lemma_15_66_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Lemma 15.66.7:
- primary domain: pseudo-coherent objects in the derived category of `A`-modules, together with
  the degree-`i` homology comparison induced by a map into a single-degree object and the
  commutative-algebra control of finite quotient modules by powers of an ideal;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyToSingle`,
  `Ideal.exists_artin_rees_constant_of_exact`,
  `Submodule.annihilator_quotient`;
- best owner abstraction: the source-facing content is still the existence theorem below; the
  canonical owners are `K.IsPseudoCoherent`, the bridge morphism `DerivedCategory.homologyToSingle`
  from `15.66.6`, and the standard quotient/annihilator API used to produce an `I`-power-torsion
  finite module;
- primitive vs. derived:
  primitive data are the object `K`, the degree `i`, the ideal `I`, and the hypothesis that
  `H^i(K) / I H^i(K)` is nontrivial;
  derived API is the chosen finite `A`-module `E`, the annihilator containment `I ^ n ≤
  Module.annihilator A E`, and the morphism `α : K ⟶ E[-i]` with nonzero induced map on
  homology;
- source/core/bridge triage:
  `source-facing`: the existence theorem
    `exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and the Chapter 10
    Artin-Rees / quotient-annihilator owner API;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat A)

-- Proof sketch: apply Lemma `15.66.6` to obtain a map from `K` to a finitely presented module in
-- degree `i` whose induced map on `H^i(K)` is injective. Use Artin-Rees for the inclusion
-- `H^i(K) ⊆ M` with respect to `I` to choose `n` with `H^i(K) ∩ I ^ n M ⊆ I H^i(K)`, pass to
-- the quotient `E = M / I ^ n M`, and compose with the quotient map; the induced map on
-- `H^i(K)` remains nonzero because `H^i(K) / I H^i(K)` is nontrivial.
/-- Lemma 15.66.7: let `A` be a Noetherian ring, let `K ∈ D(A)` be pseudo-coherent, and let `I`
be an ideal of `A`. If `H^i(K) / I H^i(K)` is nontrivial, then there exists a finite `A`-module
`E` annihilated by a power of `I` and a map `K ⟶ E[-i]` whose induced map on `H^i(K)`
is nonzero, formalized as `DerivedCategory.homologyToSingle i α ≠ 0`. -/
theorem exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ)
    (hHi : Nontrivial (((H i).obj K) ⧸ (I • (⊤ : Submodule A ((H i).obj K))))) :
    ∃ (E : ModuleCat A) (_ : Module.Finite A E) (n : ℕ)
      (_ : I ^ n ≤ Module.annihilator A E) (α : K ⟶ (single i).obj E),
        homologyToSingle i α ≠ 0 :=
  sorry

end

end CategoryTheory
