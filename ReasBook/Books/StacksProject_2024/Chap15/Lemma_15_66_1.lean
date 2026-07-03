import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

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
