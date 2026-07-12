import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import StacksProject_2024.Chap10.Lemma_10_11_1
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap13.Lemma_13_27_3
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_66_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape DerivedCategory HomologicalComplex

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- Helper for Lemma 15.66.2: the category of `R`-modules with morphism universe pinned to the
filtered-diagram universe used in this file. -/
private abbrev SizedModuleCat (R : Type u) [Ring R] := ModuleCat.{v, u} R

private noncomputable abbrev derivedExtFunctor
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{v, u} R)) (n : ℤ) :
    ModuleCat.{v, u} R ⥤ ModuleCat (End K)ᵐᵒᵖ :=
  DerivedCategory.singleFunctor (ModuleCat.{v, u} R) (0 : ℤ) ⋙
    shiftFunctor _ n ⋙ preadditiveCoyonedaObj K

section

variable {R : Type u} [Ring R]

local notation "DModMinus" => boundedAboveDerivedCategory (SizedModuleCat R)
local notation "DMod" => DerivedCategory (SizedModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (SizedModuleCat R)

-- Source/core/bridge triage:
-- * source-facing: the filtered-colimit Ext criterion for an object of `D^-(R)`.
-- * core/canonical:
--   `PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)`.
-- * bridge/view: the canonical comparison map `colimit.post F (derivedExtToModuleFunctor K.obj n)`.
--
-- Primitive data are the degree-`n` Ext functors `derivedExtToModuleFunctor K.obj n`; the
-- comparison morphisms are derived API attached to those functors.

/-- Helper for Lemma 15.66.2: the filtered-colimit `Ext` condition from the statement, packaged
as a reusable proposition on a derived object. -/
abbrev HasFilteredColimitExtCriterionOnObj (K : DMod) (m : ℤ) : Prop :=
  (∀ n : ℤ, n < -m →
    PreservesFilteredColimits (derivedExtToModuleFunctor K n)) ∧
  ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{v, u} R),
      Mono (colimit.post F (derivedExtToModuleFunctor K (-m)))

/-- Helper for Lemma 15.66.2: the same criterion, restricted to an object of `D^-(R)`. -/
abbrev HasFilteredColimitExtCriterion (K : DModMinus) (m : ℤ) : Prop :=
  HasFilteredColimitExtCriterionOnObj (R := R) K.obj m

/-- Helper for Lemma 15.66.2: a strict degree bound `n < -m` is the same bookkeeping as the
source-proof inequality `m < -n`. -/
lemma lt_neg_of_ext_degree_bound {m n : ℤ} (hn : n < -m) : m < -n := by
  -- Proof comment: this is the arithmetic rewrite used when the source proof switches from a
  -- statement about degree `n` to the index `-n` on top homology.
  omega

/-- Helper for Lemma 15.66.2: the forward comparison theorem from Lemma `15.66.1`, restated on the
present universe-pinned module surface. -/
lemma derivedExt_filteredColimitComparison_isIso_of_isMPseudoCoherent_aux
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m n : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat.{v, u} R) (hn : n < -m) :
    IsIso (colimit.post F (derivedExtToModuleFunctor K n)) := by
  -- Proof comment: the earlier owner theorem is exactly the fixed-diagram comparison isomorphism
  -- needed here, so this local bridge is now just a universe-pinned alias.
  exact derivedExtFilteredColimitComparison_isIso_of_isMPseudoCoherent K m n hK F hn

/-- Helper for Lemma 15.66.2: the boundary-degree injectivity theorem from Lemma `15.66.1`,
restated on the present universe-pinned module surface. -/
lemma derivedExt_filteredColimitComparison_mono_at_neg_of_isMPseudoCoherent_aux
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat.{v, u} R) :
    Mono (colimit.post F (derivedExtToModuleFunctor K (-m))) := by
  -- Proof comment: the boundary-degree mono statement is already provided by the earlier owner
  -- theorem, so this local helper only repackages that exact statement on the present surface.
  exact derivedExtFilteredColimitComparison_mono_at_neg_of_isMPseudoCoherent K m hK F

/-- Helper for Lemma 15.66.2: for a fixed filtered diagram, the forward comparison isomorphism
from Lemma `15.66.1` upgrades to preservation of that specific colimit by `Ext^n_R(K,-)`. -/
lemma derivedExtFilteredColimitComparison_preservesColimit
    (K : boundedAboveDerivedCategory (ModuleCat.{v, u} R))
    (m n : ℤ) (hK : K.obj.IsMPseudoCoherent m) (hn : n < -m)
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{v, u} R)
    [HasColimit F] [HasColimit (F ⋙ derivedExtToModuleFunctor (R := R) K.obj n)] :
    PreservesColimit F (derivedExtToModuleFunctor (R := R) K.obj n) := by
  -- Route correction: pin the local `ModuleCat` universe explicitly so that the fixed-diagram
  -- comparison isomorphism matches the exact surface expected by `preservesColimit_of_isIso_post`.
  letI : IsIso (colimit.post F (derivedExtToModuleFunctor (R := R) K.obj n)) :=
    derivedExt_filteredColimitComparison_isIso_of_isMPseudoCoherent_aux
      K.obj m n hK F hn
  -- Proof comment: once the comparison map is an isomorphism, Mathlib packages the mapped cocone
  -- as a colimit cocone for this fixed filtered diagram.
  exact preservesColimit_of_isIso_post
    (F := F) (G := derivedExtToModuleFunctor (R := R) K.obj n)

/-- Helper for Lemma 15.66.2: a shape-wise family of fixed-diagram colimit-preservation
witnesses packages into the corresponding `PreservesColimitsOfShape` instance. -/
lemma preservesColimitsOfShape_of_preservesColimit_family
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : Type w} [Category.{w} J] (G : C ⥤ D)
    (h : ∀ {F : J ⥤ C}, PreservesColimit F G) :
    PreservesColimitsOfShape J G := by
  -- Proof comment: this is only structure packaging; the substantive work is already in the
  -- fixed-diagram `PreservesColimit` witnesses supplied by `h`.
  exact ⟨fun {F} ↦ h (F := F)⟩

/-- Helper for Lemma 15.66.2: the forward implication from Lemma `15.66.1` already packages as
preservation of filtered colimits on filtered shapes whose object and morphism universes agree
with the module surface used in this file. -/
lemma preservesFilteredColimitsOfSize_derivedExt_of_isMPseudoCoherent
    (K : boundedAboveDerivedCategory (ModuleCat.{v, u} R))
    (m n : ℤ) (hK : K.obj.IsMPseudoCoherent m) (hn : n < -m) :
    PreservesFilteredColimitsOfSize.{v, v}
      (derivedExtToModuleFunctor (R := R) K.obj n) := by
  refine ⟨?_⟩
  intro J _ _
  refine ⟨?_⟩
  intro F
  -- Proof comment: both the source module diagram and its image under `Ext^n(K,-)` admit the
  -- required colimits, so the fixed-diagram preservation theorem applies directly to this `F`.
  letI : HasColimit F := by infer_instance
  letI : HasColimit (F ⋙ derivedExtToModuleFunctor (R := R) K.obj n) := by infer_instance
  exact derivedExtFilteredColimitComparison_preservesColimit
    (K := K) m n hK hn F

/-- Helper for Lemma 15.66.2: if a bounded-above derived object has zero cohomology in its top
possible degree `t`, then the upper bound drops to `t - 1`. -/
lemma isLE_pred_of_isLE_of_top_homology_zero
    {X : DMod} {t : ℤ}
    (hX : X.IsLE t)
    (htop : IsZero ((H t).obj X)) :
    X.IsLE (t - 1) := by
  -- Proof comment: `IsLE (t - 1)` means vanishing of `H^i(X)` for every `i > t - 1`, i.e. for
  -- every `i ≥ t`; the new hypothesis handles `i = t`, while `hX` already controls `i > t`.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  by_cases hit : i = t
  · subst hit
    simpa using htop
  · let _ : X.IsLE t := hX
    have hti : t < i := by
      omega
    exact DerivedCategory.isZero_of_isLE X t i hti

/-- Helper for Lemma 15.66.2: the forward implication of the Ext criterion can be packaged as
preservation of filtered colimits by the derived `Ext` functor in degrees `n < -m`. -/
lemma preservesFilteredColimits_derivedExt_of_isMPseudoCoherent
    (K : boundedAboveDerivedCategory (ModuleCat.{v, u} R))
    (m n : ℤ) (hK : K.obj.IsMPseudoCoherent m) (hn : n < -m) :
    PreservesFilteredColimits (derivedExtToModuleFunctor (R := R) K.obj n) := by
  have hsmall :
      PreservesFilteredColimitsOfSize.{v, v}
        (derivedExtToModuleFunctor (R := R) K.obj n) :=
    preservesFilteredColimitsOfSize_derivedExt_of_isMPseudoCoherent
      (K := K) m n hK hn
  -- Proof comment: the remaining gap is purely owner-level universe packaging. The source-faithful
  -- fixed-diagram argument already proves preservation on `Type v`-filtered shapes, but the
  -- theorem surface `PreservesFilteredColimits` asks for the larger default size determined by
  -- the target `AddCommGrpCat` universe.
  let _ := hsmall
  sorry

/-- Helper for Lemma 15.66.2: the theorem-surface criterion immediately gives the boundary-degree
comparison map in degree `-m`. -/
lemma filteredColimitExtCriterion_boundary
    (K : DModMinus) (m : ℤ)
    (hK :
      (∀ n : ℤ, n < -m →
        PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)) ∧
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
        (F : J ⥤ ModuleCat.{v, u} R),
          Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))))
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{v, u} R) :
    Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))) :=
  hK.2 F

/-- Helper for Lemma 15.66.2: the theorem-surface criterion immediately gives filtered-colimit
preservation in any degree `n < -m`. -/
lemma filteredColimitExtCriterion_preserves_degree
    (K : DModMinus) (m n : ℤ)
    (hK :
      (∀ n' : ℤ, n' < -m →
        PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n')) ∧
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
        (F : J ⥤ ModuleCat.{v, u} R),
          Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))))
    (hn : n < -m) :
    PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n) :=
  hK.1 n hn

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
        (F : J ⥤ ModuleCat.{v, u} R),
          Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))) := by
  constructor
  · intro hK
    constructor
    · intro n hn
      -- Proof comment: the isomorphism statement from Lemma `15.66.1` is already the owner-level
      -- filtered-colimit comparison needed to package preservation.
      exact preservesFilteredColimits_derivedExt_of_isMPseudoCoherent
        (K := K) m n hK hn
    · intro J _ _ F
      -- Proof comment: the boundary-degree injectivity statement is exactly the second theorem of
      -- Lemma `15.66.1`.
      exact derivedExt_filteredColimitComparison_mono_at_neg_of_isMPseudoCoherent_aux
        K.obj m hK F
  · intro hCriterion
    have hCriterion' : HasFilteredColimitExtCriterionOnObj (R := R) K.obj m := hCriterion
    -- Proof comment: the source proof descends on an upper bound `t` for `K.obj`. The closed
    -- local observation is that the boundary comparison in degree `-m` is already part of the
    -- packaged hypothesis `hCriterion'`; the remaining gap is the genuine source-faithful core:
    -- identify `Ext^{-t}(K, -)` with `Hom(H^t(K), -)` at a top bound, deduce finiteness of
    -- `H^t(K)`, lift a finite free cover, and descend the criterion to the cone.
    let _ := hCriterion'
    -- TODO: implement the source-faithful induction on a chosen bound `t` coming from
    -- `K.property`. The first unresolved blocker is the functorial top-degree bridge
    -- `Ext^{-t}(K, -) ≅ Hom(H^t(K), -)` under `K.obj.IsLE t`; after that, the cone-descending
    -- argument from the long exact `Ext` sequence remains to be formalized.
    sorry

end

end CategoryTheory
