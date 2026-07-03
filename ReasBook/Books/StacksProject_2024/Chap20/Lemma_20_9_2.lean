import StacksProject_2024.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

variable {X : TopCat.{u}} (ℱ : X.Presheaf AddCommGrpCat.{max u v})

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for degree-zero Čech comparison on abelian presheaves:
- primary domain: degree-zero Čech cohomology and the unique-gluing formulation of the sheaf
  condition for `TopCat.Presheaf`;
- sampled owner declarations:
  `opensHasFiniteProducts`,
  `CategoryTheory.cechComplexFunctor`,
  `HomologicalComplex.homologyFunctor`,
  `CochainComplex.isoHomologyπ₀`,
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`;
- best owner abstraction: the canonical degree-zero Čech cohomology object
  `((cechComplexFunctor U).obj ℱ).homology 0`;
- primitive data: the family `U` of opens and the additive presheaf `ℱ`;
- derived API: the Čech augmentation into degree `0`, its induced map to `H^0`, and the
  unique-gluing bridge expressed through `TopCat.Presheaf.IsCompatible` and
  `TopCat.Presheaf.IsGluing`.

Source/core/bridge triage:
- source-facing: the degree-zero Čech comparison map and the textbook bijectivity criterion in
  Lemma 20.9.2;
- core/canonical: the owner `((cechComplexFunctor U).obj ℱ).homology 0`;
- bridge/view: the restriction map into compatible families and its comparison with the canonical
  degree-zero Čech cohomology object.
-/

-- Proof sketch: both composites from `iSup U` to `U i ⊓ U j` factor through the same restriction
-- map, so the restricted family coming from a global section is compatible.
/-- Global sections restrict to a compatible family on any open covering. -/
theorem abelianPresheaf_restriction_isCompatible {ι : Type v} (U : ι → Opens X)
    (s : ℱ.obj (op (iSup U))) :
    IsCompatible ℱ U (fun i ↦ ℱ.map (Opens.leSupr U i).op s) := sorry

/-- The canonical map from sections on `iSup U` to degree-zero Čech cohomology of the covering
`U`, viewed as the degree-`0` homology of the canonical Čech complex. -/
abbrev abelianPresheafToCechH0 {ι : Type v} (U : ι → Opens X) :
    ℱ.obj (op (iSup U)) ⟶ ((cechComplexFunctor U).obj ℱ).homology 0 :=
  let K := (cechComplexFunctor U).obj ℱ
  K.liftCycles' (cechAugmentationMap (iSup U) U ℱ rfl) 1 (by simp)
      (cechAugmentationMap_comp_d_zero_one (iSup U) U ℱ rfl) ≫
    K.homologyπ 0

-- Proof sketch: degree-zero Čech cocycles are exactly compatible local families, while
-- `CochainComplex.isoHomologyπ₀` identifies degree-zero cycles with degree-zero homology.
/-- The canonical map to degree-zero Čech cohomology is bijective exactly when compatible local
families on `U` admit unique gluings on `iSup U`. -/
theorem abelianPresheafToCechH0_bijective_iff_existsUnique_gluing {ι : Type v}
    (U : ι → Opens X) :
    Function.Bijective (abelianPresheafToCechH0 ℱ U) ↔
      ∀ sf : ∀ i : ι, ℱ.obj (op (U i)),
        IsCompatible ℱ U sf → ∃! s : ℱ.obj (op (iSup U)), IsGluing ℱ U sf s := sorry

-- Proof sketch: rewrite the sheaf condition using the owner theorem
-- `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`. The bridge theorem above identifies the
-- source unique-gluing condition for one cover with the canonical degree-zero Čech comparison.
/-- Lemma 20.9.2: an abelian presheaf on `X` is a sheaf if and only if for every open covering,
the natural map from sections on the union to the degree-zero Čech cohomology of the covering is
bijective. -/
theorem abelianPresheaf_isSheaf_iff_bijective_toCechH0 :
    ℱ.IsSheaf ↔
      ∀ ⦃ι : Type v⦄ (U : ι → Opens X),
        Function.Bijective (abelianPresheafToCechH0 ℱ U) := sorry
