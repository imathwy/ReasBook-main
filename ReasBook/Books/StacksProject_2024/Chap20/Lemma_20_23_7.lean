import Mathlib
import stacks_project.Chap20.Lemma_20_23_4

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Lemma 20.23.7:
- primary domain: augmentations and extended complexes built from the alternating and ordered Čech
  complexes of a cover;
- sampled owner declarations:
  `cechAugmentationToFun`,
  `alternatingCechComplex`,
  `orderedCechComplex`,
  `orderedCechComparison`;
- best owner abstraction: the ordinary Čech augmentation remains at the canonical owner from
  `Lemma_20_9_3`, while the alternating and ordered Čech complexes are reused directly from
  `Lemma_20_23_4` and `Definition_20_23_2`; this file adds only the augmentation and
  `fromSingle₀` bridge layer.

Source/core/bridge triage:
- `source-facing`: the extended alternating and extended ordered Čech complexes of Lemma 20.23.7;
- `core/canonical`: `cechAugmentationToFun`, `alternatingCechComplex`, and `orderedCechComplex`;
- `bridge/view`: the degree-zero augmentation maps into those complexes and the resulting
  `fromSingle₀` complexes.

Primitive data versus derived API:
- primitive data: the open `U`, the family `𝒰`, the presheaf `F`, and the cover equality
  `hcover : U = iSup 𝒰`;
- derived API: the alternating and ordered augmentation maps and the extended complexes built from
  them. -/

-- Proof sketch: in degree `0` every tuple is automatically injective and every permutation of
-- `Fin 1` is trivial, so the degree-zero restriction cochain is alternating.
/-- The ordinary degree-zero Čech augmentation defines an alternating cochain. -/
theorem cechAugmentationToFun_isAlternating_zero
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s : F.obj (op U)) :
    IsAlternatingCechCochain 𝒰 F 0 (cechAugmentationToFun U 𝒰 F hcover s) := sorry

/-- The canonical augmentation from `F(U)` to degree `0` of the alternating Čech complex. -/
def alternatingCechAugmentationToFun
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) → (alternatingCechComplex 𝒰 F).X 0 :=
  fun s ↦
    ⟨cechAugmentationToFun U 𝒰 F hcover s,
      cechAugmentationToFun_isAlternating_zero U 𝒰 F hcover s⟩

-- Proof sketch: the underlying degree-zero Čech augmentation is additive, and the alternating
-- version just repackages it in the alternating subgroup.
/-- The alternating Čech augmentation is additive. -/
theorem alternatingCechAugmentationToFun_map_add
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s t : F.obj (op U)) :
    alternatingCechAugmentationToFun U 𝒰 F hcover (s + t) =
      alternatingCechAugmentationToFun U 𝒰 F hcover s +
        alternatingCechAugmentationToFun U 𝒰 F hcover t := sorry

/-- The canonical map from `F(U)` to degree `0` of the alternating Čech complex. -/
abbrev alternatingCechAugmentationMap
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ (alternatingCechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (alternatingCechAugmentationToFun U 𝒰 F hcover)
      (alternatingCechAugmentationToFun_map_add U 𝒰 F hcover))

-- Proof sketch: evaluate the alternating differential on the degree-zero restriction family and
-- observe that the two faces of every double intersection coincide with opposite signs.
/-- The alternating Čech augmentation is a degree-zero cocycle. -/
theorem alternatingCechAugmentationMap_comp_d_zero_one
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    alternatingCechAugmentationMap U 𝒰 F hcover ≫
        (alternatingCechComplex 𝒰 F).d 0 1 =
      0 := sorry

/-- The augmentation from `F(U)` to the alternating Čech complex viewed as a map from a single-term
complex in degree `0`. -/
abbrev alternatingExtendedCechComplexAugmentation
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
      alternatingCechComplex 𝒰 F :=
  (CochainComplex.fromSingle₀Equiv (alternatingCechComplex 𝒰 F) (F.obj (op U))).symm
    ⟨alternatingCechAugmentationMap U 𝒰 F hcover,
      alternatingCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended alternating Čech complex obtained by placing `F(U)` in degree `-1`. -/
def alternatingExtendedCechComplex
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (alternatingCechComplex 𝒰 F) (F.obj (op U))
    (alternatingExtendedCechComplexAugmentation U 𝒰 F hcover)

-- Proof sketch: compare the extended alternating Čech complex with the ordinary extended Čech
-- complex and transport the explicit contracting homotopy from the ordinary case.
/-- Lemma 20.23.7 (1): if an open cover of `U` contains `U` itself, then the extended alternating
Čech complex obtained by adjoining `F(U)` in degree `-1` is homotopy equivalent to the zero
complex. -/
theorem alternatingExtendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty
      (HomotopyEquiv (alternatingExtendedCechComplex U 𝒰 F hcover)
        ((CochainComplex.single₀ AddCommGrpCat.{max u v}).obj
          (⊥_ AddCommGrpCat.{max u v}))) := sorry

section Ordered

variable [LinearOrder ι]

/-- The canonical augmentation from `F(U)` to degree `0` of the ordered Čech complex. -/
def orderedCechAugmentationToFun
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) → (orderedCechComplex 𝒰 F).X 0 :=
  fun s σ ↦
    F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ.1)).op s

-- Proof sketch: each ordered degree-zero component is a restriction morphism from `F(U)`, hence
-- the augmentation is additive componentwise.
/-- The ordered Čech augmentation is additive. -/
theorem orderedCechAugmentationToFun_map_add
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s t : F.obj (op U)) :
    orderedCechAugmentationToFun U 𝒰 F hcover (s + t) =
      orderedCechAugmentationToFun U 𝒰 F hcover s +
        orderedCechAugmentationToFun U 𝒰 F hcover t := sorry

/-- The canonical map from `F(U)` to degree `0` of the ordered Čech complex. -/
abbrev orderedCechAugmentationMap
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ (orderedCechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (orderedCechAugmentationToFun U 𝒰 F hcover)
      (orderedCechAugmentationToFun_map_add U 𝒰 F hcover))

-- Proof sketch: the ordered degree-one differential is the alternating sum of the two
-- restrictions to double intersections, and those two terms are equal with opposite signs.
/-- The ordered Čech augmentation is a degree-zero cocycle. -/
theorem orderedCechAugmentationMap_comp_d_zero_one
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    orderedCechAugmentationMap U 𝒰 F hcover ≫ (orderedCechComplex 𝒰 F).d 0 1 = 0 := sorry

/-- The augmentation from `F(U)` to the ordered Čech complex viewed as a map from a single-term
complex in degree `0`. -/
abbrev orderedExtendedCechComplexAugmentation
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
      orderedCechComplex 𝒰 F :=
  (CochainComplex.fromSingle₀Equiv (orderedCechComplex 𝒰 F) (F.obj (op U))).symm
    ⟨orderedCechAugmentationMap U 𝒰 F hcover,
      orderedCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended ordered Čech complex obtained by placing `F(U)` in degree `-1`. -/
def orderedExtendedCechComplex
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (orderedCechComplex 𝒰 F) (F.obj (op U))
    (orderedExtendedCechComplexAugmentation U 𝒰 F hcover)

-- Proof sketch: insert the distinguished index with `U_i = U` into every ordered multi-index to
-- obtain the standard contracting homotopy described in the textbook.
/-- Lemma 20.23.7 (2): for any total ordering on the index set, if an open cover of `U` contains
`U` itself, then the extended ordered Čech complex obtained by adjoining `F(U)` in degree `-1` is
homotopy equivalent to the zero complex. -/
theorem orderedExtendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty
      (HomotopyEquiv (orderedExtendedCechComplex U 𝒰 F hcover)
        ((CochainComplex.single₀ AddCommGrpCat.{max u v}).obj
          (⊥_ AddCommGrpCat.{max u v}))) := sorry

end Ordered

end
