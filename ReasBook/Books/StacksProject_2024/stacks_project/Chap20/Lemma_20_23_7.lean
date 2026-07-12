import StacksProject_2024.Chap20.Lemma_20_9_3
import StacksProject_2024.Chap20.Lemma_20_23_4

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

variable (U : Opens X) (𝒰 : ι → Opens X)
variable (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)

/- Domain-style sampling for Lemma 20.23.7:
- primary domain: contractibility of the alternating and ordered extended Čech complexes of a
  cover;
- sampled owner declarations:
  `cechAugmentationMap`,
  `alternatingCechAugmentationMap`,
  `alternatingCechComplex`,
  `orderedCechAugmentationMap`,
  `orderedCechComplex`,
  `cechProjectionToOrderedCech`,
  `orderedCechComparison`;
- best owner abstraction: the ordinary extended Čech complex remains at the canonical owner from
  `Lemma_20_9_3`, while the alternating and ordered Čech complexes are reused directly from
  `Definition_20_23_1`, `Definition_20_23_2`, and `Lemma_20_23_4`; this file adds only the
  canonical degree-`0` augmentation maps into those existing complexes, together with the
  source-facing theorem statements about the corresponding `fromSingle₀AsComplex` constructions.

Source/core/bridge triage:
- `source-facing`: Lemma 20.23.7 (1) and (2), asserting contractibility of the alternating and
  ordered extended Čech complexes;
- `core/canonical`: `extendedCechComplex`, `alternatingCechComplex`, and `orderedCechComplex`;
- `bridge/view`: the degree-zero augmentation maps and cocycle formulas used to build the
  alternating and ordered `fromSingle₀AsComplex` constructions.

Primitive data versus derived API:
- primitive data: the open `U`, the family `𝒰`, the presheaf `F`, and the cover equality
  `hcover : U = iSup 𝒰`;
- derived API: the alternating and ordered degree-zero augmentation maps, their cocycle
  statements, and the two source-facing contractibility theorems. -/

private theorem isAlternatingCechCochain_degreeZero (s : cechTerm 𝒰 F 0) :
    IsAlternatingCechCochain 𝒰 F 0 s := by
  constructor
  · intro σ hσ
    exfalso
    apply hσ
    intro a b hab
    fin_cases a
    fin_cases b
    rfl
  · intro σ τ
    have hτ : τ = 1 := by
      ext i
      fin_cases i
      simp
    subst hτ
    simp
    rfl

/-- The degree-`0` alternating Čech augmentation induced from the ordinary Čech augmentation. -/
def alternatingCechAugmentationMap :
    F.obj (op U) ⟶ (alternatingCechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun s ↦
        ⟨(cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s),
          isAlternatingCechCochain_degreeZero 𝒰 F
            ((cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s))⟩)
      (by
        intro s t
        apply Subtype.ext
        ext σ
        change (cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover (s + t)) σ =
          ((cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s) +
            (cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover t)) σ
        rw [map_add, map_add])

/-- The alternating Čech augmentation induced from the ordinary Čech augmentation is a
degree-zero cocycle. -/
theorem alternatingCechAugmentationMap_comp_d_zero_one :
    alternatingCechAugmentationMap U 𝒰 F hcover ≫ (alternatingCechComplex 𝒰 F).d 0 1 = 0 := by
  ext s
  apply Subtype.ext
  ext σ
  change
    (((alternatingCechComplex 𝒰 F).d 0 1)
      (alternatingCechAugmentationMap U 𝒰 F hcover s)).1 σ = 0
  rw [alternatingCechComplex_d_apply]
  change
    cechDifferentialToFun 𝒰 F 0
      (alternatingCechAugmentationMap U 𝒰 F hcover s).1 σ = 0
  have haug :
      (alternatingCechAugmentationMap U 𝒰 F hcover s).1 =
        (cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s) := by
    rfl
  rw [haug, ← cechTermIso_hom_d_apply]
  have hzero := congrArg (fun g ↦ (cechTermIso 𝒰 F 1).hom (g s) σ)
    (cechAugmentationMap_comp_d_zero_one U 𝒰 F hcover)
  simpa using hzero

-- Proof sketch: compare the extended alternating Čech complex with the ordinary extended Čech
-- complex and transport the explicit contracting homotopy from the ordinary case.
/-- Lemma 20.23.7 (1): if an open cover of `U` contains `U` itself, then the extended alternating
Čech complex obtained by adjoining `F(U)` in degree `-1` is homotopy equivalent to the zero
complex. -/
@[stacks 0G6T]
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_eq
    (htrivial : ∃ i : ι, 𝒰 i = U) :
    let α :
        (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
          alternatingCechComplex 𝒰 F :=
      (CochainComplex.fromSingle₀Equiv (alternatingCechComplex 𝒰 F) (F.obj (op U))).symm
        ⟨alternatingCechAugmentationMap U 𝒰 F hcover,
          alternatingCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (0 : CochainComplex.fromSingle₀AsComplex (alternatingCechComplex 𝒰 F) (F.obj (op U)) α ⟶
        0) := by
  -- Transport the contracting homotopy from
  -- `extendedCechComplex_homotopyEquivalent_zero_of_exists_eq` to the explicit alternating
  -- degree-zero augmentation and the ordinary/alternating comparison on extended Čech complexes.
  sorry

section

variable [LinearOrder ι]

/-- The degree-`0` ordered Čech augmentation induced from the ordinary Čech augmentation. -/
def orderedCechAugmentationMap :
    F.obj (op U) ⟶ (orderedCechComplex 𝒰 F).X 0 :=
  cechAugmentationMap U 𝒰 F hcover ≫ (cechProjectionToOrderedCech 𝒰 F).f 0

/-- The ordered Čech augmentation induced from the ordinary Čech augmentation is a degree-zero
cocycle. -/
theorem orderedCechAugmentationMap_comp_d_zero_one :
    orderedCechAugmentationMap U 𝒰 F hcover ≫ (orderedCechComplex 𝒰 F).d 0 1 = 0 := by
  change cechAugmentationMap U 𝒰 F hcover ≫
      ((cechProjectionToOrderedCech 𝒰 F).f 0 ≫ (orderedCechComplex 𝒰 F).d 0 1) = 0
  rw [show (cechProjectionToOrderedCech 𝒰 F).f 0 ≫ (orderedCechComplex 𝒰 F).d 0 1 =
      (cechComplex 𝒰 F).d 0 1 ≫ (cechProjectionToOrderedCech 𝒰 F).f 1 by
      simpa using (cechProjectionToOrderedCech 𝒰 F).comm 0 1]
  simpa [cechAugmentationMap, Category.assoc] using
    congrArg (fun k ↦ k ≫ (cechProjectionToOrderedCech 𝒰 F).f 1)
      (cechAugmentationMap_comp_d_zero_one U 𝒰 F hcover)

-- Proof sketch: transport the alternating contractibility witness across the
-- ordered/alternating comparison after adjoining `F(U)` in degree `-1`.
/-- Lemma 20.23.7 (2): for any total ordering on the index set, if an open cover of `U` contains
`U` itself, then the extended ordered Čech complex obtained by adjoining `F(U)` in degree `-1` is
homotopy equivalent to the zero complex. -/
@[stacks 0G6T]
theorem extendedOrderedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (htrivial : ∃ i : ι, 𝒰 i = U) :
    let α :
        (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
          orderedCechComplex 𝒰 F :=
      (CochainComplex.fromSingle₀Equiv (orderedCechComplex 𝒰 F) (F.obj (op U))).symm
        ⟨orderedCechAugmentationMap U 𝒰 F hcover,
          orderedCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (0 : CochainComplex.fromSingle₀AsComplex (orderedCechComplex 𝒰 F) (F.obj (op U)) α ⟶ 0) := by
  -- Transport the alternating contractibility witness across the ordered/alternating comparison
  -- after adjoining `F(U)` in degree `-1`.
  sorry

end

end
