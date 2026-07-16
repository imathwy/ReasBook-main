import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap20.«20_25_3_2»
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex HomologicalComplex₂
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace TopCat.Presheaf

section

variable {X : TopCat.{u}} {ι : Type u}

/- Domain-style sampling for 20.25.0.1:
- primary domain: the global-sections-to-Čech comparison for bounded-below complexes of abelian
  presheaves on a topological space;
- sampled owner declarations:
  `(evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op (⊤ : Opens X))`,
  `embeddingUpNat.extendFunctor`,
  `rowCechFunctor`,
  `doubleCechFunctor`,
  `totalCechFunctor`;
- best owner abstraction: the source-facing comparison should stay at the presheaf layer, but the
  bounded-below `ℕ`-complex must first be extended canonically to an `ℤ`-indexed complex so that
  the rowwise Čech bicomplex and its total complex are expressed through the chapter owners
  `doubleCechFunctor` and `totalCechFunctor`;
- primitive data: only the space `X`, the indexed family of opens `𝒰`, and the bounded-below
  presheaf complex `ℱ`;
- derived API: the extended complex of global sections, the rowwise extended Čech bicomplex, its
  total complex, and the canonical comparison morphism.

Source/core/bridge triage:
- `source-facing`: `globalSectionsComplex`, `cechBicomplex`, `totalCechComplex`, and
  `globalSectionsToTotalCechMap`;
- `core/canonical`: the top-open evaluation functor, `embeddingUpNat.extendFunctor`, and the
  chapter owners `rowCechFunctor`, `doubleCechFunctor`, and `totalCechFunctor`;
- `bridge/view`: the degree-zero restriction map from global sections into the zero row of the
  extended Čech bicomplex.

This file therefore keeps the textbook comparison map as the main public entry, while using the
canonical `ℕ`-to-`ℤ` extension bridge and the chapter-level total Čech owners instead of trying to
totalize a raw `(up ℕ, up ℕ)` bicomplex. -/

/-- The functor of sections on the top open of `X`. -/
private abbrev topSectionsFunctor (X : TopCat.{u}) :
    X.Presheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

private instance topSectionsFunctor_preservesZeroMorphisms (X : TopCat.{u}) :
    (topSectionsFunctor X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private abbrev intExtension (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) :
    CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℤ :=
  (embeddingUpNat.extendFunctor (X.Presheaf AddCommGrpCat.{u})).obj ℱ

/-- The cochain complex of global sections of a bounded-below complex of abelian presheaves,
extended by zero to an `ℤ`-indexed cochain complex. -/
abbrev globalSectionsComplex (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  ((topSectionsFunctor X).mapHomologicalComplex (up ℤ)).obj (intExtension ℱ)

/-- The rowwise extended Čech bicomplex attached to a bounded-below complex of abelian
presheaves. -/
abbrev cechBicomplex (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ) :=
  (doubleCechFunctor 𝒰).obj (intExtension ℱ)

/-- The total Čech complex attached to a bounded-below complex of abelian presheaves and an
indexed family of opens. -/
abbrev totalCechComplex (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  (totalCechFunctor 𝒰).obj (intExtension ℱ)

/-- The intersection attached to a degree-zero Čech multi-index. -/
private abbrev cechZeroIntersection (𝒰 : ι → Opens X) (σ : Fin 1 → ι) : Opens X :=
  ∏ᶜ (𝒰 ∘ σ)

/-- The degree-zero row of the extended Čech complex is the degree-zero term of the ordinary Čech
complex. -/
private noncomputable def rowCechDegreeZeroIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) :
    ((rowCechFunctor 𝒰).obj F).X (0 : ℤ) ≅ ((cechComplexFunctor 𝒰).obj F).X 0 := by
  simpa [rowCechFunctor] using ((cechComplexFunctor 𝒰).obj F).extendXIso embeddingUpNat rfl

/-- The degree-zero Čech restriction map before identifying the extended row with the ordinary
Čech complex. -/
private noncomputable def globalSectionsToOrdinaryCechZero (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) :
    (topSectionsFunctor X).obj F ⟶ ((cechComplexFunctor 𝒰).obj F).X 0 :=
  Pi.lift fun σ : Fin 1 → ι ↦
    F.map (Opens.leTop (cechZeroIntersection 𝒰 σ)).op

/-- The degree-zero Čech restriction map on global sections of one bounded-below presheaf term. -/
private noncomputable def globalSectionsToCechZeroComponent (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (globalSectionsComplex ℱ).X (n : ℤ) ⟶ ((cechBicomplex 𝒰 ℱ).X (n : ℤ)).X (0 : ℤ) :=
  let F : X.Presheaf AddCommGrpCat.{u} := (intExtension ℱ).X (n : ℤ)
  globalSectionsToOrdinaryCechZero 𝒰 F ≫ (rowCechDegreeZeroIso 𝒰 F).inv

/-- The degree-zero row of the extended Čech complex, as a functor in the presheaf variable. -/
private abbrev rowCechZeroFunctor (𝒰 : ι → Opens X) :
    X.Presheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  rowCechFunctor 𝒰 ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) 0

/-- The canonical map from global sections on the top open to the degree-zero Čech row. -/
private noncomputable def globalSectionsToCechZeroNatTrans (𝒰 : ι → Opens X) :
    topSectionsFunctor X ⟶ rowCechZeroFunctor 𝒰 where
  app F := globalSectionsToOrdinaryCechZero 𝒰 F ≫ (rowCechDegreeZeroIso 𝒰 F).inv
  naturality _ _ _ := by
    sorry

/-- The degree-zero global-sections restriction is a Čech `0`-cocycle. -/
private theorem globalSectionsToOrdinaryCechZero_comp_d (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) :
    globalSectionsToOrdinaryCechZero 𝒰 F ≫ ((cechComplexFunctor 𝒰).obj F).d 0 1 = 0 := by
  sorry

/-- The degree-zero Čech comparison has zero vertical differential. -/
private theorem globalSectionsToCechZeroComponent_vertical (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    globalSectionsToCechZeroComponent 𝒰 ℱ n ≫ (((cechBicomplex 𝒰 ℱ).X (n : ℤ)).d 0 1) = 0 := by
  sorry

/-- Horizontal compatibility of the degree-zero Čech comparison with the presheaf-complex
differential. -/
private theorem globalSectionsToCechZeroComponent_comm (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) {i j : ℤ} (h : (up ℤ).Rel i j) :
    (globalSectionsToCechZeroNatTrans 𝒰).app ((intExtension ℱ).X i) ≫
        (((cechBicomplex 𝒰 ℱ).d i j).f (0 : ℤ)) =
      ((globalSectionsComplex ℱ).d i j) ≫
        (globalSectionsToCechZeroNatTrans 𝒰).app ((intExtension ℱ).X j) := by
  sorry

/-- The degree-`n` component of the canonical map from global sections to the total Čech complex.
-/
noncomputable def globalSectionsToTotalCechComponent (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (globalSectionsComplex ℱ).X (n : ℤ) ⟶ (totalCechComplex 𝒰 ℱ).X (n : ℤ) :=
  globalSectionsToCechZeroComponent 𝒰 ℱ n ≫
    (cechBicomplex 𝒰 ℱ).ιTotal (up ℤ) (n : ℤ) 0 (n : ℤ) (by simp)

/-- The nonnegative-degree comparison components commute with the total Čech differential. -/
private theorem globalSectionsToTotalCechComponent_comm (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    globalSectionsToTotalCechComponent 𝒰 ℱ n ≫ (totalCechComplex 𝒰 ℱ).d (n : ℤ) (n + 1 : ℤ) =
      (globalSectionsComplex ℱ).d (n : ℤ) (n + 1 : ℤ) ≫
        globalSectionsToTotalCechComponent 𝒰 ℱ (n + 1) := by
  sorry

/-- The degreewise comparison component, extended by zero to all integer degrees. -/
private noncomputable def globalSectionsToTotalCechComponentInt (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (i : ℤ) :
    (globalSectionsComplex ℱ).X i ⟶ (totalCechComplex 𝒰 ℱ).X i :=
  if hi : 0 ≤ i then
    let n : ℕ := Int.toNat i
    let hni : (n : ℤ) = i := Int.toNat_of_nonneg hi
    eqToHom (by
      simpa using congrArg (fun k ↦ (globalSectionsComplex ℱ).X k) hni.symm) ≫
      globalSectionsToTotalCechComponent 𝒰 ℱ n ≫
        eqToHom (by
          simpa using congrArg (fun k ↦ (totalCechComplex 𝒰 ℱ).X k) hni)
  else
    0

-- Proof sketch: in nonnegative degrees this is the same compatibility statement as for
-- `globalSectionsToTotalCechComponent`; in negative degrees both complexes are zero by construction
-- of the `embeddingUpNat` extension.
/-- The extended degreewise maps from global sections to the total Čech complex are compatible with
the differentials. -/
private theorem globalSectionsToTotalCechComponentInt_comm (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) {i j : ℤ} (h : (up ℤ).Rel i j) :
    globalSectionsToTotalCechComponentInt 𝒰 ℱ i ≫ (totalCechComplex 𝒰 ℱ).d i j =
      (globalSectionsComplex ℱ).d i j ≫ globalSectionsToTotalCechComponentInt 𝒰 ℱ j := by
  sorry

/-- 20.25.0.1: the canonical morphism from the complex of global sections of `ℱ^•` to the total
complex of the degreewise Čech complexes associated to the indexed family `𝒰`. -/
@[stacks 07M9]
noncomputable def globalSectionsToTotalCechMap (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) :
    globalSectionsComplex ℱ ⟶ totalCechComplex 𝒰 ℱ where
  f i := globalSectionsToTotalCechComponentInt 𝒰 ℱ i
  comm' _ _ h := globalSectionsToTotalCechComponentInt_comm 𝒰 ℱ h

-- Proof sketch: at a nonnegative degree `(n : ℤ)`, the map component is the defining degree-zero
-- Čech restriction into the `(n,0)` summand, and the `if`-branch in
-- `globalSectionsToTotalCechComponentInt` reduces by `Int.toNat_of_nonneg`.
/-- The degree-`n` component of the global-sections-to-Čech comparison map. -/
@[simp] theorem globalSectionsToTotalCechMap_f (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (globalSectionsToTotalCechMap 𝒰 ℱ).f (n : ℤ) = globalSectionsToTotalCechComponent 𝒰 ℱ n := by
  simp [globalSectionsToTotalCechMap, globalSectionsToTotalCechComponentInt,
    globalSectionsToTotalCechComponent]

end

end TopCat.Presheaf
