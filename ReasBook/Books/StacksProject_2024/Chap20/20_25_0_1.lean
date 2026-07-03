import Mathlib
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.Chap20.«20_9_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

namespace TopCat.Sheaf

/-- The standard sign rule for totalizing `ℕ`-indexed cochain bicomplexes. -/
instance complexShapeUpNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun n : ℕ ↦ (-1 : ℤˣ) ^ n) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by
    dsimp at hpq ⊢
    lia
  add_rel p q r (hpq : p + 1 = q) := by
    dsimp at hpq ⊢
    lia
  ε'_succ := by
    rintro p q rfl
    calc
      (-1 : ℤˣ) ^ (p + 1) = (-1 : ℤˣ) ^ p * ((-1 : ℤˣ) ^ 1) := by
        simpa using (pow_add (-1 : ℤˣ) p 1)
      _ = -((-1 : ℤˣ) ^ p) := by
        simp

section

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
variable {ι : Type v}

local instance : OrderTop (Opens X) := opensOrderTop X
local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for 20.25.0.1:
- primary domain: the global-sections-to-Čech comparison for cochain complexes of abelian sheaves
  on a topological space;
- sampled owner declarations:
  `Sheaf.Γ`,
  `Sheaf.ΓRes`,
  `cechComplexFunctor`,
  `Functor.mapHomologicalComplex`,
  `HomologicalComplex₂.ιTotal`,
  `opensHasFiniteProducts`;
- best owner abstraction: the source-facing comparison map should be built from the canonical
  global sections owner `Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat`, the canonical
  restriction maps `Sheaf.ΓRes`, and the rowwise Čech functor obtained from
  `sheafToPresheaf ⋙ cechComplexFunctor 𝒰`;
- primitive data: the space `X`, the indexed family of opens `𝒰`, and the sheaf complex `ℱ`;
- derived API: the global-sections complex, the degreewise Čech bicomplex, its total complex, and
  the canonical comparison morphism.

Source/core/bridge triage:
- `source-facing`: `globalSectionsComplex`, `cechBicomplex`, `totalCechComplex`, and
  `globalSectionsToTotalCechMap`;
- `core/canonical`: `Sheaf.Γ`, `Sheaf.ΓRes`, `cechComplexFunctor`, `Functor.mapHomologicalComplex`,
  `HomologicalComplex₂.total`, and the earlier Chapter 20 owner `opensHasFiniteProducts`;
- `bridge/view`: the internal rowwise sheaf-Čech functor obtained by composing
  `sheafToPresheaf` with `cechComplexFunctor`.

The previous version duplicated the opens-product owner from `20_9_0_1` and used the
evaluation-at-`⊤` presentation of global sections as primitive data. The refined file keeps the
same mathematics but moves the construction onto the canonical owners `Sheaf.Γ` and `Sheaf.ΓRes`,
while keeping only the source-facing complex-level objects public.
-/

/-- The category of abelian sheaves on `X` is preadditive. -/
noncomputable instance sheafAddCommGrpPreadditive (X : TopCat.{u}) :
    Preadditive (X.Sheaf AddCommGrpCat.{max u v}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))

/-- The complex of global sections of an `ℕ`-indexed complex of abelian sheaves on `X`. -/
abbrev globalSectionsComplex (X : TopCat.{u})
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ℱ

private abbrev sheafCechRowFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
    CategoryTheory.cechComplexFunctor 𝒰

private instance sheafCechRowFunctor_preservesZeroMorphisms (X : TopCat.{u})
    (𝒰 : ι → Opens X) :
    (sheafCechRowFunctor X 𝒰).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext n i
    simp [sheafCechRowFunctor]

/-- The bicomplex obtained by applying the Čech construction degreewise to a complex of sheaves. -/
abbrev cechBicomplex (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{max u v} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((sheafCechRowFunctor X 𝒰).mapHomologicalComplex (ComplexShape.up ℕ)).obj ℱ

/-- The total Čech complex attached to a complex of abelian sheaves and an indexed family of opens.
-/
abbrev totalCechComplex (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (cechBicomplex X 𝒰 ℱ).total (ComplexShape.up ℕ)

/-- The intersection attached to a degree-zero Čech multi-index. -/
abbrev cechZeroIntersection (𝒰 : ι → Opens X) (σ : Fin 1 → ι) : Opens X :=
  ∏ᶜ (𝒰 ∘ σ)

/-- The degree-zero Čech restriction map on global sections of one sheaf term. -/
def globalSectionsToCechZeroComponent (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (ℱ.X n) ⟶
      ((cechBicomplex X 𝒰 ℱ).X n).X 0 :=
  Pi.lift fun σ : Fin 1 → ι ↦
    Sheaf.ΓRes (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{max u v})
      (ℱ.X n) (op (cechZeroIntersection 𝒰 σ))

/-- The degree-`n` component of the canonical map from global sections to the total Čech complex.
-/
def globalSectionsToTotalCechComponent (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (ℱ.X n) ⟶
      (totalCechComplex X 𝒰 ℱ).X n :=
  globalSectionsToCechZeroComponent X 𝒰 ℱ n ≫
    (cechBicomplex X 𝒰 ℱ).ιTotal (ComplexShape.up ℕ) n 0 n
      (show (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (n, 0) = n from
        Nat.add_zero n)

-- Proof sketch: the total differential is the sum of the horizontal differential coming from the
-- sheaf complex and the vertical differential coming from the Čech complex. The component map lands
-- in Čech degree `0`, so the vertical part is exactly the usual restriction from global sections to
-- Čech degree `1`, while the horizontal part is induced by the differential of `ℱ`. Naturality of
-- restriction with respect to the differentials of `ℱ` gives the commutative square.
/-- The degreewise maps from global sections to the total Čech complex are compatible with the
differentials. -/
theorem globalSectionsToTotalCechComponent_comm (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) {n n' : ℕ}
    (h : (ComplexShape.up ℕ).Rel n n') :
    globalSectionsToTotalCechComponent X 𝒰 ℱ n ≫ (totalCechComplex X 𝒰 ℱ).d n n' =
      (globalSectionsComplex X ℱ).d n n' ≫ globalSectionsToTotalCechComponent X 𝒰 ℱ n' := sorry

/-- 20.25.0.1: the canonical morphism from the complex of global sections of `ℱ^•` to the
total complex of the degreewise Čech complexes associated to the indexed family `𝒰`. -/
def globalSectionsToTotalCechMap (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) :
    globalSectionsComplex X ℱ ⟶ totalCechComplex X 𝒰 ℱ where
  f n := globalSectionsToTotalCechComponent X 𝒰 ℱ n
  comm' _ _ h := globalSectionsToTotalCechComponent_comm X 𝒰 ℱ h

-- Proof sketch: this is immediate from the definition of `globalSectionsToTotalCechMap`; its
-- component in degree `n` is the degree-zero Čech restriction map followed by the inclusion of the
-- `(n, 0)` summand into the total complex.
/-- The degree-`n` component of the global-sections-to-Čech comparison map. -/
theorem globalSectionsToTotalCechMap_f (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℕ) (n : ℕ) :
    (globalSectionsToTotalCechMap X 𝒰 ℱ).f n =
      globalSectionsToTotalCechComponent X 𝒰 ℱ n := sorry

end

end TopCat.Sheaf
