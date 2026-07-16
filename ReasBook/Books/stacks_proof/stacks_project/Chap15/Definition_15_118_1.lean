import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Core
import Mathlib.RingTheory.PicardGroup
import stacks_proof.stacks_project.Chap04.Definition_4_43_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory TensorProduct

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/- Domain sampling:
- Primary domain: invertible modules in the symmetric monoidal category `ModuleCat R`.
- Core/canonical declarations inspected:
  - `Definition_4_43_4` / `(tensorLeft M).IsEquivalence`
  - `tensorLeft_isEquivalence_iff_exists_tensor_inverse`
  - `Module.Invertible R M`
  - `Module.Invertible.right`
  - `Module.Invertible.linearEquiv`
- Best owner abstraction: the chapter-wide invertibility owner `(tensorLeft M).IsEquivalence`,
  already fixed in Definition `4.43.4`; `Module.Invertible R M` is the specialized mathlib
  bridge for modules.
- Layer triage:
  - `source-facing`: the textbook tensor-left equivalence criterion for invertibility;
  - `core/canonical`: the chapter owner `(tensorLeft M).IsEquivalence`;
  - `bridge/view`: the theorem below identifying that owner with the specialized mathlib
    declaration `Module.Invertible R M`.
- Primitive vs. derived:
  - primitive data: the invertibility owner `(tensorLeft M).IsEquivalence`;
  - derived API: the module-specific reformulation `Module.Invertible R M`. -/

variable (M : ModuleCat R)

/- Definition 15.118.1: an `R`-module is invertible exactly when tensoring on the left by it is
an equivalence of `ModuleCat R`; this is the Chapter `4` owner specialized to modules. The
specialized mathlib predicate `Module.Invertible R M` is a companion bridge, not the main owner
of the definition. -/
#check (tensorLeft M).IsEquivalence

/-- For `R`-modules, the source-facing invertibility owner `(tensorLeft M).IsEquivalence` is
equivalent to the specialized mathlib predicate `Module.Invertible R M`. -/
theorem tensorLeft_isEquivalence_iff_moduleInvertible :
    (tensorLeft M).IsEquivalence ↔ Module.Invertible R M := by
  constructor
  · rintro hM
    rcases (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).1 hM with ⟨N, -, ⟨e⟩⟩
    exact Module.Invertible.right e.toLinearEquiv
  · intro hM
    letI : Module.Invertible R M := hM
    refine (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).2 ?_
    refine ⟨of R (Module.Dual R M), ?_, ?_⟩
    · exact ⟨(β_ M (of R (Module.Dual R M))) ≪≫ (Module.Invertible.linearEquiv R M).toModuleIso⟩
    · exact ⟨(Module.Invertible.linearEquiv R M).toModuleIso⟩

/-- The full subcategory of invertible `R`-modules, cut out by the chapter owner
`(tensorLeft M).IsEquivalence`. -/
def InvertibleSubcategory (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    ((fun N : ModuleCat R ↦ (tensorLeft N).IsEquivalence) : ObjectProperty (ModuleCat R))

instance invertibleSubcategoryCategory (R : Type u) [CommRing R] :
    Category (InvertibleSubcategory R) := by
  dsimp [InvertibleSubcategory]
  infer_instance

/-- The core groupoid of invertible `R`-modules. -/
def InvertibleCore (R : Type u) [CommRing R] : Type (u + 1) :=
  CategoryTheory.Core (InvertibleSubcategory R)

instance invertibleCoreCategory (R : Type u) [CommRing R] :
    Category (InvertibleCore R) := by
  dsimp [InvertibleCore]
  infer_instance

end ModuleCat
