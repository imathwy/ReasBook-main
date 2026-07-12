import StacksProject_2024.Chap28.Definition_28_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall note: Definition 28.23.1 already fixes `SheafOfModules.IsKappaGenerated` as
-- the source-facing owner for cardinal-bounded generation, and local Chapter 28 precedent
-- expresses "directed colimit of subobjects" through the canonical subset of `Subobject ℱ`
-- together with its directedness and supremum `⊤`.

/-- The quasi-coherent subobjects of `ℱ` that are `κ`-generated. -/
def kappaGeneratedQuasiCoherentSubobjects
    (κ : Cardinal.{u}) (ℱ : X.Modules) : Set (Subobject ℱ) :=
  { G | ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsKappaGenerated κ }

/-- Membership in the family of quasi-coherent `κ`-generated subobjects. -/
@[simp] theorem mem_kappaGeneratedQuasiCoherentSubobjects
    (κ : Cardinal.{u}) (ℱ : X.Modules) (G : Subobject ℱ) :
    G ∈ kappaGeneratedQuasiCoherentSubobjects κ ℱ ↔
      ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsKappaGenerated κ :=
  Iff.rfl

/-- Lemma 28.23.3: for every scheme `X`, there exists a cardinal `κ` such that every
quasi-coherent `\mathcal O_X`-module is the directed colimit of its quasi-coherent
`κ`-generated submodules. In the canonical `Subobject ℱ` language, this is expressed by the
canonical family of all quasi-coherent `κ`-generated subobjects, together with its directedness
and supremum `⊤`. -/
@[stacks 077N]
theorem exists_cardinal_kappaGeneratedQuasiCoherentSubobjects_isDirectedColimit
    (X : Scheme.{u}) :
    ∃ κ : Cardinal.{u},
      ∀ (ℱ : X.Modules), ℱ.IsQuasicoherent →
        DirectedOn (· ≤ ·) (kappaGeneratedQuasiCoherentSubobjects κ ℱ) ∧
          IsLUB (kappaGeneratedQuasiCoherentSubobjects κ ℱ) (⊤ : Subobject ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
