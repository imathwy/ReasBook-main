import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Presentable.Finite

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Cardinal

universe w v v' u u'

namespace CategoryTheory

attribute [local instance] fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {P : ObjectProperty C}

/- Domain-style sampling:
- Primary domain: accessible category theory and filtered-colimit extensions from a small full
  subcategory of finitely presentable objects.
- Core/canonical declarations inspected:
  - `ObjectProperty.IsCardinalFilteredGenerator`
  - `Functor.isFinitelyAccessible_iff_preservesFilteredColimits`
  - `Functor.HasLeftKanExtension`
- Best owner abstraction: the hypothesis that the source subcategory consists of categorically
  compact objects and generates `C` by filtered colimits is already packaged canonically as
  `P.IsCardinalFilteredGenerator ℵ₀`.
- Source/core/bridge triage:
  - `source-facing`: a unique strict extension `F : C ⥤ D` of `F' : P.FullSubcategory ⥤ D`
    preserving filtered colimits;
  - `core/canonical`: the filtered-generator hypothesis `P.IsCardinalFilteredGenerator ℵ₀`;
  - `bridge/view`: Kan-extension machinery is relevant for proofs, but it is not the public owner
    of this statement. -/

namespace ObjectProperty.IsCardinalFilteredGenerator

variable [ObjectProperty.Small.{w} P]

-- Proof sketch: use the filtered-colimit presentation of each object supplied by `hP` and take
-- the corresponding colimit of the `F'`-image diagram in `D` to define the extension on objects.
-- Compactness of the objects of `P.FullSubcategory` gives independence of the chosen
-- presentation and functoriality, and the same presentations force uniqueness of any
-- filtered-colimit-preserving strict extension.
/-- Lemma 4.26.2: if `P.FullSubcategory` is small, consists of categorically compact objects, and
generates `C` by filtered colimits, then every functor `F' : P.FullSubcategory ⥤ D` admits a
unique extension `F : C ⥤ D` along the inclusion `P.ι` that preserves filtered colimits. -/
theorem exists_unique_filtered_colimit_preserving_extension
    (hP : P.IsCardinalFilteredGenerator ℵ₀) [HasFilteredColimits D]
    (F' : P.FullSubcategory ⥤ D) :
    ∃! F : C ⥤ D, P.ι ⋙ F = F' ∧ PreservesFilteredColimits F := sorry

end ObjectProperty.IsCardinalFilteredGenerator

end CategoryTheory
