import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap04.Lemma_4_33_3
import StacksProject_2024.Chap04.Lemma_4_33_12

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.35.14:
- primary domain: fibered categories in groupoids and stability under functor composition;
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_comp`,
  `Functor.isStronglyCartesian_map_comp`,
  `Functor.IsStronglyCartesian`;
- best owner abstraction: the source-facing notion remains `IsFibredInGroupoids`, while the
  composite structure should be derived entirely from the existing owner-level composition results
  for `IsFibered` and `IsStronglyCartesian`;
- primitive data: the two input `IsFibredInGroupoids` instances on `F` and `G`;
- derived API: the induced `IsFibredInGroupoids` instance on the composite functor `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a composite of functors fibred in groupoids is
  again fibred in groupoids;
- `core/canonical`: `Functor.IsFibered` and `Functor.IsStronglyCartesian`;
- `bridge/view`: the instance below, which combines the existing composite-owner instances without
  introducing a parallel wrapper API. -/

-- Proof sketch: use Lemma 4.33.12 to obtain that `F ⋙ G` is fibred. For any morphism `φ` in `A`,
-- `φ` is strongly cartesian over `F.map φ` because `F` is fibred in groupoids, and `F.map φ` is
-- strongly cartesian over `G.map (F.map φ)` because `G` is fibred in groupoids. Lemma 4.33.3 then
-- upgrades `φ` to a strongly cartesian morphism for the composite functor `F ⋙ G`.
/-- Lemma 4.35.14: if `F : A ⥤ B` is fibred in groupoids over `B` and `G : B ⥤ C` is fibred in
groupoids over `C`, then the composite functor `F ⋙ G : A ⥤ C` is fibred in groupoids over
`C`. -/
instance isFibredInGroupoids_comp
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G] :
    IsFibredInGroupoids (F ⋙ G) where
  toIsFibered := inferInstance
  isStronglyCartesian_map := fun φ ↦ by
    letI : F.IsStronglyCartesian (F.map φ) φ := inferInstance
    letI : G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ) := inferInstance
    simpa using isStronglyCartesian_map_comp F G φ

end CategoryTheory.Functor
