import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap12.Lemma_12_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory
open MorphismProperty
open Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation] (Z : D)

/- Domain-style sampling:
- primary domain: localization of a pretriangulated category at a morphism property compatible with
  distinguished triangles;
- sampled owner declarations:
  `localization_object_isZero_tfae`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `CategoryTheory.Retract`,
  `binaryBiproductTriangle_distinguished`;
- best owner abstraction: the canonical localization functor `S.Q`, with primitive zero-object
  data recorded by `IsZero (S.Q.obj Z)` and the Chapter 12 owner theorem
  `localization_object_isZero_tfae`; the direct-summand clause is most canonically expressed by
  the retract owner `Retract` rather than by equality with a chosen biproduct model;
- primitive data: the morphism property `S`, the object `Z`, and the relevant localization owner
  instances;
- derived API: the triangulated and saturated refinements that add the distinguished-triangle
  formulations, best stated through the owner objects `Triangle D` and `Retract` rather than by
  primitive biproduct-coordinate data.

Source/core/bridge triage:
- `source-facing`: Lemma 13.5.9, which adds the triangulated direct-summand and distinguished-triangle
  formulations to the zero-object criterion;
- `core/canonical`: the localization owner `S.Q`, the zero-object criterion
  `localization_object_isZero_tfae`, and the saturation owner
  `MorphismProperty.IsSaturatedMultiplicativeSystem`;
- `bridge/view`: the passage between zero morphisms in `S` and distinguished triangles, expressed
  through `Triangle D`, `Retract`, and `binaryBiproductTriangle_distinguished` together with
  `S.compatible_with_triangulation`.
-/

-- Proof sketch: combine the additive-localization criterion `localization_object_isZero_tfae`
-- for clauses `(1)`–`(3)` with the pretriangulated binary-biproduct triangle
-- `binaryBiproductTriangle_distinguished`, the retract/direct-summand owner `Retract`, and the
-- compatibility axiom for `S` to pass between a zero morphism in `S` and a distinguished triangle
-- whose third object has `Z` as a direct summand and whose first morphism lies in `S`.
/-- Lemma 13.5.9: for a pretriangulated category `D`, a multiplicative system `S` compatible with
the triangulated structure, and an object `Z` of `D`, the following are equivalent: `S.Q.obj Z`
is zero; some zero morphism `0 : Z ⟶ Z'` lies in `S`; some zero morphism `0 : Z' ⟶ Z` lies in
`S`; and `Z` is a retract, hence a direct summand, of the third term of a distinguished triangle
whose first morphism lies in `S`. -/
theorem localization_object_isZero_tfae_of_compatibleWithTriangulation
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      ] := sorry

-- Proof sketch: under saturation, Lemma `4.27.21` identifies `S` with the inverse image of the
-- isomorphisms under `S.Q`; hence the maps `0 ⟶ Z` and `Z ⟶ 0` lie in `S` exactly when
-- `S.Q.obj Z` is zero. The triangle `(0, Z, Z, 0, 𝟙 Z, 0)` is distinguished, so these zero-object
-- conditions are equivalent to the existence of a distinguished triangle with third vertex `Z`
-- whose first morphism lies in `S`.
/-- If `S` is saturated, the preceding zero-object criterion is also equivalent to the canonical
zero morphisms `0 ⟶ Z` and `Z ⟶ 0` lying in `S`, and to the existence of a distinguished triangle
with third vertex exactly `Z` whose first morphism belongs to `S`. -/
theorem localization_object_isZero_tfae_of_saturated_compatibleWithTriangulation
    [IsSaturatedMultiplicativeSystem S] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      , S (0 : 0 ⟶ Z)
      , S (0 : Z ⟶ 0)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ T.obj₃ = Z
      ] := sorry

end

end CategoryTheory
