import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_28_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.28.13:
- primary domain: functoriality of the canonical base-change morphism on relative differentials;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison_unique`,
  `SheafOfModules.pullbackComp`,
  `CategoryTheory.CommSq.horiz_comp`;
- best owner abstraction:
  the source-facing base-change morphism `pullbackDifferentialsComparison`, with
  `SheafOfModules.pullbackComp` as the canonical bridge from pullback along a composite to the
  iterated pullback;
- primitive data:
  only the two composable commutative squares `hf` and `hg`;
- derived API:
  compatibility of the canonical comparison morphism with composition.

Source/core/bridge triage:
- `source-facing`: the composition law for the comparison morphisms on relative differentials;
- `core/canonical`: `pullbackDifferentialsComparison`, `pullbackDifferentialsComparison_unique`,
  and `SheafOfModules.pullbackComp`;
- `bridge/view`: `CommSq.horiz_comp` and the adjunction transposes appearing in the proof.

The local theorem `pullbackDifferentialsComparison_outer_square_commutes` was a duplicate wrapper
around `CommSq.horiz_comp`, so this file should use the owner declaration directly. -/

namespace AlgebraicGeometry.RingedSpace

variable {X X' X'' S S' S'' : RingedSpace.{u}}

/-
Proof sketch: prove that the iterated base-change morphism satisfies the same sectionwise
characterization as the canonical morphism for the pasted square, then apply the uniqueness
statement from Lemma `17.28.12`.

Lemma 17.28.13: the comparison morphism on relative differentials is compatible with composition,
so the map for the outer rectangle equals `c_g ∘ g^* c_f` after identifying `(f \circ g)^*` with
the iterated pullback.
-/
theorem pullbackDifferentialsComparison_comp
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    pullbackDifferentialsComparison (g ≫ f) (t ≫ s) h h'' (hg.horiz_comp hf) =
      ((SheafOfModules.pullbackComp
            (toRingCatSheafHom f)
            (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫
        (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg := by
  sorry

end AlgebraicGeometry.RingedSpace
