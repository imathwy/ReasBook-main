import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_9_13

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 22.9.3:
- primary domain: standard mapping-cone triangles of differential graded modules and the
  two-out-of-three isomorphism theorem for their morphisms in the homotopy category;
- inspected owner declarations:
  `CategoryTheory.mappingCone_triangleh_isIso₃_of_isIso₁₂`,
  `CochainComplex.mappingCone.triangleh`,
  `HomotopyCategory.mappingCone_triangleh_distinguished`;
- best owner abstraction:
  `source-facing`: a morphism between the standard mapping-cone triangles attached to two
    morphisms of differential graded `A`-modules;
  `core/canonical`: the chapter-level owner
    `CategoryTheory.mappingCone_triangleh_isIso₃_of_isIso₁₂`;
  `bridge/view`: the specialization from arbitrary cochain complexes to differential graded
    `A`-modules, i.e. cochain complexes in `ModuleCat A`.

Primitive data are only the triangle morphism and the isomorphism assumptions on its first two
components. The conclusion that the cone component is an isomorphism is already exposed by the
canonical owner theorem, so this file should remain a recall file rather than a duplicate wrapper.
-/

/- Lemma 22.9.3: for a morphism between the standard mapping-cone triangles of two morphisms of
differential graded `A`-modules, if the first two components are isomorphisms in the homotopy
category of differential graded `A`-modules, then so is the third component. This is exactly the
canonical theorem `CategoryTheory.mappingCone_triangleh_isIso₃_of_isIso₁₂`. -/
recall CategoryTheory.mappingCone_triangleh_isIso₃_of_isIso₁₂
