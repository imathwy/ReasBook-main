import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_35_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_36_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `AlgebraicGeometry.IsEtale` and
  `AlgebraicGeometry.Flat`.
- Local Chapter 29 precedent fixes the pointwise owners as `Scheme.Hom.EtaleAt`,
  `Scheme.Hom.flatAt`, and `Scheme.Hom.GUnramifiedAt`, and the global source-facing owner
  `GUnramified`.
- The source tag evidence is consistent: Stacks tag `02GV` is the URL tag for
  `Lemma 29.36.16`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.36.16 (1): a morphism is étale at a point if and only if it is flat
and G-unramified at that point. -/
@[stacks 02GV]
theorem etaleAt_iff_flatAt_and_gUnramifiedAt (x : X) :
    f.EtaleAt x ↔ Scheme.Hom.flatAt f x ∧ f.GUnramifiedAt x := sorry

/-- Lemma 29.36.16 (2): a morphism is étale if and only if it is flat and
G-unramified. -/
@[stacks 02GV]
theorem etale_iff_flat_and_gUnramified (f : X ⟶ S) :
    Etale f ↔ Flat f ∧ GUnramified f := sorry

end AlgebraicGeometry
