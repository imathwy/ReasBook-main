import Mathlib
import StacksProject_2024.Chap05.Lemma_5_11_5
import StacksProject_2024.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - the scheme owner for catenarity is the canonical topological-space owner `CatenarySpace S`,
--   recorded in `Chap28/Definition_28_11_1`;
-- - the open-cover and locally closed restriction companions already live in
--   `Chap05/Lemma_5_11_5`;
-- - Chapter 29's universally catenary analogue packages the affine/open-cover equivalences as a
--   `List.TFAE`, so this file keeps the source-facing numbered clauses while also exposing that
--   bundled reusable form.

variable (S : Scheme.{u})

/-- Lemma 28.11.2 (1)–(3): for a scheme `S`, catenarity is equivalent to admitting an open cover
by catenary open subschemes, to every affine-open section ring being catenary, and to admitting
an affine open cover whose section rings are catenary. -/
@[stacks 02IX]
theorem catenarySpace_tfae :
    List.TFAE
      [ CatenarySpace S,
        ∃ (ι : Type v) (U : ι → S.Opens), TopologicalSpace.IsOpenCover U ∧
          ∀ i, CatenarySpace (U i),
        ∀ U : S.affineOpens, IsCatenaryRing (Γ(S, (U : S.Opens))),
        ∃ 𝒰 : S.AffineOpenCover,
          ∀ i : 𝒰.I₀, IsCatenaryRing (Γ(S, ((𝒰.openCover.f i).opensRange))) ] := sorry

/-- Lemma 28.11.2 (1): a scheme is catenary if and only if it admits an open covering by catenary
open subschemes. -/
@[stacks 02IX]
theorem catenarySpace_iff_exists_openCover_by_catenaryOpens :
    CatenarySpace S ↔
      ∃ (ι : Type v) (U : ι → S.Opens), TopologicalSpace.IsOpenCover U ∧ ∀ i, CatenarySpace (U i) :=
  sorry

/-- Lemma 28.11.2 (2): a scheme is catenary if and only if the coordinate ring of every affine
open is catenary. -/
@[stacks 02IX]
theorem catenarySpace_iff_forall_affineOpen_isCatenaryRing :
    CatenarySpace S ↔
      ∀ U : S.affineOpens, IsCatenaryRing (Γ(S, (U : S.Opens))) := sorry

/-- Lemma 28.11.2 (3): a scheme is catenary if and only if it admits an affine open covering whose
coordinate rings are catenary. -/
@[stacks 02IX]
theorem catenarySpace_iff_exists_affineOpenCover_isCatenaryRing :
    CatenarySpace S ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsCatenaryRing (Γ(S, ((𝒰.openCover.f i).opensRange))) := sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 28.11.2 (4): any locally closed subscheme of a catenary scheme is catenary.
Formally, a locally closed subscheme is represented by an immersion `f : X ⟶ Y`. -/
@[stacks 02IX]
theorem catenarySpace_of_isImmersion [IsImmersion f] [CatenarySpace Y] :
    CatenarySpace X := sorry

end AlgebraicGeometry
