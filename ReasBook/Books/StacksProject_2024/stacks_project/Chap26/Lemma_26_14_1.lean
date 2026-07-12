import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

/-
Source/core/bridge triage for Lemma 26.14.1:
- `source-facing`: a locally ringed-space gluing datum together with the glued object, the chart
  maps into it, and the standard open-immersion / cover / overlap API;
- `core/canonical`: `LocallyRingedSpace.GlueData`, with constructed object and maps inherited from
  `CategoryTheory.GlueData` as `D.glued` and `D.ι i`, and companion results
  `ι_isOpenImmersion`, `ι_jointly_surjective`, and `vPullbackConeIsLimit`;
- `bridge/view`: `D.toGlueData : CategoryTheory.GlueData _`, which exposes the abstract gluing
  object/maps API (`glued`, `ι`, `vPullbackCone`) and the transport API `gluedIso` /
  `ι_gluedIso_inv` under forgetful functors.
-/

-- Semantic recall: mathlib already exposes the Stacks-style gluing construction for locally
-- ringed spaces through `LocallyRingedSpace.GlueData`, with the glued object and chart maps coming
-- from the inherited `CategoryTheory.GlueData` construction.

/- Lemma 26.14.1: a gluing datum of locally ringed spaces is the canonical owner of the gluing
construction itself. Its glued locally ringed space is `D.glued`, and the canonical chart maps are
`D.ι i : D.U i ⟶ D.glued`. The overlap pullbacks are encoded by `D.vPullbackCone i j` and
`D.vPullbackConeIsLimit i j`, inherited from the underlying categorical gluing datum `D.toGlueData`.
-/
recall LocallyRingedSpace.GlueData
recall GlueData.ι_isOpenImmersion
recall GlueData.ι_jointly_surjective
recall GlueData.vPullbackConeIsLimit
recall GlueData.toGlueData
recall CategoryTheory.GlueData.vPullbackCone
recall CategoryTheory.GlueData.gluedIso
recall CategoryTheory.GlueData.ι_gluedIso_inv

section

variable (D : GlueData.{u})

/-- Lemma 26.14.1: the canonical glued locally ringed space `D.glued` comes with open-immersion
charts `D.ι i` that jointly cover `D.glued`. The overlap pullback comparison is the canonical
owner `D.vPullbackConeIsLimit i j`. -/
@[stacks 01JB]
theorem glued_openCover :
    (∀ i, IsOpenImmersion (D.ι i)) ∧
      ∀ x : D.glued, ∃ (i : D.J) (y : D.U i), (D.ι i).base y = x := by
  exact ⟨fun i ↦ D.ι_isOpenImmersion i, D.ι_jointly_surjective⟩

end

end AlgebraicGeometry.LocallyRingedSpace
