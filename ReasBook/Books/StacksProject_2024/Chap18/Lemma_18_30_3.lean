import Mathlib
import StacksProject_2024.Chap07.Definition_7_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.30.3:
- primary domain: sections functors on sheaves and sheaves of modules over a Grothendieck site,
  with quasi-compactness controlling preservation of arbitrary coproducts/direct sums;
- sampled owner declarations:
  `sheafSections`,
  `sheafSectionsNatIsoEvaluation`,
  `SheafOfModules.evaluation`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the canonical owner for sections of set-valued sheaves is
  `(sheafSections J (Type (max u v))).obj (op W)`, while the module-valued sections owner is
  `SheafOfModules.evaluation 𝒪 (op W)`, and the source-facing additive-sections functor is its
  abelian-group bridge
  `SheafOfModules.toSheaf 𝒪 ⋙ (sheafSections J AddCommGrpCat.{max u v}).obj (op W)`;
- primitive-vs-derived split:
  primitive data are only the site `(C, J)`, the quasi-compact object `W`, and the index type `ι`;
  the module-valued evaluation functor is the core owner, while the textbook `Ab`-valued sections
  functor is derived by forgetting scalars from that owner through `SheafOfModules.toSheaf 𝒪`;
- source/core/bridge triage:
  `source-facing`: preservation of coproducts/direct sums by sections over a quasi-compact object;
  `core/canonical`: `sheafSections` and `SheafOfModules.evaluation`;
  `bridge/view`: passage from module-valued sections to abelian-group-valued sections by
  `SheafOfModules.toSheaf 𝒪` and the induced sections functor. -/

-- Proof sketch: write an arbitrary coproduct of sheaves as the filtered colimit over its finite
-- subcoproducts; the transition maps are monomorphisms, so Lemma 7.17.7 identifies sections over a
-- quasi-compact object `W` with the corresponding colimit of sections.
/-- Lemma 18.30.3 (1): if `W` is quasi-compact, then taking sections over `W` defines a functor
`Sh(\mathcal{C}) \to \mathrm{Sets}` that preserves coproducts. -/
theorem quasiCompactObject_sheaf_sections_preserves_coproducts
    (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) ((sheafSections J (Type (max u v))).obj (op W)) := sorry

-- Proof sketch: apply part `(1)` to the underlying sheaves of abelian groups via
-- `SheafOfModules.toSheaf 𝒪`; this gives the source-facing additive-sections functor
-- `Mod(𝒪) ⥤ AddCommGrpCat`. The stronger module-valued statement for
-- `SheafOfModules.evaluation 𝒪 (op W)` is a companion owner-level refinement.
/-- Lemma 18.30.3 (2): if `W` is quasi-compact, then for any sheaf of rings `𝒪` the functor
`Mod(\mathcal{O}) \to \mathrm{Ab}` given by sections over `W` preserves direct sums. -/
theorem quasiCompactObject_module_sections_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf 𝒪 ⋙ (sheafSections J AddCommGrpCat.{max u v}).obj (op W)) := sorry

/-- Companion owner-level form of Lemma 18.30.3 (2): for quasi-compact `W`, the stronger
module-valued sections functor `Mod(\mathcal{O}) \to \mathrm{Mod}(\mathcal{O}(W))` also preserves
direct sums. -/
theorem quasiCompactObject_module_evaluation_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (SheafOfModules.evaluation 𝒪 (op W)) := sorry

end
