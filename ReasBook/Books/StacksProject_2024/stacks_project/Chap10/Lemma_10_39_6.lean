import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open PresheafOfModules

universe u

noncomputable section

section

variable {C : Type u} [SmallCategory C] [IsCofiltered C]

local instance : InitiallySmall.{u} C := initiallySmall_of_essentiallySmall C

/- Domain-style sampling for Lemma 10.39.6:
- primary domain: flatness for cofiltered colimits of module diagrams over a cofiltered diagram of
  commutative rings;
- sampled owner declarations:
  `flat_of_isColimit_filtered_system`,
  `PresheafOfModules.colimitFunctor`,
  `preservesColimitIso (forget₂ CommRingCat RingCat)`;
- best owner abstraction: fixed-base filtered colimits in `ModuleCat`, with
  `PresheafOfModules.colimitFunctor` as the canonical owner of the colimit module attached to a
  compatible system of modules over a ring diagram;
- primitive data: the ring diagram `R`, either a single module over `colimit R` or a presheaf of
  modules `M` over the underlying ring diagram, and the stagewise flatness hypotheses;
- derived API: clause `(1)` is the source-facing restriction-of-scalars specialization of the
  fixed-base owner theorem, while clause `(2)` is the source-facing `CommRingCat` view of the
  canonical `PresheafOfModules.colimitFunctor` module transported along the standard colimit
  comparison isomorphism;
- source/core/bridge triage:
  `source-facing`: the two flatness statements of Lemma 10.39.6 over `colimit R`;
  `core/canonical`: `flat_of_isColimit_filtered_system` and `PresheafOfModules.colimitFunctor`;
  `bridge/view`: the restriction-of-scalars passage from the ring-valued colimit
    `colimit (R ⋙ forget₂ CommRingCat RingCat)` to the source-facing ring `colimit R`. -/

-- Proof sketch: consider the constant presheaf of modules over `R` attached to the
-- `colimit R`-module `M`. Each stage is the restriction of scalars of `M` to `R.obj U`, so the
-- stagewise flatness hypothesis lets us apply the compatible-system clause below. The colimit of
-- this constant presheaf identifies with `M` because `Cᵒᵖ` is filtered, hence connected.
/-- Lemma 10.39.6 (1): if `R` is a cofiltered system of commutative rings, `A = colimit R`, and
an `A`-module is flat after restriction of scalars to every stage ring `R.obj U`, then it is flat
over `A`. -/
theorem flat_of_stagewise_restrictScalars_flat
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : ModuleCat (colimit R : CommRingCat))
    [∀ U, Module.Flat (R.obj U)
      ((ModuleCat.restrictScalars ((colimit.cocone R).ι.app U).hom).obj M)] :
    Module.Flat (colimit R : CommRingCat) M := sorry

-- Proof sketch: form the filtered diagram in
-- `ModuleCat (colimit R)` obtained from the stage modules by change of scalars along the
-- structure maps `R.obj U ⟶ colimit R`. Stagewise flatness is preserved by base change, so the
-- owner theorem `flat_of_isColimit_filtered_system` from Lemma `10.39.3` applies to this fixed
-- base-ring diagram. Its colimit is the direct owner construction
-- `PresheafOfModules.colimitFunctor`, transported along the standard comparison
-- `colimit R ≅ colimit (R ⋙ forget₂ CommRingCat RingCat)`.
/-- Lemma 10.39.6 (2): if `R` is a cofiltered system of commutative rings and `M` is a compatible
system of flat modules over `R`, then the canonical colimit module over `colimit R` is flat. This
is the categorical reformulation of the directed-system statement `M = \mathop{\mathrm{colim}}_i
M_i`. -/
theorem flat_colimitFunctor_of_stagewise_flat
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    [∀ U, Module.Flat (R.obj U) (M.obj U)] :
    Module.Flat (colimit R : CommRingCat)
      ((ModuleCat.restrictScalars
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
        ((colimitFunctor (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M)) := sorry

end
