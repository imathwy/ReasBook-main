import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksProject_2024.Chap18.Definition_18_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Domain-style sampling for Lemma 18.14.2:
- primary domain: categorical completeness, cocompleteness, and Grothendieck-axiom structure for
  sheaves of modules on a ringed site;
- inspected owner declarations:
  `Mod`,
  `SheafOfModules`,
  `SheafOfModules.toSheaf`,
  the canonical `HasLimitsOfSize` / `HasColimitsOfSize` instances on `SheafOfModules 𝒪`,
  `CategoryTheory.Sheaf.ab5ofSize`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪)` on top of the canonical owner
  `SheafOfModules 𝒪`, together with the canonical bridge functor `SheafOfModules.toSheaf 𝒪` to
  sheaves of abelian groups;
- primitive-vs-derived split:
  the primitive data are only the sheaf of rings `𝒪` and the canonical forgetful bridge
  `SheafOfModules.toSheaf 𝒪`;
  all limit, colimit, and `AB5` assertions are derived owner-level API, so the public surface
  should use `Mod(𝒪)` plus anonymous owner instances rather than parallel named wrappers.

Source/core/bridge triage:
- `source-facing`: the Stacks assertions that `Mod(𝒪)` has limits and colimits and that filtered
  colimits are exact;
- `core/canonical`: the owner `SheafOfModules 𝒪`, the bridge functor `SheafOfModules.toSheaf 𝒪`,
  and the Grothendieck-axiom owner `AB5`;
- `bridge/view`: the two preservation instances for `SheafOfModules.toSheaf 𝒪`, which connect the
  owner `Mod(𝒪)` to the already-canonical sheaf category `Sheaf J AddCommGrpCat`.
-/

/-- Helper for Lemma 18.14.2: forgetting a sheaf of modules to a sheaf of abelian groups and then
to a presheaf is the canonical underlying presheaf of abelian groups. -/
noncomputable abbrev toSheaf_comp_sheafToPresheaf :
    SheafOfModules.toSheaf.{max u v} 𝒪 ⋙ sheafToPresheaf J AddCommGrpCat.{max u v} ≅
      SheafOfModules.forget.{max u v} 𝒪 ⋙ PresheafOfModules.toPresheaf.{max u v} 𝒪.obj :=
  SheafOfModules.toSheafCompSheafToPresheafIso (R := 𝒪)

/-- Helper for Lemma 18.14.2: sheafification of presheaves of `𝒪`-modules followed by forgetting
to additive sheaves agrees with additive sheafification of the underlying presheaf, so this
composite preserves all colimits. -/
private theorem sheafification_toSheaf_preservesColimits :
    PreservesColimits
      (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) ⋙
        SheafOfModules.toSheaf.{max u v} 𝒪) := by
  -- The comparison to additive sheafification is the canonical module-sheafification iso.
  let _ :
      PreservesColimits
        (PresheafOfModules.toPresheaf.{max u v} 𝒪.obj ⋙
          presheafToSheaf J AddCommGrpCat.{max u v}) := by
    infer_instance
  simpa using
    (preservesColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{max u v} (𝟙 𝒪.obj)).symm :
      PreservesColimits
        (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) ⋙
          SheafOfModules.toSheaf.{max u v} 𝒪))

/- Lemma 18.14.2 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small limits. -/
#synth HasLimits (Mod(𝒪))

noncomputable instance moduleSheafToSheaf_preservesLimits :
    PreservesLimits (SheafOfModules.toSheaf.{max u v} 𝒪) := by
  -- Route correction: compute limits through the underlying additive presheaf, and then reflect
  -- that computation back along the sheaf inclusion.
  let F := SheafOfModules.toSheaf.{max u v} 𝒪
  let G := sheafToPresheaf J AddCommGrpCat.{max u v}
  -- The composite with `sheafToPresheaf` is the underlying presheaf functor, which preserves
  -- all limits at this universe level.
  let _ : PreservesLimitsOfSize.{max u v, max u v} (F ⋙ G) := by
    refine { preservesLimitsOfShape := fun {K} _ => ?_ }
    let _ : PreservesLimitsOfShape K
        (SheafOfModules.forget.{max u v} 𝒪 ⋙
          PresheafOfModules.toPresheaf.{max u v} 𝒪.obj) := by
      infer_instance
    exact preservesLimitsOfShape_of_natIso (toSheaf_comp_sheafToPresheaf (𝒪 := 𝒪)).symm
  -- Since the sheaf inclusion reflects limits, preservation descends from the composite.
  let _ : ReflectsLimitsOfSize.{max u v, max u v} G := by
    refine { reflectsLimitsOfShape := fun {K} _ => ?_ }
    exact inferInstanceAs
      (ReflectsLimitsOfShape K (sheafToPresheaf J AddCommGrpCat.{max u v}))
  exact preservesLimits_of_reflects_of_preserves F G

/- Lemma 18.14.2 (2): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small limits. -/
#synth PreservesLimits (SheafOfModules.toSheaf.{max u v} 𝒪)

section Colimits

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.14.2 (3): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small colimits. -/
#synth HasColimits (Mod(𝒪))

noncomputable instance moduleSheafToSheaf_preservesColimits :
    PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪) := by
  -- Route correction: replace a module-sheaf diagram by the sheafification of its underlying
  -- presheaf-module diagram, exactly as in the source proof.
  refine { preservesColimitsOfShape := fun {K} _ => ?_ }
  refine { preservesColimit := fun {L} => ?_ }
  let P := L ⋙ SheafOfModules.forget.{max u v} 𝒪
  let e :
      L ≅ P ⋙ PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) :=
    Functor.isoWhiskerLeft L
      (asIso (PresheafOfModules.sheafificationAdjunction.{max u v}
        (𝟙 𝒪.obj)).counit).symm
  let _ :
      PreservesColimits
        (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) ⋙
          SheafOfModules.toSheaf.{max u v} 𝒪) :=
    sheafification_toSheaf_preservesColimits (𝒪 := 𝒪)
  -- The sheafified presheaf-module diagram has a colimit after forgetting to additive sheaves.
  have hsheafified :
      PreservesColimit
        (P ⋙ PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj))
        (SheafOfModules.toSheaf.{max u v} 𝒪) := by
    refine preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves
        (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj))
        (colimit.isColimit P)) ?_
    change IsColimit
      (Functor.mapCocone
        (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) ⋙
          SheafOfModules.toSheaf.{max u v} 𝒪)
        (colimit.cocone P))
    exact isColimitOfPreserves
      (PresheafOfModules.sheafification.{max u v} (𝟙 𝒪.obj) ⋙
        SheafOfModules.toSheaf.{max u v} 𝒪)
      (colimit.isColimit P)
  -- Preservation for the original diagram follows by transporting across the counit iso.
  exact preservesColimit_of_iso_diagram
    (SheafOfModules.toSheaf.{max u v} 𝒪) e.symm

/- Lemma 18.14.2 (4): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small colimits. -/
#synth PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪)

section ExactFilteredColimits

variable [HasSheafify J AddCommGrpCat.{max u v}]

noncomputable instance : AB5 (Mod(𝒪)) where
  ofShape K _ _ := by
    let _ : HasExactColimitsOfShape K (Sheaf J AddCommGrpCat.{max u v}) := by
      infer_instance
    -- Exact filtered colimits descend along the additive forgetful functor just proved above.
    exact HasExactColimitsOfShape.domain_of_functor K
      (SheafOfModules.toSheaf.{max u v} 𝒪)

/- Lemma 18.14.2 (5): filtered colimits are exact in `Mod(𝒪)`. In canonical mathlib form, this
says that `Mod(𝒪)` satisfies `AB5`. -/
#synth AB5 (Mod(𝒪))

/-- Lemma 18.14.2: for a ringed topos `(Sh(𝒞), 𝒪)`, the category `Mod(𝒪)` of sheaves of
`𝒪`-modules has all small limits and colimits, the forgetful functor to sheaves of abelian groups
commutes with them, and filtered colimits are exact. The canonical mathlib packaging of these
assertions is split between the owner-level limit/colimit instances synthesized above and the
source-facing preservation/exactness conjunction below. -/
@[stacks 03DB]
theorem mod_forgetful_has_limits_colimits_and_ab5 :
    PreservesLimits (SheafOfModules.toSheaf.{max u v} 𝒪) ∧
      PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪) ∧ AB5 (Mod(𝒪)) := by
  exact ⟨moduleSheafToSheaf_preservesLimits 𝒪, moduleSheafToSheaf_preservesColimits 𝒪,
    inferInstance⟩

end ExactFilteredColimits

end Colimits

end
