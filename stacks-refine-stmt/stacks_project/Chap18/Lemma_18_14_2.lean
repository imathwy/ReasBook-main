import Mathlib
import stacks_project.Chap18.Definition_18_10_1

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

/- Lemma 18.14.2 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small limits. -/
#synth HasLimits (Mod(𝒪))

private theorem toSheaf_preservesLimits :
    PreservesLimits (SheafOfModules.toSheaf 𝒪) := by
  sorry

noncomputable instance :
    PreservesLimits (SheafOfModules.toSheaf 𝒪) :=
  toSheaf_preservesLimits 𝒪

/- Lemma 18.14.2 (2): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small limits. -/
#synth PreservesLimits (SheafOfModules.toSheaf 𝒪)

section Colimits

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.14.2 (3): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small colimits. -/
#synth HasColimits (Mod(𝒪))

private theorem toSheaf_preservesColimits :
    PreservesColimits (SheafOfModules.toSheaf 𝒪) := by
  sorry

noncomputable instance :
    PreservesColimits (SheafOfModules.toSheaf 𝒪) :=
  toSheaf_preservesColimits 𝒪

/- Lemma 18.14.2 (4): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small colimits. -/
#synth PreservesColimits (SheafOfModules.toSheaf 𝒪)

section ExactFilteredColimits

variable [HasSheafify J AddCommGrpCat.{max u v}]

noncomputable instance : AB5 (Mod(𝒪)) where
  ofShape K _ _ := by
    let _ : HasExactColimitsOfShape K (Sheaf J AddCommGrpCat.{max u v}) := by
      infer_instance
    exact HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf 𝒪)

/- Lemma 18.14.2 (5): filtered colimits are exact in `Mod(𝒪)`. In canonical mathlib form, this
says that `Mod(𝒪)` satisfies `AB5`. -/
#synth AB5 (Mod(𝒪))

end ExactFilteredColimits

end Colimits

end
