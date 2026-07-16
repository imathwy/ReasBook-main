import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Sheaf J CommRingCat)
variable (φ : O₁ ⟶ O₂)

/- Domain-style sampling for Definition 18.33.3:
- primary domain: sheafified relative differentials of a morphism of sheaves of commutative rings
  on a site, together with the universal relative derivation;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `relativeDifferentials`,
  `relativeDifferentials_def`,
  `relativeDifferential`;
- best owner abstraction: the chapter owner `relativeDifferentials`, written `Ω(φ)`, with
  `relativeDifferentials_def` and `relativeDifferential` as its derived API;
- primitive data: only the morphism of sheaves of rings `φ : O₁ ⟶ O₂`;
- derived API: the sheafification identity for `Ω(φ)` and the universal derivation
  `relativeDifferential φ`.

Source/core/bridge triage:
- `core/canonical`: the presheaf-level owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: `relativeDifferentials`, written `Ω(φ)`;
- `bridge/view`: the theorem `relativeDifferentials_def` identifying `Ω(φ)` with the sheafified
  presheaf owner, and the universal derivation `relativeDifferential φ`.

This numbered definition is recall-only: the canonical chapter owner already exists in
`Lemma_18_33_2`, so this file should reuse that owner directly rather than rebuild the same
sheafification term on the public surface. -/

/- Definition 18.33.3, owner recall: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative
rings on a site, the sheaf of relative differentials `Ω_{O₂/O₁}` is the canonical owner
`relativeDifferentials`, written `Ω(φ)`. -/
recall relativeDifferentials

/- Companion recall: `Ω(φ)` is the sheafification of the canonical presheaf of relative
differentials. -/
#check relativeDifferentials_def φ

/- Companion recall: the universal `φ`-derivation
`d : O₂ ⟶ Ω_{O₂/O₁}` is the canonical owner `relativeDifferential φ`. -/
#check relativeDifferential φ

end
