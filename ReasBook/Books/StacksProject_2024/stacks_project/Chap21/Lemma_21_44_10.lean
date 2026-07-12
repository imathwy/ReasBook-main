import StacksProject_2024.Chap21.Lemma_21_44_9

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [MonoidalClosed (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.44.10:
- primary domain: derived internal Hom for complexes of `𝒪`-modules on a ringed site,
  represented by the canonical internal-Hom complex under the bounded-below, bounded-above, and
  degreewise finite-free-retract hypotheses;
- best owner abstraction: the source-facing owner is the direct comparison statement
  `IsIsomorphic (DerivedCategory.Q.obj (E ⟶[CpxO] F))
    (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F)`;
- primitive data: the complexes `E`, `F`, the lower bound on `F`, the upper bound on `E`, and
  the Chapter 21 owner `SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J 𝒪)` applied
  termwise to `E`;
- derived API: the source-facing boundedness theorem together with the explicit-bounds companion
  below, which is only a bridge/view that repackages the existential boundedness hypotheses.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.10 on a ringed site;
- `core/canonical`: `(ihom E).obj F`, `IsIsomorphic`, and
  `SheafOfModules.finiteFreeRetractModuleProperty`;
- `bridge/view`: the explicit-bounds companion theorem below, which only unwraps the existential
  boundedness data from the source-facing statement.
-/

/-- Lemma 21.44.10: for complexes `E` and `F` of `𝒪`-modules on a ringed site `(𝒞, 𝒪)`, if `F`
is bounded below, `E` is bounded above, and each term of `E` is a direct summand of a finite free
`𝒪`-module, then the derived internal Hom from `E` to `F` is represented by the canonical
internal-Hom complex `E ⟶[CpxO] F`. -/
@[stacks 08JI]
theorem ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
    (E F : CpxO)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ,
        SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J 𝒪) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (E ⟶[CpxO] F))
      (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F) := by
  sorry

/-- Explicit-bounds companion to Lemma 21.44.10. It is only a bridge/view form of the main
source-facing theorem, with the existential boundedness hypotheses replaced by chosen bounds
`a` and `b`. -/
theorem ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyGE_of_isStrictlyLE_of_termwise_finiteFreeRetract
    (E F : CpxO)
    {a b : ℤ}
    (hF_boundedBelow : F.IsStrictlyGE a)
    (hE_boundedAbove : E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ,
        SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J 𝒪) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (E ⟶[CpxO] F))
      (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F) := by
  exact
    ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
      E F ⟨a, hF_boundedBelow⟩ ⟨b, hE_boundedAbove⟩ hE_termwise_finiteFreeRetract

end

end SheafOfModules.RingedSite
