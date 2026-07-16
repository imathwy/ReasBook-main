import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

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
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.44.9:
- primary domain: derived internal Hom for complexes of `𝒪`-modules on a ringed site,
  computed by the canonical internal-Hom complex under the strict-perfect source hypotheses;
- inspected owner declarations:
  `cochainComplex_isStrictlyPerfect_iff`,
  `SheafOfModules.RingedSite.CochainComplex.IsStrictlyPerfect`,
  `(ihom E).obj F`,
  `IsIsomorphic`,
  `DerivedCategory.Q`,
  `ringedSiteModuleComplexInternalHom_isKInjective`,
  `module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective`;
- best owner abstraction: the direct comparison statement
  `IsIsomorphic (DerivedCategory.Q.obj (E ⟶[CpxO] F))
    ((DerivedCategory.Q.obj E) ⟹ (DerivedCategory.Q.obj F))`,
  with the strict-perfect hypothesis expressed by the Chapter 21 ringed-site owner
  `SheafOfModules.RingedSite.CochainComplex.IsStrictlyPerfect E`;
- primitive data: the complexes `E`, `F`, together with the Chapter 21 owner hypothesis
  `SheafOfModules.RingedSite.CochainComplex.IsStrictlyPerfect E`;
- derived API: the representing-isomorphism statement for the canonical internal-Hom complex
  `E ⟶[CpxO] F`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.9 for complexes of `𝒪`-modules on a ringed site;
- `core/canonical`: `CochainComplex.IsStrictlyPerfect`, `(ihom E).obj F`, and
  `IsIsomorphic`;
- `bridge/view`: the bundled-site specialization
  `_root_.RingedSite.CochainComplex.IsStrictlyPerfect` on `RingedSite.ofCommRingSheaf J 𝒪`,
  identified with the Chapter 21 owner by matching the two boundedness-and-termwise-retract
  predicates. -/

-- Proof sketch: choose a K-injective resolution `F ⟶ I`. By Section `21.35`, the complex
-- `E ⟶[CpxO] I` represents `RHom(E, F)`. Since
-- `E` is strictly perfect, only finitely many terms contribute in each degree, so the canonical
-- map `(E ⟶[CpxO] F) ⟶ (E ⟶[CpxO] I)` is a
-- quasi-isomorphism by the local comparison argument of Lemma `21.44.8`.
--
/-
The public statement only needs the closed-monoidal owners on the complex category `CpxO` and on
the derived category `D(Mod)`, together with the Chapter 21 strict-perfectness owner. The
module-level product, biproduct, coproduct, additivity, and map-bifunctor infrastructure used to
construct those monoidal structures stays off the exported theorem surface.
-/
/-- Lemma 21.44.9: for complexes `E` and `F` of `𝒪`-modules on a ringed site `(𝒞, 𝒪)`, if `E`
is strictly perfect, then `RHom(E, F)` is represented by the canonical internal-Hom complex
`E ⟶[CpxO] F`. Because `E` is strictly perfect, the degreewise products in this complex are
finite and match the textbook formula `⨁_{n = p + q} Hom_𝒪(E^{-q}, F^p)`. -/
@[stacks 08JH]
theorem ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect
    (E F : CpxO)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    IsIsomorphic
      (DerivedCategory.Q.obj (E ⟶[CpxO] F))
      (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F) := by
  sorry

end

end SheafOfModules.RingedSite
