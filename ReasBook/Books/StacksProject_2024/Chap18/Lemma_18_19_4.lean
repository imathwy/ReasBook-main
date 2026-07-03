import StacksProject_2024.Chap18.Lemma_18_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.4:
- primary domain: exactness reflection for extension by zero from the localized ringed site
  `(C/U, J.over U, 𝒪_U)` to `(C, J, 𝒪)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `ringedSiteLocalizedExtensionByZero_exact`;
- best owner abstraction:
  `let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U;
   SheafOfModules.pullback (𝟙 𝒪_U)`, the canonical
  lower-shriek extension-by-zero owner `j_{U!}`;
- primitive data: only the site `(C, J)`, the structure sheaf `𝒪`, and the object `U : C`;
- derived API: the source-facing exactness comparison for short complexes under `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a short complex over `𝒪_U` is exact iff its
  extension by zero is exact over `𝒪`;
- `core/canonical`: the mathlib owner
  `let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U;
   SheafOfModules.pullback (𝟙 𝒪_U)` for localization extension by zero;
- `bridge/view`: the exactness comparison theorem below.

This lemma is a bridge/view statement: the source-facing `j_{U!}` is the canonical pullback owner
above, so the file should reuse that owner directly instead of introducing the opposite direct
image `j_{U,*}` or extra local wrapper/instance noise. -/

-- Proof sketch: Lemma `18.19.3` identifies the forward implication with exactness of the
-- canonical extension-by-zero owner `j_{U!}`. The converse is the source-facing reflection
-- statement for the same owner on localized `\mathcal O_U`-modules.
/-- Lemma 18.19.4: a short complex of `\mathcal O_U`-modules on the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is exact if and only if its image under extension by zero
`j_{U!} : \mathrm{Mod}(\mathcal O_U) ⥤ \mathrm{Mod}(\mathcal O)` is exact. In canonical mathlib
form, `j_{U!}` is the pullback functor on sheaves of modules induced by the identity morphism of
the localized structure sheaf `\mathcal O_U`. -/
theorem ringedSiteLocalizedExtensionByZero_exact_iff
    (S : ShortComplex (ringedSiteModuleCategory (J.over U) (𝒪.over U))) :
    let 𝒪_U := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U
    S.Exact ↔ (S.map (SheafOfModules.pullback (𝟙 𝒪_U))).Exact :=
  sorry

end
