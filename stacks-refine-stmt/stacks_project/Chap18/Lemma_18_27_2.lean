import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 18.27.2:
- primary domain: prestacks on a site, viewed as pseudofunctors `Cᵒᵖ ⥤ᵖ Cat`, together with the
  Hom-presheaves on slice categories and their compatibility with restriction;
- sampled owner API:
  `Pseudofunctor.presheafHom`,
  `Pseudofunctor.presheafHomObjHomEquiv`,
  `Pseudofunctor.overMapCompPresheafHomIso`,
  `Pseudofunctor.sheafHom`;
- best owner abstraction: the Hom-presheaf owner `Pseudofunctor.presheafHom`, with
  `Pseudofunctor.overMapCompPresheafHomIso` as the canonical restriction-compatibility isomorphism;
- primitive data: a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, a base object `S : C`,
  two fiber objects `M N : F.obj (.mk (Opposite.op S))`, and a morphism `q : S' ⟶ S`;
- derived API: the slice-site Hom-presheaf `F.presheafHom M N`, its value at the identity object,
  the restriction isomorphism along `Over.map q`, and under prestack hypotheses the associated
  sheaf `F.sheafHom`.

Source/core/bridge triage:
- `source-facing`: internal Hom for modules on localized ringed sites commutes with restriction to
  a slice site;
- `core/canonical`: `Pseudofunctor.overMapCompPresheafHomIso`;
- `bridge/view`: specializing the generic prestack statement to the pseudofunctor of localized
  module categories and then using `Presieve.isSheafFor_iff_of_iso` in descent arguments.

This file is therefore a core/canonical recall file. No chapter-local compatibility wrapper should
survive here, since the exact comparison isomorphism already lives upstream in mathlib.
-/
/- Lemma 18.27.2: for the prestack on a ringed site sending an object `U` to the category of
sheaves of `\mathcal O_U`-modules on the localized site `(C/U, J.over U)`, formation of the
internal Hom commutes with restriction to `U`. In canonical mathlib form, this is exactly the
generic compatibility isomorphism of the prestack Hom-presheaf with pullback to a slice site,
applied to the pseudofunctor of localized module categories. -/
recall Pseudofunctor.overMapCompPresheafHomIso
