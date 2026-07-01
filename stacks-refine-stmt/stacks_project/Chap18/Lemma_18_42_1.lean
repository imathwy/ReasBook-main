import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace CategoryTheory

open CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C]
/- Domain-style sampling:
- primary domain: constant presheaves/sheaves of abelian groups on a site and preservation of
  short exact sequences by exact functors;
- sampled owner declarations:
  `Functor.const`,
  `constantSheaf`,
  `presheafToSheaf`,
  `ExactFunctor.of`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the exact-functor factorization
  `Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{w}`, whose sheaf-level owner is
  `constantSheaf J AddCommGrpCat.{w}`;
- primitive data: the short exact sequence `S` in `AddCommGrpCat`, plus the site `J` for the
  sheafification stage;
- derived API: exactness of the constant presheaf sequence is the bridge/view layer, and the
  sheaf-level theorem is obtained by applying exact sheafification.

Source/core/bridge triage:
- `source-facing`: `shortExact_constantAbelianSheaf`;
- `core/canonical`: `Functor.const Cᵒᵖ`, `constantSheaf J AddCommGrpCat.{w}`,
  `presheafToSheaf J AddCommGrpCat.{w}`, and `ShortComplex.ShortExact.map_of_exact`;
- `bridge/view`: `shortExact_constantAbelianPresheaf`, which records the honest constant-presheaf
  stage before sheafification.

The source statement is about constant sheaves on a site, so the main labeled entry remains at the
`constantSheaf` owner. The previous bridge through the underlying presheaf of `constantSheaf` was
semantically wrong, because `constantSheaf` is the sheafification of the constant presheaf rather
than a sectionwise copy of the original abelian group on arbitrary objects. The correct bridge is
therefore the exact constant-presheaf sequence, followed by exact sheafification at the
`HasSheafify` layer. -/

variable {J : GrothendieckTopology C}

local instance constantSheaf_preservesZeroMorphisms [HasWeakSheafify J AddCommGrpCat.{w}] :
    (constantSheaf J AddCommGrpCat.{w}).PreservesZeroMorphisms := by
  dsimp [constantSheaf]
  infer_instance

-- Proof sketch: `Functor.const Cᵒᵖ` is exact, so it carries short exact sequences of abelian
-- groups to short exact sequences of constant abelian presheaves.
/-- Companion to Lemma 18.42.1: a short exact sequence of abelian groups remains short exact after
applying the constant abelian presheaf functor. -/
theorem shortExact_constantAbelianPresheaf
    (S : ShortComplex AddCommGrpCat.{w}) (hS : S.ShortExact) :
    (S.map (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})).ShortExact := by
  simpa using
    hS.map_of_exact (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})

-- Proof sketch: `constantSheaf J AddCommGrpCat` is `Functor.const Cᵒᵖ ⋙ presheafToSheaf`, so the
-- sheaf statement follows from the presheaf bridge together with exactness of `presheafToSheaf`.
/-- Lemma 18.42.1: for a site `(\mathcal C, J)`, a short exact sequence of abelian groups remains
short exact after applying the constant abelian sheaf functor
`constantSheaf J AddCommGrpCat`. -/
theorem shortExact_constantAbelianSheaf
    [HasSheafify J AddCommGrpCat.{w}]
    (S : ShortComplex AddCommGrpCat.{w}) (hS : S.ShortExact) :
    (S.map (constantSheaf J AddCommGrpCat.{w})).ShortExact := by
  simpa [constantSheaf] using
    (show ((S.map (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})).map
        (presheafToSheaf J AddCommGrpCat.{w})).ShortExact from
      (shortExact_constantAbelianPresheaf (C := C) S hS).map_of_exact
        (presheafToSheaf J AddCommGrpCat.{w}))

end CategoryTheory
