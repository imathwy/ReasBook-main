import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u w

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.ShortComplex

/- Domain-style sampling for Lemma 12.32.1:
- primary domain: homology of short complexes and exact products in an abelian category;
- sampled owner declarations:
  * `CategoryTheory.HasExactLimitsOfShape`
  * `ShortComplex.mapHomologyIso`
  * `ShortComplex.functorEquivalence`
  * `Pi.isoLimit`
- best owner abstraction: the exact product functor `lim : (Discrete I ⥤ C) ⥤ C`, together with
  the canonical short-complex-in-functors view provided by `functorEquivalence`;
- primitive data:
  * the family `S : I → ShortComplex C`
  * the product functor on `Discrete I`-shaped diagrams in `C`
- derived API:
  * the short complex `T : ShortComplex (Discrete I ⥤ C)` corresponding to `S`
  * the termwise homology identification
  * the resulting comparison between the homology of `∏ᶜ S` and `∏ᶜ fun i ↦ (S i).homology`

Source/core/bridge triage:
- `source-facing`: the product-homology comparison for a family of short complexes;
- `core/canonical`: `mapHomologyIso` for the exact limit functor `lim`;
- `bridge/view`: `functorEquivalence (Discrete I) C`, which turns the family `S` into a single
  short complex in the functor category so the owner `mapHomologyIso` applies directly. -/

variable {C : Type u} [Category.{v} C] [Abelian C] {I : Type w}
  [HasProductsOfShape I C] [HasExactLimitsOfShape (Discrete I) C]

/-- Lemma 12.32.1: for a family of short complexes in an abelian category with exact
`I`-indexed products, the homology of their product is canonically isomorphic to the
product of their homology objects. Here `∏ᶜ S` is the termwise product short complex,
viewed through the canonical product object in `ShortComplex C`. -/
def pi_homologyIso (S : I → ShortComplex C) :
    (∏ᶜ S).homology ≅ ∏ᶜ fun i ↦ (S i).homology := by
  let F : Discrete I ⥤ ShortComplex C := Discrete.functor S
  let e := functorEquivalence (Discrete I) C
  let T : ShortComplex (Discrete I ⥤ C) := e.inverse.obj F
  let H : Discrete I ⥤ C := Discrete.functor fun i ↦ (S i).homology
  let termwiseHomologyIso : T.homology ≅ H :=
    Discrete.natIso fun i ↦
      (T.mapHomologyIso ((evaluation (Discrete I) C).obj i)).symm ≪≫
        (homologyFunctor C).mapIso ((e.counitIso.app F).app i)
  exact (homologyFunctor C).mapIso
      ((limit.isLimit F).conePointUniqueUpToIso (isLimitLimitCone F)) ≪≫
    (T.mapHomologyIso (lim : (Discrete I ⥤ C) ⥤ C) ≪≫
      lim.mapIso termwiseHomologyIso ≪≫
        (Pi.isoLimit H).symm)

end CategoryTheory.ShortComplex
