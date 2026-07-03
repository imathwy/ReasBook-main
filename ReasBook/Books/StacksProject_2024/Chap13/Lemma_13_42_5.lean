import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_42_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open SequentialProObjectMorphismRep
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.42.5:
- primary domain: morphisms of sequential inverse systems in `D(𝒜)`, controlled through the
  Chapter 4 owner `SequentialProObjectMorphismRep` and detected on cohomology towers.
- inspected owner-level declarations:
  `SequentialInverseSystem`,
  `SequentialProObjectMorphismRep.ofNatTrans`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  `triangleFirstToSecond_isProIsomorphism_of_proZero_third`.
- best owner abstraction: the source-facing result is that the sequential representative attached
  to `α` is a pro-isomorphism; the owner-level bridge to Hom-colimit bijectivity is already
  upstream, so it should not be recopied locally.
- primitive data: the sequential inverse systems `A` and `B`, the natural transformation `α`, the
  uniform cohomological bounds on both systems expressed by the canonical owners `IsGE` / `IsLE`,
  and the degreewise owner-level pro-isomorphism hypotheses on the cohomology towers `A ⋙ H^i`
  and `B ⋙ H^i` in the
  bounded window `Set.Icc a b`.
- derived API: `(ofNatTrans α).IsProIsomorphism`; Hom-colimit bijectivity is derived from the
  upstream owner theorem `isProIsomorphism_toProObjectHom_app_bijective`.

Source/core/bridge triage:
- `source-facing`: the main theorem below, asserting that `α` induces a pro-isomorphism in
  `D(𝒜)`.
- `core/canonical`: `SequentialInverseSystem`, `SequentialProObjectMorphismRep`, and
  `.IsProIsomorphism`.
- `bridge/view`: the Hom-colimit evaluation map `.toProObjectHom.app X`, supplied upstream rather
  than by a second local wrapper theorem. -/

-- Proof sketch: choose a compatible inverse system of distinguished triangles extending the maps
-- `α.app (op n) : A.obj (op n) ⟶ B.obj (op n)`. The boundedness assumptions and the degreewise
-- pro-isomorphism
-- hypothesis imply, by Lemma `13.42.3`, that the cone system has pro-zero cohomology and hence is
-- pro-zero in `D(𝒜)`; outside `[a, b]` the cone cohomology towers are already zero by the uniform
-- bounds. Then Lemma `13.42.4` gives a pro-isomorphism for those triangles, and the owner-level
-- bridge `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective` turns
-- that into bijectivity of the induced Hom-colimit map for every test object.
/-- Lemma 13.42.5: if `α : A ⟶ B` is a morphism of sequential inverse systems in `D(\mathcal A)`
and there exist integers `a` and `b` such that both systems have cohomology supported in
`[a, b]`, while for every degree `i ∈ [a, b]` the induced morphism of inverse systems on `H^i` is a
pro-isomorphism in `\mathcal A`, then `α` is a pro-isomorphism of inverse systems in
`D(\mathcal A)`. -/
theorem ofNatTrans_isProIsomorphism_of_uniformlyBounded_homologywise_proIso
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b,
      (ofNatTrans (Functor.whiskerRight α (H^i))).IsProIsomorphism) :
    (ofNatTrans α).IsProIsomorphism :=
  sorry

end CategoryTheory
