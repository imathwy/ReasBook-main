import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_92_1 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: countable directed subpresentations of finitely presented colimit presentations of
  countably generated Mittag-Leffler modules;
- sampled owner declarations of the same kind:
  `Module.MittagLeffler`,
  `Module.CountablyGenerated`,
  `IsMittagLefflerDirectedSystem`,
  `Module.MittagLefflerPresentation`;
- owner abstraction: `Module.MittagLeffler` is the canonical owner for the source-level
  Mittag-Leffler hypothesis, while `IsMittagLefflerDirectedSystem` is presentation-level bridge
  data attached to one chosen diagram;
- primitive data for the source-facing theorem: the module `M`, a directed system `F` of finitely
  presented modules, a colimit identification `c : colimit F ≅ M`, and the owner hypotheses
  `Module.MittagLeffler R M` and `Module.CountablyGenerated R M`;
- derived API: the presentation-level companion theorem below specializes the source-facing theorem
  to the intrinsic colimit module `colimit F`.
-/
-- Proof sketch: choose a countable generating family of `M`, transfer those generators to the
-- fixed presentation `c : colimit F ≅ M`, and combine countability with the module-level
-- Mittag-Leffler condition to build a countable directed subset of stages that already captures
-- all generators and the eventual factorization data for the chosen presentation. The restricted
-- colimit comparison is then surjective by construction and injective by the stabilization
-- property.
/-- Lemma 10.92.1: let `M` be a countably generated Mittag-Leffler `R`-module and let
`c : colimit F ≅ M` be a directed colimit presentation of `M` by finitely presented modules. Then
there is a countable directed sub-preorder of `I`, realized canonically as a subtype, whose
comparison morphism to the original colimit is an isomorphism. Equivalently, the chosen
presentation of `M` admits a countable directed subsystem with the same colimit. -/
theorem exists_countable_directed_subpresentation_of_countably_generated_mittag_leffler
    (F : I ⥤ ModuleCat.{v} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M)
    (hML : Module.MittagLeffler R M)
    (hcg : Module.CountablyGenerated R M) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      IsIso (colimit.pre F (OrderEmbedding.subtype S).toOrderHom.toFunctor) := sorry

-- Proof sketch: specialize Lemma `10.92.1` to the intrinsic colimit module `colimit F`, using the
-- finite-presentation component of `hF` and the presentation-level Mittag-Leffler hypothesis to
-- recover the owner hypothesis `Module.MittagLeffler R ↑(colimit F)`.
/-- Presentation-level bridge form of Lemma 10.92.1: if a chosen directed system `F` is
Mittag-Leffler in the sense of Definition `10.88.1` and its colimit is countably generated, then
that presentation has a countable directed subsystem with the same colimit. -/
theorem exists_countable_directed_subpresentation_of_countably_generated_of_isMittagLefflerDirectedSystem
    (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F)) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      IsIso (colimit.pre F (OrderEmbedding.subtype S).toOrderHom.toFunctor) := sorry

end

/-! ### Lemma_10_92_2 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]

/- Domain triage:
- primary domain: countably generated Mittag-Leffler modules via directed colimit presentations by
  finitely presented modules;
- sampled owner declarations:
  `Module.CountablyGenerated`,
  `Module.MittagLeffler`,
  `IsMittagLefflerDirectedSystem`,
  `exists_countable_directed_subpresentation_of_countably_generated_mittag_leffler`,
  `exists_countable_directed_subpresentation_of_countably_generated_of_isMittagLefflerDirectedSystem`,
  and `Module.MittagLeffler.exists_presentation`;
- best owner abstraction for the ring-general source statement: `Module.MittagLeffler`;
- primitive data:
  the module `M`, the countable-generation hypothesis, and the finite source map `f`;
- derived API:
  a chosen presentation `F : I ⥤ ModuleCat R` with `IsMittagLefflerDirectedSystem F`,
  used only in the bridge theorem below, and the resulting finitely presented factor module.

Layer classification:
- `bridge/view`: the presentation-level theorem below upgrades a chosen presentation to the
  source-facing factorization statement;
- `source-facing`: the second theorem is the textbook ring-general statement for an abstract module
  `M`;
- `core/canonical`: `Module.MittagLeffler` is the owner abstraction, while
  `IsMittagLefflerDirectedSystem` is the presentation data extracted from
  `MittagLeffler.exists_presentation`.
-/
-- Proof sketch: first apply the presentation-level bridge form of Lemma `10.92.1` to replace the
-- given presentation by a countable directed subsystem with the same colimit. Then use Example
-- `10.86.2` and Lemma `10.86.3` on the associated Hom inverse system against the finite source `P`
-- to find a stage where the image of `f` stabilizes. The induced map back to the colimit yields an
-- endomorphism fixing `f`, and this endomorphism factors through a finitely presented stage of the
-- presentation.
/-- Lemma 10.92.2 in presentation form: if `F` is a Mittag-Leffler directed system of finitely
presented `R`-modules with countably generated colimit, then any map from a finite module into
`colimit F` is fixed by an endomorphism of `colimit F` factoring through a single stage `F.obj i`.
This is the bridge from the owner `MittagLeffler R M` to the source-facing finite-presentation
factorization statement; the stage `F.obj i` is already finitely presented by
`IsMittagLefflerDirectedSystem F`. -/
theorem exists_stage_factorization_fixing_finite_map
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I] (F : I ⥤ ModuleCat.{v} R)
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R ↑(colimit F))
    (f : P →ₗ[R] ↑(colimit F)) :
    ∃ i, ∃ g : ↑(colimit F) →ₗ[R] F.obj i,
      (((colimit.ι F i).hom : F.obj i →ₗ[R] ↑(colimit F)) ∘ₗ g) ∘ₗ f = f := sorry

/-- Lemma 10.92.2: if `M` is a countably generated Mittag-Leffler `R`-module, then for every map
`f : P →ₗ[R] M` from a finite source there is a finitely presented `R`-module `Q` and maps
`M → Q → M` whose composite fixes `f`. This is the ring-general source-facing statement, with the
presentation data kept internal to the owner `MittagLeffler R M`. -/
theorem exists_endomorphism_factorsThroughFinitePresentation_fixing_finite_map
    (hcg : Module.CountablyGenerated R M)
    (hML : MittagLeffler R M)
    (f : P →ₗ[R] M) :
    ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q)
      (g : M →ₗ[R] Q) (h : Q →ₗ[R] M),
        (h ∘ₗ g) ∘ₗ f = f := sorry

end

end Module
