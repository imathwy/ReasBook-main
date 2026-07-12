import Mathlib
import StacksProject_2024.Chap10.Definition_10_84_1
import StacksProject_2024.Chap10.Definition_10_88_1
import StacksProject_2024.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

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
