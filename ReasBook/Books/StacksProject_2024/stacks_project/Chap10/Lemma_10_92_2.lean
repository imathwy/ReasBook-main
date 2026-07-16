import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_84_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_88_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_88_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_92_1

-- Declarations for this item will be appended below by the statement pipeline.

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
