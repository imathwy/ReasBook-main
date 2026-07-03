import Mathlib
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_6_1 (from Chap07) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.6.1:
- primary domain: type-indexed families of arrows with common target in a category, viewed through
  slice categories;
- inspected owner declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.SemiRepresentableFamily`,
  `CategoryTheory.SemiRepresentableFamily.Over`,
  `CategoryTheory.SemiRepresentableFamily.Over.forget`;
- best owner abstraction: `SemiRepresentableFamily.Over U`, i.e. a semi-representable family in the
  slice category `C / U`;
- primitive data: only the common target `U` and the family of objects of `C / U`, equivalently an
  index type together with arrows to `U`;
- derived API: forgetting to the underlying semi-representable family in `C` via
  `SemiRepresentableFamily.Over.forget`.

Source/core/bridge triage:
- `source-facing`: the textbook notion of a family of morphisms with fixed target `U`;
- `core/canonical`: `SemiRepresentableFamily.Over U`;
- `bridge/view`: the equivalent indexed-arrow presentation, obtained by viewing an object of
  `SemiRepresentableFamily.Over U` as a type-indexed family of objects of `Over U`.
-/

/- Definition 7.6.1: for an object `U` of a category `C`, a family of morphisms with fixed target
`U` is canonically modeled by `SemiRepresentableFamily.Over U`, i.e. by a family of objects of the
slice category `C / U`, equivalently an index type `I` together with arrows `Uᵢ ⟶ U` for each
`i : I`. -/
recall SemiRepresentableFamily.Over

end CategoryTheory

/-! ### Definition_7_6_2 (from Chap07) -/
universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.6.2:
- primary domain: sites presented by set-sized covering families on a category;
- sampled owner API:
  `Precoverage`,
  `Pretopology`,
  `Pretopology.toPrecoverage`,
  `Pretopology.toGrothendieck`,
  `Precoverage.toPretopology`;
- best owner abstraction: `Pretopology C`;
- primitive data: the covering presieves of a chosen precoverage;
- derived API: the three site axioms and the associated Grothendieck topology.

Source/core/bridge triage:
- `source-facing`: the Stacks Project notion of a site given by set-sized covering families;
- `core/canonical`: mathlib's `Pretopology C`, whose docstring explicitly records that Stacks
  calls a category with a pretopology a site;
- `bridge/view`: the underlying `Precoverage` and the generated Grothendieck topology.

The file therefore recalls the canonical owner `Pretopology` directly rather than introducing a
parallel local `Site` wrapper or a conjunction of the three axioms. -/

section

variable [HasPullbacks C]

/- Definition 7.6.2: a site is a category equipped with covering families with fixed target,
containing singleton isomorphism covers, closed under composition of covering families, and stable
under base change. In mathlib this is the canonical owner `Pretopology C`. -/
recall Pretopology

section

variable (J : Pretopology C)

/- Companion check: the raw set of covering families underlying a pretopology is its inherited
`Precoverage`. -/
#check (J.toPrecoverage)

/- Companion check: the pretopology site generates its associated Grothendieck topology. -/
#check (J.toGrothendieck)

end

section

variable (J : Precoverage C)
variable [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]

/- Bridge recall: a raw precoverage satisfying the three owner-level axioms upgrades to the
canonical pretopology owner. -/
recall Precoverage.toPretopology

end

end

end CategoryTheory

/-! ### Remark_7_6_3 (from Chap07) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 7.6.3:
- primary domain: replacing a proper class of coverings by set-sized site presentations without
  changing the resulting sheaf category;
- sampled owner API:
  `Coverage.toGrothendieck`,
  `topology_eq_iff_same_sheaves`,
  `Coverage.tautologicalEnlargement_toGrothendieck`,
  `isSheaf_iff_of_common_ambient_pretopology`;
- source/core/bridge triage:
  `source-facing`: the remark that several natural set-sized replacements for a proper class of
    coverings lead to the same sheaf category, even though the chapter chooses one presentation
    for later development;
  `core/canonical`: `GrothendieckTopology C` and the sheaf predicate on it;
  `bridge/view`: equal-topology comparisons between different set-sized presentations, especially
    `Coverage.tautologicalEnlargement_toGrothendieck`, whose source-facing owner is now
    `Precoverage.tautologicalEnlargement`, and which matches the later chapter route of replacing
    a coverage by the canonical set of tautologically equivalent coverings while keeping the
    associated topology unchanged.

Primitive data in Lean are the chosen set-sized presentations such as `Coverage C`. The associated
Grothendieck topology and the induced sheaf predicate are derived API, so the main public entry
here should be the canonical same-sheaf owner theorem rather than a presentation-specific wrapper.
For the remark's stated alternative route, the faithful bridge is the later tautological
enlargement theorem; the choice-based comparison route is already available separately via
Lemma 7.8.8.
-/

/- Remark 7.6.3, core/canonical recall: two Grothendieck topologies define the same sheaf theory
exactly when they are equal. This is the owner-level invariance statement behind the remark that
different set-sized replacements for a proper-class covering relation give the same sheaf
category. -/
recall topology_eq_iff_same_sheaves

/- Companion bridge recall: replacing a coverage by the later canonical set of tautologically
equivalent coverings does not change the associated Grothendieck topology. This matches the
remark's cited route through the associated topology and the later covering-family modification. -/
recall Coverage.tautologicalEnlargement_toGrothendieck (K : Coverage C) :
    K.toPrecoverage.tautologicalEnlargement.toGrothendieck = K.toGrothendieck

end CategoryTheory

/-! ### Example_7_6_4 (from Chap07) -/
/- Domain-style sampling for Example 7.6.4:
- primary domain: the canonical site on the opens category of a topological space and the
  corresponding sheaf condition for presheaves on that site;
- sampled owner API:
  `Opens.pretopology`,
  `Opens.grothendieckTopology`,
  `Opens.pretopology_toGrothendieck`,
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`;
- source/core/bridge triage:
  `source-facing`: the textbook description of the opens site by covering families
  `{Uᵢ ⟶ U}` with `iSup Uᵢ = U`, together with the usual open-cover sheaf condition;
  `core/canonical`: the mathlib owners `Opens.pretopology`, `Opens.grothendieckTopology`, and
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`;
  `bridge/view`: the theorem `Opens.pretopology_toGrothendieck`, which identifies the
  source-facing covering-family presentation with the canonical opens-site Grothendieck topology.

Primitive data are just the topological space and its opens category. The covering-family and
usual-sheaf-condition phrasing are derived views of the upstream owners, so this file should remain
a pure recall file rather than introduce chapter-local aliases or wrapper definitions.
-/

/- Example 7.6.4: for a topological space `X`, the category of open subsets of `X` with
inclusion morphisms and covering families `{Uᵢ ⟶ U}` satisfying `⋃ i, Uᵢ = U` is the canonical
pretopology `Opens.pretopology` on the opens category. In particular, the empty open and the
empty covering of `⊥` are allowed. -/
recall Opens.pretopology

/- The associated site on the category of open subsets is the canonical Grothendieck topology
`Opens.grothendieckTopology`. -/
recall Opens.grothendieckTopology

/- The source-facing opens-covering pretopology induces that canonical Grothendieck topology. -/
recall Opens.pretopology_toGrothendieck

/- For a presheaf on a topological space, the site-theoretic sheaf condition for the opens site is
equivalent to the usual open-cover sheaf condition. -/
recall TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover

/-! ### Example_7_6_5 (from Chap07) -/
open CategoryTheory

universe u

/- Domain-style sampling for Example 7.6.5:
- primary domain: source-facing sites presented by a `Precoverage`, specialized to the category
  `Action (Type u) G` of universe-sized `G`-sets;
- sampled owner API:
  `CategoryTheory.Precoverage`,
  `Types.jointlySurjectivePrecoverage`,
  `Presieve.mem_comap_jointlySurjectivePrecoverage_iff`,
  `Scheme.jointlySurjectivePrecoverage` / `Scheme.jointlySurjectiveTopology`;
- best owner abstraction: the primitive owner is the pulled-back jointly surjective
  `Precoverage`; the Grothendieck topology is derived from that owner by
  `Precoverage.toGrothendieck`, so it should not be stored as independent primitive data;
- source/core/bridge triage:
  `source-facing`: the jointly surjective covering families on `G`-sets and the associated site;
  `core/canonical`: `Precoverage` and `Precoverage.toGrothendieck`;
  `bridge/view`: the pointwise topology-membership characterization below.

This refinement follows the existing mathlib owner pattern for surjective sites by placing the
`G`-set site in the `Action` namespace, deleting the file-local `tG...` wrappers, and exposing the
primitive precoverage first and the derived topology second.
-/

namespace Action

section

variable (G : Type u) [Group G]

/- Example 7.6.5: the source first replaces the proper-class category `G-Sets` by a
size-restricted full subcategory `G-Sets_α`, then equips it with the jointly surjective
coverings. In Lean the universe-sized category `Action (Type u) G` is the corresponding
size-restricted category of `G`-sets, and the pulled-back jointly surjective precoverage is the
canonical restricted covering class from which the site is generated. -/

/-- The primitive covering families for Example 7.6.5: presieves on the universe-sized category
of `G`-sets whose underlying maps are jointly surjective. This is the source-facing owner
abstraction; the Grothendieck topology is derived from it. -/
abbrev jointlySurjectivePrecoverage : Precoverage (Action (Type u) G) :=
  Types.jointlySurjectivePrecoverage.comap (Action.forget (Type u) G)

/-- Example 7.6.5: the site `\mathcal T_G` on `G`-sets is the Grothendieck topology generated by
jointly surjective families of equivariant maps, modeled in Lean on the universe-sized category
`Action (Type u) G`. -/
abbrev jointlySurjectiveTopology : GrothendieckTopology (Action (Type u) G) :=
  (jointlySurjectivePrecoverage G).toGrothendieck

-- Proof sketch: the Grothendieck topology generated by `jointlySurjectivePrecoverage` is
-- covering exactly when the sieve contains a jointly surjective family, and the canonical comap
-- theorem identifies those families pointwise.
/-- A sieve on a `G`-set is covering for `\mathcal T_G` exactly when its arrows are jointly
surjective on the underlying set. -/
theorem mem_jointlySurjectiveTopology_iff
    {X : Action (Type u) G} {R : Sieve X} :
    R ∈ jointlySurjectiveTopology G X ↔
      ∀ x : X.V, ∃ (Y : Action (Type u) G) (f : Y ⟶ X), R f ∧ x ∈ Set.range f.hom :=
  by
    -- Reduce Grothendieck-topology membership to the existence of a covering presieve below `R`.
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := jointlySurjectivePrecoverage G) (S := R)]
    constructor
    · rintro ⟨R₀, hR₀, hR₀R⟩ x
      -- Convert the covering presieve witness into the pointwise jointly surjective formulation.
      have hsurj :
          ∀ x : X.V, ∃ (Y : Action (Type u) G) (f : Y ⟶ X), R₀ f ∧ x ∈ Set.range f.hom := by
        simpa [jointlySurjectivePrecoverage, Action.forget_obj, Action.forget_map] using
          (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
            (F := Action.forget (Type u) G) (X := X) (R := R₀)).1 hR₀
      -- Enlarge the jointly surjective subfamily from `R₀` to the ambient sieve `R`.
      rcases hsurj x with ⟨Y, f, hf, hx⟩
      exact ⟨Y, f, hR₀R Y f hf, hx⟩
    · intro hR
      -- The sieve itself is already jointly surjective, so it can serve as the covering witness.
      refine ⟨R, ?_, le_rfl⟩
      simpa [jointlySurjectivePrecoverage, Action.forget_obj, Action.forget_map] using
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
          (F := Action.forget (Type u) G) (X := X) (R := R)).2 hR

end

end Action

/-! ### Example_7_6_6 (from Chap07) -/
universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A]

/- Domain-style sampling for Example 7.6.6:
- primary domain: chaotic Grothendieck topologies and the associated sheaf categories;
- sampled canonical declarations:
  `GrothendieckTopology.trivial`,
  `GrothendieckTopology.trivial_eq_bot`,
  `sheafBotEquivalence`,
  `Pretopology.trivial`;
- best owner abstraction:
  the source-facing chaotic site is owned canonically at the topology layer by
  `GrothendieckTopology.trivial C`, while `Pretopology.trivial` is only the stronger pullback-based
  presentation available when pullbacks exist;
- source/core/bridge triage:
  `source-facing`: the chaotic topology on `C` and its sheaf category;
  `core/canonical`: `GrothendieckTopology.trivial` together with `sheafBotEquivalence`;
  `bridge/view`: `GrothendieckTopology.trivial_eq_bot`, which identifies the source-facing chaotic
    topology with the bottom topology used by `sheafBotEquivalence`.

Primitive data are only the category `C` and the target category `A`. The induced sheaf category
equivalence is derived from the canonical topology owner, so the local `Coverage` presentation is
duplicate wheel data and should be deleted rather than preserved as a parallel owner.
-/

/- Example 7.6.6: the chaotic site on `C` is the canonical trivial Grothendieck topology. -/
recall GrothendieckTopology.trivial

/- Example 7.6.6: sheaves on the chaotic topology on `C` with values in `A` are canonically
equivalent to `A`-valued presheaves on `C`. This is the bottom-topology equivalence specialized
along `GrothendieckTopology.trivial_eq_bot`. -/
#check
  (show Sheaf (GrothendieckTopology.trivial C) A ≌ Cᵒᵖ ⥤ A from by
    simpa [GrothendieckTopology.trivial_eq_bot] using (sheafBotEquivalence A))

end CategoryTheory
