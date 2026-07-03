import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Plus
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_10_1 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (I : Type w) [Category I] [Small.{max u v} I]

/- Source/core/bridge triage for Lemma 7.10.1:
- sampled upstream declarations in the same domain:
  `sheafToPresheaf`, `Sheaf.createsLimitsOfShape`,
  `hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape`,
  `preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape`
- source-facing content: the forgetful functor from set-valued sheaves on `(C, J)` to presheaves
  creates `I`-shaped limits
- core/canonical owner: `Sheaf.createsLimitsOfShape`
- bridge/view: the `Type (max u v)` specialization and the induced `HasLimitsOfShape` instance on
  `Sheaf J (Type (max u v))`, together with the induced preservation statement for
  `sheafToPresheaf J (Type (max u v))`
- primitive data: the site `(C, J)` and the diagram shape `I`
- derived API: existence of `I`-shaped limits in the sheaf category, obtained from the owner
  instance together with limits in `Type`
-/
/- Lemma 7.10.1 targets the source-facing specialization of the canonical owner:
for set-valued sheaves on `(C, J)`, the forgetful functor to presheaves creates `I`-shaped
limits. -/
#check (inferInstance : CreatesLimitsOfShape I (sheafToPresheaf J (Type (max u v))))

/- Core/canonical owner recall behind the specialized statement above. -/
recall Sheaf.createsLimitsOfShape

/- Companion derived API: since `Type (max u v)` has `I`-shaped limits, the sheaf category
`Sheaf J (Type (max u v))` inherits them. -/
#check (inferInstance : HasLimitsOfShape I (Sheaf J (Type (max u v))))

/- The owner instance also implies that the forgetful functor computes these limits on underlying
presheaves. -/
#check (inferInstance : PreservesLimitsOfShape I (sheafToPresheaf J (Type (max u v))))

/-! ### Example_7_10_2 (from Chap07) -/
universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

namespace TerminalPresheaf

/- Lean surface notation for the singleton terminal presheaf `*`. We write `*ₚ[C]` to keep the
presheaf and sheaf surfaces distinct while still exposing the source-facing star notation. -/
set_option quotPrecheck false in
scoped notation:max "*ₚ[" C "]" => (Functor.const Cᵒᵖ).obj PUnit

end TerminalPresheaf

namespace TerminalSheaf

/- Lean surface notation for the singleton terminal sheaf `*` on the site `(C, J)`. -/
scoped notation:max "*[" J "]" => Sheaf.terminal J Types.isTerminalPUnit

end TerminalSheaf

open scoped TerminalPresheaf TerminalSheaf

/- Domain-style sampling for Example 7.10.2:
- primary domain: terminal objects in presheaf and sheaf categories on a Grothendieck site;
- sampled owner API:
  `Functor.isTerminalConst`,
  `Presheaf.isSheaf_of_isTerminal`,
  `Sheaf.terminal`,
  `Sheaf.isTerminalTerminal`;
- best owner abstraction: the terminal-object owner API for the constant presheaf and the induced
  terminal sheaf on `(C, J)`, with source-facing `*` notation implemented directly as scoped
  notation over those canonical constructions;
- source/core/bridge triage:
  `source-facing`: the singleton-valued presheaf `*ₚ[C]` and sheaf `*[J]`;
  `core/canonical`: `Functor.isTerminalConst`, `Presheaf.isSheaf_of_isTerminal`,
    `Sheaf.terminal`, and `Sheaf.isTerminalTerminal`;
  `bridge/view`: the scoped notation `*ₚ[C]` and `*[J]`, which expose the source-facing star
  surface directly over the owner-level canonical constructions.

- primitive data: only the terminal object `PUnit` in `Type _`;
- derived API: terminality in presheaves, the sheaf condition, the bundled terminal sheaf, and its
  terminality in `Sheaf J (Type _)`.

The only new declarations below are the scoped notations `*ₚ[C]` and `*[J]`, exposing the
recurring source-facing object `*` without introducing parallel owner names.
-/
/- Example 7.10.2: the constant singleton-valued presheaf on `C` is terminal in the presheaf
category. This is owned canonically by `Functor.isTerminalConst`. -/
recall Functor.isTerminalConst

/- Companion specialization: the terminal presheaf `*ₚ[C]` is the constant presheaf with value
`PUnit`. -/
#check (show IsTerminal *ₚ[C] from Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit)

/- Example 7.10.2: because a terminal presheaf is a sheaf, the constant singleton-valued
presheaf satisfies the sheaf condition for every Grothendieck topology `J`. This is owned
canonically by `Presheaf.isSheaf_of_isTerminal`. -/
recall Presheaf.isSheaf_of_isTerminal

/- Companion specialization: the terminal presheaf `*ₚ[C]` is a sheaf on `(C, J)`. -/
#check (show Presheaf.IsSheaf J *ₚ[C] from Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)

/- Example 7.10.2: the sheaf `*[J]` is the canonical terminal singleton sheaf on `(C, J)`. -/
recall Sheaf.terminal

/- Companion specialization: on the site `(C, J)`, the singleton sheaf `*[J]` is the canonical
terminal sheaf. -/
#check (*[J] : Sheaf J (Type (max u v)))

/- Example 7.10.2: the sheaf `*[J]` is terminal in the category of sheaves on the site `(C, J)`.
This is owned canonically by
`Sheaf.isTerminalTerminal`. -/
recall Sheaf.isTerminalTerminal

/- Companion specialization: the singleton sheaf `*[J]` is terminal in `Sheaf J (Type _)`. -/
#check (show IsTerminal *[J] from Sheaf.isTerminalTerminal J Types.isTerminalPUnit)

end CategoryTheory

/-! ### Lemma_7_10_3 (from Chap07) -/
open CategoryTheory Opposite
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 7.10.3:
- primary domain: the plus construction for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.plusObj`,
  `CategoryTheory.GrothendieckTopology.toPlus`,
  `CategoryTheory.GrothendieckTopology.toPlusNatTrans`,
  `CategoryTheory.Presheaf.isLocallySurjective_toPlus`;
- source-facing layer: the source introduces the plus construction `P ↦ P⁺` and its canonical map;
- core/canonical owner: `J.plusObj P` and `J.toPlus P`;
- bridge/view: the functorial packaging `J.plusFunctor` and `J.toPlusNatTrans`.

Primitive data are only the topology `J` and the presheaf `P`. The map `J.toPlus P` is derived
from the owner construction, so this file should remain a direct recall of the canonical API
rather than introduce a local wrapper.
-/
/-
Lemma 7.10.3: the plus construction on a set-valued presheaf `P` canonically gives the presheaf
`P⁺`.
-/
#check P⁺

/- Companion recall: the plus construction comes with the canonical map of presheaves
`J.toPlus P : P ⟶ P⁺`. -/
#check J.toPlus P

/-! ### Lemma_7_10_4 (from Chap07) -/
open CategoryTheory Opposite

universe v u

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling:
- primary domain: the plus construction on set-valued presheaves over a Grothendieck topology;
- sampled owner API:
  `GrothendieckTopology.plusFunctor`,
  `GrothendieckTopology.toPlus_naturality`,
  `GrothendieckTopology.toPlusNatTrans`;
- best owner abstraction: `GrothendieckTopology.toPlusNatTrans`, the natural transformation from
  the identity functor to the plus functor;
- source/core/bridge triage:
  `source-facing`: the functoriality of the canonical maps `J.toPlus P : P ⟶ J.plusObj P`;
  `core/canonical`: `GrothendieckTopology.toPlusNatTrans`;
  `bridge/view`: the componentwise naturality equation
    `GrothendieckTopology.toPlus_naturality`;
- primitive data: the topology `J`;
- derived API: the component maps `J.toPlus P` and their functoriality, packaged canonically by
  `J.toPlusNatTrans`; in the `Type`-valued specialization used here, the plus-construction
  (co)limit assumptions are discharged by existing instances and should not remain as explicit
  public hypotheses.
-/

/- Lemma 7.10.4: the assignment `ℱ ↦ (J.toPlus ℱ : ℱ ⟶ J.plusObj ℱ)` is functorial for
set-valued presheaves. Canonically, this is the `Type`-valued specialization of the natural
transformation from the identity functor to the plus functor; the commutative square for a
morphism `η : ℱ ⟶ 𝒢` is the componentwise naturality equation `J.toPlus_naturality η`. -/
#check
  (J.toPlusNatTrans (Type (max u v)) :
    𝟭 (Cᵒᵖ ⥤ Type (max u v)) ⟶ J.plusFunctor (Type (max u v)))

end

/-! ### Lemma_7_10_5 (from Chap07) -/
universe w₁ w₂ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
  [J.IsStableUnderComposition]

open Limits
open Precoverage

namespace SemiRepresentableFamily
namespace Over

variable {U : C}

/- Domain-style sampling for Lemma 7.10.5:
- primary domain: precoverage covering families and common refinements;
- sampled owner API:
  `Precoverage.ZeroHypercover`,
  `Precoverage.ZeroHypercover.inter`,
  `PreZeroHypercover.interFst`,
  `PreZeroHypercover.interSnd`;
- source/core/bridge triage:
  `source-facing`: the existence of a common covering refinement of two fixed-target families;
  `core/canonical`: `J.ZeroHypercover U` together with its canonical intersection cover;
  `bridge/view`: the comparison between a covering family and the canonical intersection
  construction on `J.ZeroHypercover U`.

Primitive data are only the two covering families and their covering proofs. The common refinement
is derived from `ZeroHypercover.inter`, so the public statement should stay at the level of the
covering-family API rather than introducing extra wrapper data.
-/

-- Proof sketch: view each covering family as a `0`-hypercover, take the canonical intersection
-- `𝒰.inter 𝒱`, and translate its two projection morphisms back to refinement morphisms of
-- fixed-target families.
/-- Helper for Lemma 7.10.5: a fixed-target family is covering for a precoverage when its
generated presieve belongs to that precoverage. -/
abbrev IsCovering (K : Precoverage C) (𝒰 : Over U) : Prop :=
  𝒰.toPresieve ∈ K U

/-- Lemma 7.10.5: two covering fixed-target families over `U` admit a common covering
refinement. -/
theorem exists_covering_family_common_refinement {U : C}
    (𝒰 𝒱 : Over U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ (𝒲 : Over U) (_ : IsCovering J 𝒲), Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := by
  let E : J.ZeroHypercover U :=
    { I₀ := 𝒰.index
      X := fun i ↦ (𝒰.obj i).left
      f := fun i ↦ (𝒰.obj i).hom
      mem₀ := h𝒰 }
  let F : J.ZeroHypercover U :=
    { I₀ := 𝒱.index
      X := fun i ↦ (𝒱.obj i).left
      f := fun i ↦ (𝒱.obj i).hom
      mem₀ := h𝒱 }
  -- Each pair of covering arrows admits a pullback, so the canonical intersection exists.
  have hpull :
      ∀ i : E.I₀, ∀ j : F.I₀, HasPullback (E.f i) (F.f j) := by
    intro i j
    letI : F.presieve₀.HasPullbacks (E.f i) :=
      J.hasPullbacks_of_mem (E.f i) F.mem₀
    letI : HasPullback (F.f j) (E.f i) :=
      Presieve.HasPullbacks.hasPullback (R := F.presieve₀) (f := E.f i) (h := F.f j) (by
        exact ⟨j⟩)
    exact hasPullback_symmetry (F.f j) (E.f i)
  letI : ∀ i : E.I₀, ∀ j : F.I₀, HasPullback (E.f i) (F.f j) := hpull
  let W₀ : J.ZeroHypercover U := E.inter F
  let 𝒲 : Over U :=
    { index := W₀.I₀
      obj := fun i ↦ CategoryTheory.Over.mk (W₀.f i) }
  let π₁ : W₀.toPreZeroHypercover.Hom E.toPreZeroHypercover :=
    PreZeroHypercover.interFst E.toPreZeroHypercover F.toPreZeroHypercover
  let π₂ : W₀.toPreZeroHypercover.Hom F.toPreZeroHypercover :=
    PreZeroHypercover.interSnd E.toPreZeroHypercover F.toPreZeroHypercover
  -- The pullback-intersection hypercover is covering by the base-change and composition axioms.
  have h𝒲 : IsCovering J 𝒲 := by
    simpa [IsCovering, toPresieve, 𝒲] using W₀.mem₀
  -- The first pullback projection sends each intersection term to the corresponding `𝒰`-member.
  have hRefines𝒰 : Refines 𝒲 𝒰 := by
    refine ⟨{ α := π₁.s₀, f := fun i ↦ CategoryTheory.Over.homMk (π₁.h₀ i) (π₁.w₀ i) }⟩
  -- The second pullback projection does the same for the family `𝒱`.
  have hRefines𝒱 : Refines 𝒲 𝒱 := by
    refine ⟨{ α := π₂.s₀, f := fun i ↦ CategoryTheory.Over.homMk (π₂.h₀ i) (π₂.w₀ i) }⟩
  exact ⟨𝒲, h𝒲, hRefines𝒰, hRefines𝒱⟩

end Over
end SemiRepresentableFamily

end CategoryTheory

/-! ### Lemma_7_10_6 (from Chap07) -/
open CategoryTheory

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {P : Cᵒᵖ ⥤ Type w}

/- Domain-style sampling for Lemma 7.10.6:
- primary domain: matching families for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Meq`,
  `CategoryTheory.GrothendieckTopology.Meq.refine`,
  `CategoryTheory.GrothendieckTopology.Meq.pullback`,
  `CategoryTheory.GrothendieckTopology.Meq.pullback_refine`,
  `CategoryTheory.GrothendieckTopology.Cover.pullback`;
- source-facing layer: the Stacks lemma says that the induced pullback map on matching families
  depends only on the base morphism `h : U ⟶ V`, not on a chosen refinement witness;
- core/canonical owner: matching families `Meq P 𝒱` with the canonical operations `refine`,
  `pullback`, and the interchange theorem `pullback_refine`;
- bridge/view layer: the textbook pullback statement below is a specialization of the owner-level
  witness-independence of `Meq.refine`;
- primitive data: a matching family `x : Meq P 𝒱` and a refinement morphism between covers;
- derived API: the pullback specialization along `h : U ⟶ V`.

No extra wrapper structure is warranted: the statement should live directly on the owner namespace
`Meq`.
-/

namespace Meq

-- Proof sketch: a morphism of covers is unique when it exists, so refining along two such
-- morphisms gives the same matching family.
/-- Helper for Lemma 7.10.6: two morphisms between the same covers are equal because
`J.Cover U` is a thin category. -/
theorem refinement_hom_eq {U : C} {𝒰 𝒱 : J.Cover U} (e e' : 𝒰 ⟶ 𝒱) :
    e = e' := by
  -- A hom between fixed covers is unique, so the two refinement witnesses coincide.
  exact Subsingleton.elim e e'

/-- Helper for Lemma 7.10.6: refining a matching family along a morphism of covers depends only
on the source and target covers, not on the chosen morphism. -/
theorem refine_eq {U : C} {𝒰 𝒱 : J.Cover U} (x : Meq P 𝒱) (e e' : 𝒰 ⟶ 𝒱) :
    x.refine e = x.refine e' := by
  -- Replace one refinement witness by the other and transport the equality through `refine`.
  simpa using congrArg (fun φ ↦ x.refine φ) (refinement_hom_eq (J := J) e e')

-- Lemma 7.10.6 is the pullback specialization of `refine_eq`.
/-- Lemma 7.10.6: for a matching family on `𝒱`, refining its pullback along `h : U ⟶ V` is
independent of the chosen morphism `𝒰 ⟶ 𝒱.pullback h`. -/
theorem pullback_refine_eq
    {U V : C} {𝒰 : J.Cover U} {𝒱 : J.Cover V}
    (x : Meq P 𝒱) (h : U ⟶ V) (e e' : 𝒰 ⟶ 𝒱.pullback h) :
    (x.pullback h).refine e = (x.pullback h).refine e' := by
  -- The pullback case is exactly the same witness-independence statement for the cover `𝒱.pullback h`.
  simpa using (refine_eq (J := J) (x := x.pullback h) e e')

end Meq

end CategoryTheory.GrothendieckTopology

/-! ### Remark_7_10_7 (from Chap07) -/
universe w v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] CategoryTheory.Types.instFunLike
attribute [local instance] CategoryTheory.Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : C} {P : Cᵒᵖ ⥤ Type w}
variable {𝒰 𝒱 : J.Cover X}

/-
Domain-style sampling for Remark 7.10.7:
- primary domain: matching families for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Cover`,
  `CategoryTheory.leOfHom`,
  `CategoryTheory.GrothendieckTopology.Meq`,
  `Equiv.cast`;
- source/core/bridge triage:
  `source-facing`: mutually refining covers define the same matching-family model for `H^0`;
  `core/canonical`: `J.Cover X` is the owner poset of covers, with equality supplied by
    antisymmetry from the refinement morphisms, and `Meq P` is the dependent owner family over
    that poset;
  `bridge/view`: the canonical identification below is transport of `Meq P` along that equality
    via `Equiv.cast`.

Primitive data are only the two refinement morphisms `𝒰 ⟶ 𝒱` and `𝒱 ⟶ 𝒰`. The equivalence of
matching-family types is derived API from equality in `J.Cover X`, so no parallel public
cover-equality wrapper is needed here beyond the canonical antisymmetry step.
-/
namespace Meq

/-- Remark 7.10.7: if the covers `𝒰` and `𝒱` refine each other, then they are equal in the
poset `J.Cover X`, so the matching-family types `Meq P 𝒰` and `Meq P 𝒱`, which model
`H^0(𝒰, P)` and `H^0(𝒱, P)`, are canonically identified. -/
def equivOfMutualRefinements
    (h𝒰𝒱 : 𝒰 ⟶ 𝒱) (h𝒱𝒰 : 𝒱 ⟶ 𝒰) :
    Meq P 𝒰 ≃ Meq P 𝒱 :=
  Equiv.cast <| congrArg (Meq P) <| le_antisymm (leOfHom h𝒰𝒱) (leOfHom h𝒱𝒰)

/-- The equivalence from mutually refining covers is transport of matching families along the
equality of covers induced by antisymmetry. -/
-- Proof sketch: unfold `equivOfMutualRefinements`; both sides are definitionally the same
-- transport equivalence given by `Equiv.cast`.
theorem equivOfMutualRefinements_def
    (h𝒰𝒱 : 𝒰 ⟶ 𝒱) (h𝒱𝒰 : 𝒱 ⟶ 𝒰) :
    equivOfMutualRefinements h𝒰𝒱 h𝒱𝒰 =
      Equiv.cast (congrArg (Meq P) (le_antisymm (leOfHom h𝒰𝒱) (leOfHom h𝒱𝒰))) := by
  -- Unfold the canonical identification to expose the underlying transport equivalence.
  rfl

end Meq

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_10_8 (from Chap07) -/
open CategoryTheory Opposite

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (ℱ : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 7.10.8:
- primary domain: the plus construction and local surjectivity for set-valued presheaves on a
  Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.plusObj`,
  `CategoryTheory.GrothendieckTopology.toPlus`,
  `CategoryTheory.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Presheaf.isLocallySurjective_toPlus`;
- best owner abstraction: the canonical predicate `Presheaf.IsLocallySurjective J` applied to the
  canonical plus map `J.toPlus ℱ`;
- source/core/bridge triage:
  `source-facing`: the textbook lemma says the canonical map `ℱ ⟶ ℱ⁺` is locally surjective;
  `core/canonical`: the owner constructions `J.plusObj ℱ`, `J.toPlus ℱ`, and the predicate
    `Presheaf.IsLocallySurjective J`;
  `bridge/view`: the canonical derived instance
    `Presheaf.isLocallySurjective_toPlus J ℱ`.
- primitive data: only `J` and `ℱ`;
- derived API: the plus object `J.plusObj ℱ`, the canonical map `J.toPlus ℱ`, and the instance
  `Presheaf.isLocallySurjective_toPlus J ℱ`.

No local wrapper or chapter-level restatement should remain here: this item is already best
expressed as a direct recall of the owner instance.
-/
/- Lemma 7.10.8: the canonical map `θ : ℱ ⟶ ℱ⁺`, namely `J.toPlus ℱ` with `ℱ⁺ = J.plusObj ℱ`, is
locally surjective. Equivalently, for every object `U` and every section `s ∈ ℱ⁺(U)`, there
exists a covering of `U` on which the restriction of `s` lies in the image of `θ`. -/
recall Presheaf.isLocallySurjective_toPlus :
  Presheaf.IsLocallySurjective J (J.toPlus ℱ)

end

/-! ### Definition_7_10_9 (from Chap07) -/
universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for Definition 7.10.9:
- primary domain: separated presheaves of sets on a Grothendieck site;
- sampled canonical declarations:
  `Presieve.IsSeparatedFor`,
  `Presieve.IsSeparated`,
  `Presieve.IsSheaf.isSeparated`,
  `Presheaf.IsSeparated`;
- source/core/bridge triage:
  `core/canonical`: `Presieve.IsSeparated J F`,
  `bridge/view`: coverwise injectivity criteria such as the plus-construction lemmas.

Primitive data are only the site `(C, J)` and the set-valued presheaf `F`. The coverwise
restriction-map injectivity formulation is derived directly from the defining body of
`Presieve.IsSeparated`. The broader concrete-category predicate `Presheaf.IsSeparated` is not the
owner here, because the source item and the downstream plus API are specifically set-valued.
Accordingly, no separate chapter-level owner or wrapper theorem is kept here.
-/

/- Definition 7.10.9: for a site `(C, J)`, the source-facing owner notion that a set-valued
presheaf `F` is separated is the canonical predicate `Presieve.IsSeparated`. -/
recall Presieve.IsSeparated

/- Source-facing specialization: separatedness of `F` on `(C, J)` is expressed directly as the
proposition `Presieve.IsSeparated J F`. -/
#check (Presieve.IsSeparated J F : Prop)

end CategoryTheory.Presheaf

/-! ### Theorem_7_10_10 (from Chap07) -/
-- Route correction: the previous local `PlusNotation` shim is unavailable in this item-per-file
-- target, so we use the canonical owner notation-free form `J.plusObj ℱ` directly.

open CategoryTheory Opposite
open GrothendieckTopology Plus

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (ℱ : Cᵒᵖ ⥤ Type (max u v))

/-- Helper for Theorem 7.10.10: a separated presheaf is injective against any covering family of
restrictions. -/
private theorem eq_of_restrict_eq_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ ⦃X : C⦄ (S : J.Cover X) (x y : ℱ.obj (op X)),
      (∀ I : S.Arrow, ℱ.map I.f.op x = ℱ.map I.f.op y) → x = y := by
  -- Turn the covering family into the sieve-level separatedness predicate supplied by `hℱ`.
  intro X S x y hxy
  exact (hℱ S S.condition).ext fun Y f hf ↦ hxy ⟨Y, f, hf⟩

-- Proof sketch: use the explicit separatedness criterion proved by `Plus.sep`, which exactly
-- says that two sections of `J.plusObj ℱ`
-- agreeing after restriction to a covering must already be equal.
/-- Theorem 7.10.10 (1): the plus construction `J.plusObj ℱ` of a presheaf of sets is
separated. -/
theorem plusObj_isSeparated :
    Presieve.IsSeparated J (J.plusObj ℱ) := by
  -- `Plus.sep` is the packaged common-refinement argument from the source proof.
  intro U S hS x t₁ t₂ ht₁ ht₂
  exact Plus.sep ℱ ⟨S, hS⟩ t₁ t₂ fun I ↦ (ht₁ I.f I.hf).trans (ht₂ I.f I.hf).symm

-- Proof sketch: unpack `Presieve.IsSeparated J ℱ` into the coverwise injectivity hypothesis used
-- by `Plus.isSheaf_of_sep`, and then apply that theorem directly.
/-- Theorem 7.10.10 (2), first assertion: if `ℱ` is separated, then `J.plusObj ℱ` is a sheaf. -/
theorem plusObj_isSheaf_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Presheaf.IsSheaf J (J.plusObj ℱ) := by
  -- Feed the bridge lemma into the owner theorem implementing the gluing argument.
  exact Plus.isSheaf_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: `Plus.inj_of_sep` gives the objectwise injectivity statement for `J.toPlus ℱ`
-- once we feed it the coverwise separatedness condition coming directly from `hℱ`.
/-- Theorem 7.10.10 (2), second assertion: if `ℱ` is separated, then the canonical map
`ℱ ⟶ J.plusObj ℱ` is injective in the sense of Definition 7.3.1. -/
theorem toPlus_injective_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ U : C, Function.Injective ((J.toPlus ℱ).app (op U)) := by
  -- This is exactly the objectwise injectivity statement owned by `Plus.inj_of_sep`.
  exact Plus.inj_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: Definition 7.3.1 already identifies the objectwise injectivity statement with the
-- canonical owner `Mono`.
/-- Companion to Theorem 7.10.10 (2): if `ℱ` is separated, then the canonical map
`ℱ ⟶ J.plusObj ℱ` is a monomorphism of presheaves. -/
theorem toPlus_mono_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Mono (J.toPlus ℱ) := by
  -- Translate the objectwise injectivity result into the categorical monomorphism criterion.
  exact (Presheaf.mono_iff_injective (J.toPlus ℱ)).2
    (toPlus_injective_of_isSeparated J ℱ hℱ)

/- Theorem 7.10.10 (3): if `ℱ` is already a sheaf, then the canonical map `ℱ ⟶ J.plusObj ℱ` is an
isomorphism. This is exactly the canonical owner theorem
`GrothendieckTopology.isIso_toPlus_of_isSheaf`. -/
recall GrothendieckTopology.isIso_toPlus_of_isSheaf

/- Theorem 7.10.10 (4): the iterated plus construction `J.plusObj (J.plusObj ℱ)` is always a
sheaf. This is exactly the canonical owner theorem
`GrothendieckTopology.Plus.isSheaf_plus_plus`. -/
recall GrothendieckTopology.Plus.isSheaf_plus_plus

end

/-! ### Definition_7_10_11 (from Chap07) -/
open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Source/core/bridge triage for Definition 7.10.11:
- source-facing content: the associated sheaf `P^#` of a set-valued presheaf `P` on `(C, J)`;
- core/canonical owner: `presheafToSheaf J (Type (max u v))`;
- derived API: the underlying sheafification `J.sheafify P` and the unit `J.toSheafify P`.

The source item only recalls the canonical sheafification owner, so this file keeps the public
surface at that owner and records the underlying presheaf and unit map only as companion views.
-/
/- Definition 7.10.11: the associated sheaf `P^#` of a set-valued presheaf `P` on the site
`(C, J)` is the image of `P` under the canonical sheafification functor
`presheafToSheaf J (Type (max u v))`. -/
recall presheafToSheaf

/- Source-facing specialization: `P^#` is the bundled sheaf obtained by applying the
sheafification functor to `P`. -/
#check (presheafToSheaf J (Type (max u v))).obj P

/- Companion recall: the underlying-presheaf owner is `GrothendieckTopology.sheafify`. -/
recall GrothendieckTopology.sheafify

/- Companion recall: the underlying presheaf of `P^#` is the canonical sheafification
`J.sheafify P`, implemented in mathlib by the usual plus-plus construction. -/
#check J.sheafify P

/- Companion recall: the unit owner is `GrothendieckTopology.toSheafify`. -/
recall GrothendieckTopology.toSheafify

/- Companion recall: the canonical map from `P` to the underlying presheaf of `P^#` is the
sheafification unit `J.toSheafify P : P ⟶ J.sheafify P`. -/
#check J.toSheafify P

/-! ### Proposition_7_10_12 (from Chap07) -/
open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
variable (P : Cᵒᵖ ⥤ Type (max u v)) (𝒢 : Sheaf J (Type (max u v)))

/- Domain-style sampling for Proposition 7.10.12:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site, specifically the
  universal property of the sheafification unit;
- sampled owner declarations:
  `sheafificationAdjunction`,
  `GrothendieckTopology.toSheafify`,
  `GrothendieckTopology.sheafifyLift`,
  `GrothendieckTopology.sheafifyLift_unique`;
- best owner abstraction: the sheafification adjunction Hom-set equivalence
  `((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢)`;
- primitive data: the presheaf `P` and the sheaf `𝒢`;
- derived API: the factorization morphism `J.sheafifyLift`, its compatibility with the unit
  `J.toSheafify_sheafifyLift`, and the uniqueness theorem `J.sheafifyLift_unique`.

The source proposition is therefore a `bridge/view` statement whose mathematically canonical owner
is the adjunction equivalence, not a separate local universal-property wrapper.
-/
/- Source/core/bridge triage for Proposition 7.10.12:
- source-facing content: the sheafification unit `J.toSheafify P` is universal for maps from `P`
  to sheaves of sets
- core/canonical owner: the sheafification adjunction Hom-set equivalence
  `((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢)`
- bridge/view: the explicit factorization map `J.sheafifyLift` together with
  `J.toSheafify_sheafifyLift` and `J.sheafifyLift_unique`
- primitive data: the presheaf `P` and the sheaf `𝒢`
- derived API: the unique factorization through `J.toSheafify P`
-/
/- Proposition 7.10.12: the sheafification unit `J.toSheafify P : P ⟶ J.sheafify P` is universal
for maps from `P` to sheaves of sets. The canonical owner-level form is the sheafification
adjunction, and the source-facing universal property is the derived bridge API consisting of
`J.sheafifyLift`, `J.toSheafify_sheafifyLift`, and `J.sheafifyLift_unique`. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.toSheafify
recall CategoryTheory.sheafifyLift
recall CategoryTheory.toSheafify_sheafifyLift
recall CategoryTheory.sheafifyLift_unique

variable {P 𝒢}

/- Owner-level form: the sheafification adjunction Hom-set equivalence. -/
#check (((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢) :
  ((presheafToSheaf J _).obj P ⟶ 𝒢) ≃
    (P ⟶ 𝒢.obj))

/- Source-facing factorization: a map `φ : P ⟶ 𝒢.obj` uniquely lifts through `J.toSheafify P`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ J.sheafifyLift φ 𝒢.property :
  (P ⟶ 𝒢.obj) → (J.sheafify P ⟶ 𝒢.obj))

/- The factorization equation is exactly `toSheafify_sheafifyLift`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ J.toSheafify_sheafifyLift φ 𝒢.property :
  ∀ φ : P ⟶ 𝒢.obj, J.toSheafify P ≫ J.sheafifyLift φ 𝒢.property = φ)

/- Uniqueness is exactly `sheafifyLift_unique`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ fun γ : J.sheafify P ⟶ 𝒢.obj ↦
    J.sheafifyLift_unique φ 𝒢.property γ)

end

/-! ### Example_7_10_13 (from Chap07) -/
universe u v

namespace CategoryTheory

open Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section

variable [HasWeakSheafify J (Type (max u v))]
variable (E : Type (max u v)) (F : Sheaf J (Type (max u v)))

/- Domain-style sampling for Example 7.10.13:
- primary domain: constant sheaves and global sections on a site;
- sampled owner API:
  `CategoryTheory.constantSheaf`,
  `CategoryTheory.HasGlobalSectionsFunctor`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.constantSheafΓAdj`;
- best owner abstraction: the adjunction `constantSheafΓAdj J (Type (max u v))`
  between the constant-sheaf functor and the global-sections functor;
- primitive data: the site `(C, J)`, the value `E : Type (max u v)`, and the sheaf `F`;
- derived API: the Hom-set bijection exported by
  `(constantSheafΓAdj J (Type (max u v))).homEquiv`.

Source/core/bridge triage:
- `source-facing`: the constant sheaf with value `E` and the bijection
  `Mor(underline E, F) = Mor_Sets(E, Γ(C, F))`;
- `core/canonical`: `constantSheaf` and `Γ`, organized by the adjunction
  `constantSheafΓAdj`;
- `bridge/view`: the source-text bijection is the `homEquiv` of `constantSheafΓAdj`.

This file therefore targets the `bridge/view` layer: the source statement carries no extra data
past the canonical constant-sheaf/global-sections adjunction, so the correct refinement is direct
recall of the owner declarations and their `homEquiv`, not a local duplicate wrapper.
-/

/- Example 7.10.13: for a site `(C, J)`, the constant sheaf with value `E` is the canonical
mathlib construction `CategoryTheory.constantSheaf J (Type (max u v))` specialized at `E`; by
definition this is the sheafification of the constant presheaf with value `E`. -/
recall constantSheaf

/- Example 7.10.13: the global-sections functor on `Type`-valued sheaves is the canonical owner
`CategoryTheory.Sheaf.Γ J (Type (max u v))`, defined whenever the constant-sheaf functor admits a
right adjoint; for `Type`, this exists from the standard limits-based instance. -/
recall Sheaf.Γ

/- Example 7.10.13: the mathematical core of the characterization of the constant sheaf is the
constant-sheaf/global-sections adjunction. Specializing `constantSheafΓAdj.homEquiv` for
`constantSheafΓAdj J (Type (max u v))` recovers the source-text bijection
`Mor(underline E, F) = Mor_Sets(E, Γ(C, F))`. -/
recall constantSheafΓAdj

#check ((constantSheafΓAdj J (Type (max u v))).homEquiv E F :
  ((constantSheaf J (Type (max u v))).obj E ⟶ F) ≃
    (E ⟶ (Γ J (Type (max u v))).obj F))

end

end CategoryTheory

/-! ### Lemma_7_10_14 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (I : Type w) [Category I] [Small.{max u v} I]
variable [HasWeakSheafify J (Type (max u v))]
variable (F : I ⥤ Sheaf J (Type (max u v)))

/- Source/core/bridge triage for Lemma 7.10.14:
- source-facing content: colimits of set-valued sheaves are obtained by sheafifying a colimit
  cocone of the underlying presheaf diagram
- core/canonical owner: `CategoryTheory.Sheaf.isColimitSheafifyCocone`
- bridge/view: the `Type`-specialization to the canonical cocone
  `colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))`
- primitive data: the diagram `F`
- derived API: the colimit cocone in sheaves, obtained by sheafifying the underlying presheaf
  colimit cocone
-/
/- Lemma 7.10.14: for a small diagram `F` of sheaves of sets on the site `(C, J)`, the colimit
of `F` is obtained by sheafifying the colimit cocone of the underlying diagram of presheaves.
This is exactly the canonical sheaf-colimit statement `Sheaf.isColimitSheafifyCocone`. -/
recall Sheaf.isColimitSheafifyCocone

/- Source-facing specialization: the set-valued sheaf colimit cocone attached to `F` is the
sheafification of the presheaf colimit cocone. -/
#check
  (isColimitSheafifyCocone
    (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v))))
    (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v)))))

/-! ### Lemma_7_10_15 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.10.15:
- primary domain: exactness of set-valued sheafification on a Grothendieck site;
- sampled owner API:
  `presheafToSheaf`,
  `PreservesFiniteLimits (presheafToSheaf J (Type (max u v)))`,
  `Sheaf.isColimitSheafifyCocone`,
  `ExactFunctor.of`;
- best owner abstraction: `ExactFunctor.of (presheafToSheaf J (Type (max u v)))`;
- primitive data: the Grothendieck topology `J`;
- derived API: the underlying sheafification functor obtained by forgetting the exact structure.

Source/core/bridge triage:
- source-facing: the sheafification functor on set-valued presheaves is exact;
- core/canonical: `ExactFunctor.of (presheafToSheaf J (Type (max u v)))`;
- bridge/view: forgetting the bundled exact structure recovers the usual sheafification functor.
-/

/- Lemma 7.10.15 recalls the owner sheafification functor used to build the exact functor. -/
recall presheafToSheaf

/- Lemma 7.10.15: the sheafification functor from set-valued presheaves on `(C, J)` to sheaves of
sets on `(C, J)` is exact. The canonical bundled exact-functor owner is `ExactFunctor.of`. -/
recall ExactFunctor.of

/- Source-facing specialization: the exact sheafification functor for set-valued presheaves. -/
#check
  (ExactFunctor.of (presheafToSheaf J (Type (max u v))) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤ₑ Sheaf J (Type (max u v)))

/-! ### Lemma_7_10_16 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Plus

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))
variable (U : C)

/- Domain-style sampling for Lemma 7.10.16:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Meq`,
  `CategoryTheory.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Presheaf.IsLocallyInjective`,
  `CategoryTheory.Presheaf.IsSheaf.amalgamate`,
  `CategoryTheory.Presheaf.IsSheaf.hom_ext`;
- source-facing layer: the two textbook assertions describing sections of `J.sheafify F` in terms
  of local representatives in `F` and the converse gluing of compatible matching families;
- core/canonical owners: the matching-family object `Meq F S`, the local-bijectivity owners for
  `J.toSheafify F`, and the sheaf gluing/extensionality API on `J.sheafify F`;
- bridge/view layer: the source-facing existence and uniqueness theorems below, derived from those
  owner abstractions.

Primitive data for the second assertion are exactly a cover `S : J.Cover U` and a matching family
`x : Meq F S`. The glued section, its restriction formula, and the uniqueness statement are
derived API from the canonical sheaf owner `J.sheafify_isSheaf F`; no additional public wrapper
around matching families is warranted.
-/

-- Proof sketch: local surjectivity of `J.toSheafify F` gives local representatives for any
-- section of `J.sheafify F`, and local injectivity provides the compatibility on overlaps after
-- refining by further covers. Conversely, `J.sheafify F` is a sheaf, so any compatible matching
-- family of sections of `F` glues uniquely to a global section.
/-- Helper for Lemma 7.10.16: the image sieve of a sheafified section is a covering sieve, and
each arrow in that cover carries a chosen representative in the original presheaf. -/
lemma imageSieve_cover_with_local_preimages
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S : J.Cover U) (y : ∀ I : S.Arrow, F.obj (op I.Y)),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I) := by
  let S : J.Cover U :=
    ⟨Presheaf.imageSieve (J.toSheafify F) s, Presheaf.imageSieve_mem J (J.toSheafify F) s⟩
  let y : ∀ I : S.Arrow, F.obj (op I.Y) :=
    fun I ↦ Presheaf.localPreimage (J.toSheafify F) s I.f I.hf
  refine ⟨S, y, ?_⟩
  intro I
  -- The chosen representative maps to the restricted sheafified section by construction.
  simpa [y] using (Presheaf.app_localPreimage (J.toSheafify F) s I.f I.hf).symm

/-- Helper for Lemma 7.10.16: on each overlap of the initial local representatives, local
injectivity of `J.toSheafify F` yields a covering on which the two pullbacks agree. -/
lemma overlap_equalizer_cover_of_local_representatives
    (s : (J.sheafify F).obj (op U))
    (S : J.Cover U)
    (y : ∀ I : S.Arrow, F.obj (op I.Y))
    (hy : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I)) :
    ∃ T : ∀ r : S.Relation, J.Cover r.r.Z,
      ∀ r : S.Relation, ∀ I : (T r).Arrow,
        F.map I.f.op (F.map r.r.g₁.op (y r.fst)) =
          F.map I.f.op (F.map r.r.g₂.op (y r.snd)) := by
  let T : ∀ r : S.Relation, J.Cover r.r.Z := fun r ↦
    let a : F.obj (op r.r.Z) := F.map r.r.g₁.op (y r.fst)
    let b : F.obj (op r.r.Z) := F.map r.r.g₂.op (y r.snd)
    let h :
        (J.toSheafify F).app (op r.r.Z) a =
          (J.toSheafify F).app (op r.r.Z) b := by
      -- Both images are the restriction of the original global section to the overlap object.
      calc
        (J.toSheafify F).app (op r.r.Z) a =
            (J.sheafify F).map r.r.g₁.op ((J.toSheafify F).app (op r.fst.Y) (y r.fst)) := by
              simpa [a] using
                (FunctorToTypes.naturality _ _ (J.toSheafify F) r.r.g₁.op (y r.fst))
        _ = (J.sheafify F).map r.r.g₁.op ((J.sheafify F).map r.fst.f.op s) := by
              rw [hy r.fst]
        _ = (J.sheafify F).map r.r.g₂.op ((J.sheafify F).map r.snd.f.op s) := by
              simpa only [FunctorToTypes.map_comp_apply, op_comp] using
                congrArg (fun k => (J.sheafify F).map k.op s) r.r.w
        _ = (J.sheafify F).map r.r.g₂.op ((J.toSheafify F).app (op r.snd.Y) (y r.snd)) := by
              rw [hy r.snd]
        _ = (J.toSheafify F).app (op r.r.Z) b := by
              simpa [b] using
                (FunctorToTypes.naturality _ _ (J.toSheafify F) r.r.g₂.op (y r.snd)).symm
    let E : Sieve r.r.Z := Presheaf.equalizerSieve (X := op r.r.Z) a b
    have hmem : E ∈ J r.r.Z := by
      simpa [E] using
        (Presheaf.equalizerSieve_mem (J := J) (φ := J.toSheafify F) (X := op r.r.Z) a b h)
    ⟨E, hmem⟩
  refine ⟨T, ?_⟩
  intro r I
  -- Membership in the equalizer sieve is exactly the required equality.
  exact I.hf

/-- Helper for Lemma 7.10.16: a section of the sheafification is represented by a matching family
of `F⁺`-sections on some outer cover. -/
lemma outer_plus_representation_of_sheafification_section
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀),
      s = Plus.mk y := by
  -- Unfold the concrete sheafification model only at the outermost level.
  simpa using (Plus.exists_rep (J := J) (P := J.plusObj F) s)

/-- Helper for Lemma 7.10.16: each local `F⁺`-section in an outer matching family admits a
representative by a matching family of `F`-sections on an inner cover. -/
lemma inner_plus_representatives_over_outer_cover
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀) :
    ∃ (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      ∀ I : S₀.Arrow, y I = Plus.mk (t I) := by
  -- Choose a concrete `F`-matching family representing each local `F⁺`-section.
  choose T t ht using fun I => Plus.exists_rep (J := J) (P := F) (y I)
  exact ⟨T, t, ht⟩

/-- Helper for Lemma 7.10.16: on each outer overlap, the chosen inner representatives admit a
common refinement over which their pullbacks agree strictly as matching families of `F`. -/
lemma overlap_refinement_of_nested_representatives
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀)
    (T : ∀ I : S₀.Arrow, J.Cover I.Y)
    (t : ∀ I : S₀.Arrow, Meq F (T I))
    (ht : ∀ I : S₀.Arrow, y I = Plus.mk (t I)) :
    ∀ r : S₀.Relation,
      ∃ (W : J.Cover r.r.Z)
        (h₁ : W ⟶ (J.pullback r.r.g₁).obj (T r.fst))
        (h₂ : W ⟶ (J.pullback r.r.g₂).obj (T r.snd)),
        ((t r.fst).pullback r.r.g₁).refine h₁ = ((t r.snd).pullback r.r.g₂).refine h₂ := by
  intro r
  -- Rewrite the outer compatibility equality using the chosen inner representatives.
  have hr : Plus.mk ((t r.fst).pullback r.r.g₁) = Plus.mk ((t r.snd).pullback r.r.g₂) := by
    calc
      Plus.mk ((t r.fst).pullback r.r.g₁)
          = (J.plusObj F).map r.r.g₁.op (Plus.mk (t r.fst)) := by
              symm
              exact Plus.res_mk_eq_mk_pullback (J := J) (x := t r.fst) r.r.g₁
      _ = (J.plusObj F).map r.r.g₁.op (y r.fst) := by
            rw [ht]
      _ = (J.plusObj F).map r.r.g₂.op (y r.snd) := by
            exact y.condition r
      _ = (J.plusObj F).map r.r.g₂.op (Plus.mk (t r.snd)) := by
            rw [ht]
      _ = Plus.mk ((t r.snd).pullback r.r.g₂) := by
            exact Plus.res_mk_eq_mk_pullback (J := J) (x := t r.snd) r.r.g₂
  -- Equality in `F⁺` is exactly represented by a common refinement of the underlying `F` data.
  simpa using
    (Plus.eq_mk_iff_exists (J := J) ((t r.fst).pullback r.r.g₁) ((t r.snd).pullback r.r.g₂)).mp hr

/-- Helper for Lemma 7.10.16: a strict `Meq F`-description of a sheafified section on one cover
already descends that section to a global section of `F⁺`. -/
lemma plus_representation_of_strict_matching_family
    (s : (J.sheafify F).obj (op U))
    {S : J.Cover U} (x : Meq F S)
    (hx : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I)) :
    ∃ y : (J.plusObj F).obj (op U),
      s = (J.toPlus (J.plusObj F)).app (op U) y := by
  refine ⟨Plus.mk x, ?_⟩
  -- Equality in `F⁺⁺` follows from equality on a cover because `F⁺` is separated.
  apply Plus.sep (J := J) (P := J.plusObj F) (S := S)
  intro I
  -- Rewrite the chosen local `F`-section through `F⁺` and then through `F⁺⁺`.
  calc
    (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := hx I
    _ = (J.sheafify F).map I.f.op ((J.toPlus (J.plusObj F)).app (op U) (Plus.mk x)) := by
          rw [GrothendieckTopology.toSheafify]
          rw [GrothendieckTopology.plusMap_toPlus]
          change
            (J.toPlus (J.plusObj F)).app (op I.Y) ((J.toPlus F).app (op I.Y) (x I)) =
              (J.sheafify F).map I.f.op ((J.toPlus (J.plusObj F)).app (op U) (Plus.mk x))
          have hnat :=
            (FunctorToTypes.naturality _ _ (J.toPlus (J.plusObj F)) I.f.op (Plus.mk x)).symm
          exact Eq.trans
            (congrArg ((J.toPlus (J.plusObj F)).app (op I.Y))
              (Plus.toPlus_apply (J := J) (P := F) S x I))
            hnat.symm

/-- Lemma 7.10.16, first assertion: every section of the sheafification is represented by an
outer matching family of `F⁺`-sections, and each of those local `F⁺`-sections is itself represented
by a matching family of sections of the original presheaf `F`.  This is the faithful two-stage
`F⁺⁺` formulation of the source phrase "locally comes from the presheaf"; it deliberately does
not assert the stronger false claim that one can strictify to a single `Meq F S` over the original
cover. -/
theorem exists_cover_and_matchingFamily_of_sheafification_section
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀)
      (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      s = Plus.mk y ∧ ∀ I : S₀.Arrow, y I = Plus.mk (t I) := by
  obtain ⟨S₀, y, hy⟩ := outer_plus_representation_of_sheafification_section (J := J) (F := F) (U := U) s
  obtain ⟨T, t, ht⟩ := inner_plus_representatives_over_outer_cover (J := J) (F := F) (U := U) y
  exact ⟨S₀, y, T, t, hy, ht⟩


/-- Companion source-facing formulation of Lemma 7.10.16, second assertion: a compatible matching
family glues uniquely to a section of the sheafification. -/
theorem existsUnique_sheafificationSection_of_matchingFamily
    (S : J.Cover U) (x : Meq F S) :
    ∃! s : (J.sheafify F).obj (op U),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := by
  let y : ∀ I : S.Arrow, PUnit ⟶ (J.sheafify F).obj (op I.Y) :=
    fun I _ ↦ (J.toSheafify F).app (op I.Y) (x I)
  have hy :
      ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
        y I₁ ≫ (J.sheafify F).map r.g₁.op = y I₂ ≫ (J.sheafify F).map r.g₂.op := by
    intro I₁ I₂ r
    funext _
    change
      (J.sheafify F).map r.g₁.op ((J.toSheafify F).app (op I₁.Y) (x I₁)) =
        (J.sheafify F).map r.g₂.op ((J.toSheafify F).app (op I₂.Y) (x I₂))
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₁.op (x I₁)]
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₂.op (x I₂)]
    exact congrArg ((J.toSheafify F).app (op r.Z))
      (x.condition (Cover.Relation.mk' r))
  refine ⟨((J.sheafify_isSheaf F).amalgamate S y hy) PUnit.unit, ?_, ?_⟩
  · intro I
    exact congrFun ((J.sheafify_isSheaf F).amalgamate_map S y hy I) PUnit.unit
  intro s hs
  have h :
      (fun _ : PUnit ↦ s) = (J.sheafify_isSheaf F).amalgamate S y hy := by
    apply (J.sheafify_isSheaf F).hom_ext S
    intro I
    funext u
    cases u
    simpa [y, hs I] using
      congrFun (((J.sheafify_isSheaf F).amalgamate_map S y hy I).symm) PUnit.unit
  exact congrFun h PUnit.unit

/-! ### Lemma_7_10_17 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Presheaf
open CategoryTheory.SemiRepresentableFamily.Over

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {F G : Cᵒᵖ ⥤ Type (max u v)} (η : F ⟶ G)

/- Domain-style sampling for Lemma 7.10.17:
- primary domain: Grothendieck-topology local bijectivity and sheafification for set-valued
  presheaves;
- sampled owner API:
  `Presheaf.IsLocallyInjective`,
  `Presheaf.IsLocallySurjective`,
  `GrothendieckTopology.W_iff_isLocallyBijective`,
  `GrothendieckTopology.W_iff`,
  `SemiRepresentableFamily.Over.toSieve`;
- source-facing layer: the covering-family hypothesis that `η` is componentwise bijective on some
  cover of each object;
- core/canonical owner: `J.W η`, equivalently the sheafification map of `η` is an isomorphism;
- bridge/view: the two local proofs turning the source-facing covering hypothesis into the
  canonical local injectivity and local surjectivity predicates.

Primitive data are only the explicit covering-family hypothesis:
for each `U`, a family `𝒰 : SemiRepresentableFamily.Over U` whose generated sieve
lies in `J U`, together with the componentwise bijectivity of `η.app (op (𝒰.obj i).left)`.
The local injective/surjective facts and the `J.W` conclusion are derived API and should not be
repackaged as a second owner.
-/

/-- Helper for Lemma 7.10.17: componentwise injectivity on a covering family makes the morphism
locally injective. -/
private theorem isLocallyInjective_of_cover_by_componentwise_bijective :
    (∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over U,
      𝒰.toSieve ∈ J U ∧
        ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) →
    IsLocallyInjective J η := by
  intro hcover
  refine ⟨fun {X} x y hxy ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, hbij⟩ := hcover X.unop
  -- It is enough to work on a covering family where each component map of `η` is injective.
  refine J.superset_covering ?_ h𝒰
  intro Y g hg
  have hg' :
      Sieve.ofArrows (fun i : 𝒰.index ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) g := by
    simpa [SemiRepresentableFamily.Over.toSieve, SemiRepresentableFamily.Over.toPresieve] using hg
  let i : 𝒰.index := Sieve.ofArrows.i hg'
  let k : Y ⟶ (𝒰.obj i).left := Sieve.ofArrows.h hg'
  have hk : k ≫ (𝒰.obj i).hom = g := by
    dsimp [i, k]
    exact Sieve.ofArrows.fac hg'
  -- Naturality moves the equality of images to the chosen covering object, where injectivity
  -- recovers equality upstairs.
  have hfg : F.map ((𝒰.obj i).hom).op x = F.map ((𝒰.obj i).hom).op y := by
    apply (hbij i).injective
    exact
      (FunctorToTypes.naturality _ _ η ((𝒰.obj i).hom).op x).trans <|
        (congrArg (G.map ((𝒰.obj i).hom).op) hxy).trans
          (FunctorToTypes.naturality _ _ η ((𝒰.obj i).hom).op y).symm
  -- Restricting further along the factorization arrow `k` keeps the two sections equal.
  dsimp [equalizerSieve]
  calc
    F.map g.op x
        = F.map k.op (F.map ((𝒰.obj i).hom).op x) := by
            rw [← hk]
            simp [op_comp]
    _ = F.map k.op (F.map ((𝒰.obj i).hom).op y) := by rw [hfg]
    _ = F.map g.op y := by
          rw [← hk]
          simp [op_comp]

/-- Helper for Lemma 7.10.17: componentwise surjectivity on a covering family makes the morphism
locally surjective. -/
private theorem isLocallySurjective_of_cover_by_componentwise_bijective :
    (∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over U,
      𝒰.toSieve ∈ J U ∧
        ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) →
    IsLocallySurjective J η := by
  intro hcover
  refine ⟨fun {U} s ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, hbij⟩ := hcover U
  -- The covering family supplies local targets where `η` is surjective, so we lift `s`
  -- componentwise and then pull back along an arbitrary member of the generated sieve.
  refine J.superset_covering ?_ h𝒰
  intro Y g hg
  have hg' :
      Sieve.ofArrows (fun i : 𝒰.index ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) g := by
    simpa [SemiRepresentableFamily.Over.toSieve, SemiRepresentableFamily.Over.toPresieve] using hg
  let i : 𝒰.index := Sieve.ofArrows.i hg'
  let k : Y ⟶ (𝒰.obj i).left := Sieve.ofArrows.h hg'
  have hk : k ≫ (𝒰.obj i).hom = g := by
    dsimp [i, k]
    exact Sieve.ofArrows.fac hg'
  obtain ⟨t, ht⟩ := (hbij i).surjective (G.map ((𝒰.obj i).hom).op s)
  refine ⟨F.map k.op t, ?_⟩
  -- Naturality identifies the image of the pulled-back lift with the restriction of `s`.
  calc
    η.app (op Y) (F.map k.op t)
        = G.map k.op (η.app (op ((𝒰.obj i).left)) t) :=
          FunctorToTypes.naturality _ _ η _ t
    _ = G.map k.op (G.map ((𝒰.obj i).hom).op s) := by rw [ht]
    _ = G.map g.op s := by
          rw [← hk]
          simp [op_comp]

-- Proof sketch: the covering hypothesis makes `η` locally injective and locally surjective in
-- the canonical mathlib sense, so `η` belongs to `J.W`, i.e. it becomes an isomorphism after
-- sheafification.
/-- Lemma 7.10.17: if every object admits a covering by objects on which a morphism of set-valued
presheaves is componentwise bijective, then the morphism lies in `J.W`, equivalently it becomes an
isomorphism after sheafification. -/
theorem w_of_cover_by_componentwise_bijective
    (hcover :
      ∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over U,
        𝒰.toSieve ∈ J U ∧
          ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) :
    J.W η := by
  -- The canonical criterion for `J.W` is local bijectivity, and the two helper lemmas establish
  -- exactly that from the source covering-family hypothesis.
  exact (J.W_iff_isLocallyBijective η).2
    ⟨isLocallyInjective_of_cover_by_componentwise_bijective J η hcover,
      isLocallySurjective_of_cover_by_componentwise_bijective J η hcover⟩
