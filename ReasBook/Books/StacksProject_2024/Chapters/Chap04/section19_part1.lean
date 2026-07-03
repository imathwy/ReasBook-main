import Mathlib
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Bool
import Mathlib.Logic.Function.ULift
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_19_1 (from Chap04) -/
universe v u vC uC

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]
variable {C : Type uC} [Category.{vC} C]

/-- Definition 4.19.1, diagram form: a diagram is filtered when its indexing category is
nonempty, any two objects admit a common successor, and any two parallel arrows become equal
after postcomposition with some arrow and applying the diagram. -/
structure IsFilteredDiagram (M : I ⥤ C) : Prop where
  /-- The indexing category has at least one object. -/
  nonempty : Nonempty I
  /-- Any two objects in the indexing category admit a common successor. -/
  cocone_objs : ∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True
  /-- Parallel morphisms can be equalized after postcomposition and applying the diagram. -/
  cocone_maps : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
    ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c)

namespace IsFilteredDiagram

/-- A functor indexed by a filtered category is a filtered diagram in the source sense. -/
theorem of_isFiltered (M : I ⥤ C) [IsFiltered I] : IsFilteredDiagram M where
  nonempty := IsFiltered.nonempty
  cocone_objs := IsFilteredOrEmpty.cocone_objs
  cocone_maps := by
    intro x y a b
    obtain ⟨z, c, hc⟩ := IsFilteredOrEmpty.cocone_maps a b
    exact ⟨z, c, by simpa using congrArg M.map hc⟩

/-- The identity diagram is filtered exactly when the indexing category is filtered. -/
theorem isFiltered_of_id (h : IsFilteredDiagram (𝟭 I)) : IsFiltered I where
  nonempty := h.nonempty
  cocone_objs := h.cocone_objs
  cocone_maps := by
    intro x y a b
    obtain ⟨z, c, hc⟩ := h.cocone_maps a b
    exact ⟨z, c, by simpa using hc⟩

/-- Definition 4.19.1, index-category clause: `I` is filtered iff its identity diagram is
filtered. -/
theorem id_iff_isFiltered : IsFilteredDiagram (𝟭 I) ↔ IsFiltered I :=
  ⟨isFiltered_of_id, fun _ => of_isFiltered (𝟭 I)⟩

end IsFilteredDiagram

/- Definition 4.19.1: the canonical mathlib notion of a filtered index category is
`CategoryTheory.IsFiltered I`. -/
recall IsFiltered

/-
Domain-style sampling for Definition 4.19.1:
- primary domain: filtered index categories in category theory;
- relevant owner declarations inspected:
  - `CategoryTheory.IsFiltered`,
  - `CategoryTheory.IsFilteredOrEmpty`,
  - `CategoryTheory.IsFiltered.max`,
  - `CategoryTheory.IsFiltered.coeq_condition`;
- best owner abstraction:
  - `source-facing`: `IsFilteredDiagram`, with the textbook nonemptiness,
    common-successor, and diagram-level postcomposition-equalizer conditions;
  - `core/canonical`: `IsFiltered`, with primitive owner data in `IsFilteredOrEmpty`;
  - `bridge/view`: direct downstream existential uses of `IsFilteredOrEmpty.cocone_objs` and
    local equalizer constructions when only the source-facing witnesses are needed;
- primitive data: `IsFiltered.nonempty`, `IsFilteredOrEmpty.cocone_objs`, and
  `IsFilteredOrEmpty.cocone_maps`.

Source/core/bridge triage for Definition 4.19.1:
- `source-facing`: `IsFilteredDiagram`, including the diagram-level
  postcomposition-equalizer condition, and its identity-diagram bridge to `IsFiltered`.
- `core/canonical`: `IsFiltered` and `IsFilteredOrEmpty`.
- `bridge/view`: downstream existential uses of `IsFilteredOrEmpty.cocone_objs` together with
  direct equalizer witnesses on opposite categories.
-/

end CategoryTheory

/-! ### Lemma_4_19_2 (from Chap04) -/
universe v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I] [IsFiltered I]

/- Domain-style sampling for Lemma 4.19.2:
- primary domain: filtered categories and preservation of finite limits by colimits of
  `Type`-valued diagrams
- inspected owner declarations:
  - `CategoryTheory.IsFiltered`
  - `CategoryTheory.Limits.PreservesFiniteLimits`
  - `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSize`
  - `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`
- owner abstraction: `PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`
- primitive data: the filteredness hypothesis on `I`
- derived API: the canonical owner property is available by instance search; mathlib constructs it
  via `filtered_colim_preservesFiniteLimits_of_types`
- target layer here: `core/canonical`, so the file should expose the owner property directly rather
  than introduce a parallel local theorem or use the bridge instance name as the main entry
-/
/- Source/core/bridge triage for Lemma 4.19.2:
- `source-facing`: the filteredness hypothesis on the index category `I`
- `core/canonical`: `PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`
- `bridge/view`: the named mathlib instance
  `filtered_colim_preservesFiniteLimits_of_types`
-/
/- Lemma 4.19.2: if `I` is filtered, then colimits over `I` commute with finite limits in the
category of sets. In mathlib this is expressed directly by the owner property
`PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`. The named instance
`CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types` is the canonical proof term
behind the instance search below. -/
#check
  (show PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v) from inferInstance)

end CategoryTheory.Limits

/-! ### Lemma_4_19_3 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace ObjectProperty

variable {I : Type u} [Category.{v} I]
variable (P : ObjectProperty I)
variable [IsFiltered I]
variable (h : ∀ X : I, ∃ Y : P.FullSubcategory, Nonempty (X ⟶ Y.obj))

/- Domain sampling:
- Primary domain: filtered categories and full subcategories cut out by an object property.
- Core/canonical declarations inspected:
  - `FullSubcategory`
  - `ι`
  - `fullyFaithfulι`
  - `IsFiltered.of_exists_of_isFiltered_of_fullyFaithful`
  - `Functor.final_of_exists_of_isFiltered_of_fullyFaithful`
- Owner abstraction: the inclusion functor `P.ι : P.FullSubcategory ⥤ I`.
- Layer triage:
  - `source-facing`: the existence hypothesis that every `X : I` maps to an object satisfying `P`;
  - `core/canonical`: the fully faithful inclusion `P.ι`;
  - `bridge/view`: the two source-level consequences obtained by specializing the owner theorems to
    `P.ι`.
- Since the canonical owners are generic theorems rather than named declarations specialized to
  `P.ι`, this file records the specialized bridge layer with `#check` instead of introducing local
  wrapper theorems.
- Primitive vs. derived:
  - primitive data: the object property `P` and the hypothesis `h`;
  - derived API: filteredness of `P.FullSubcategory` and finality of `P.ι`.
-/

/- Owner recall: the full-subcategory inclusion `P.ι` is the canonical owner abstraction from which
the source-facing consequences in Lemma 4.19.3 are derived. -/
recall ι (P : ObjectProperty I) : P.FullSubcategory ⥤ I

/- Lemma 4.19.3, filteredness part: under the source hypothesis `h`, the filteredness of
`P.FullSubcategory` is exactly the canonical owner theorem applied to the inclusion `P.ι`. -/
#check
  (IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    IsFiltered P.FullSubcategory)

/- Lemma 4.19.3, cofinality part: under the same source hypothesis `h`, the finality of `P.ι` is
exactly the canonical owner theorem specialized to that inclusion. -/
#check
  (Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    P.ι.Final)

end ObjectProperty
end CategoryTheory

/-! ### Lemma_4_19_4 (from Chap04) -/
open CategoryTheory
open CategoryTheory.FunctorToTypes

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I] [Small.{w} I]

/-
Domain-style sampling for Lemma 4.19.4:
- source-facing hypothesis: every pair of objects admits a common successor
- sampled owner declarations in this domain:
  - `CategoryTheory.Limits.prodComparison`
  - `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
  - `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`
- primitive data: a pair of colimit representatives together with the source-level
  common-successor hypothesis
- derived API: the resulting surjectivity bridge for `prodComparison`
- best owner abstraction: the comparison morphism `prodComparison` itself; the source-facing
  theorem below is the weak bridge from common successors to surjectivity, while the stronger
  finite-limit preservation owner is only background because it proves more than this lemma needs
- target layer here: `bridge/view`, namely the surjectivity statement for `prodComparison`,
  with a thin `IsFilteredOrEmpty` corollary through the owner field
  `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
-/

/-
Source/core/bridge triage for Lemma 4.19.4:
- `source-facing`: the explicit common-successor hypothesis on the index category
- `core/canonical`: the binary-product comparison morphism `prodComparison colim M N`
- `bridge/view`: surjectivity of that comparison under the weaker source hypothesis, plus the
  `IsFilteredOrEmpty` specialization obtained from `IsFilteredOrEmpty.cocone_objs`
-/

/-- Applied form of the first projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: compose `prodComparison` with the first projection from the binary product
-- isomorphism, then rewrite using the canonical `prodComparison_fst` compatibility together with
-- the explicit `Type` colimit map formula.
theorem prodComparison_colim_ι_fst (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
      colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := by
  -- Rewrite the first coordinate through the explicit `Type` binary-product isomorphism.
  have hIso :
      ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
        (Limits.prod.fst : colimit M ⨯ colimit N ⟶ colimit M)
          (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) := by
    simpa using
      congrFun (Types.binaryProductIso_hom_comp_fst (colimit M) (colimit N))
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))
  have hComp :
      (Limits.prod.fst : colimit M ⨯ colimit N ⟶ colimit M)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) =
        (colim.map (prod.fst : M ⨯ N ⟶ M)) (colimit.ι (M ⨯ N) k x) := by
    simpa using
      congrFun (prodComparison_fst (F := colim) (A := M) (B := N))
        (colimit.ι (M ⨯ N) k x)
  have hMap :
      (colim.map (prod.fst : M ⨯ N ⟶ M)) (colimit.ι (M ⨯ N) k x) =
        colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := by
    simpa using Types.Colimit.ι_map_apply (prod.fst : M ⨯ N ⟶ M) k x
  exact hIso.trans (hComp.trans hMap)

/-- Applied form of the second projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: this is the second-projection analogue of
-- `prodComparison_colim_ι_fst`, using `prodComparison_snd` and the `Type` colimit map formula for
-- `prod.snd`.
theorem prodComparison_colim_ι_snd (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
      colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := by
  -- Rewrite the second coordinate through the explicit `Type` binary-product isomorphism.
  have hIso :
      ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
        (Limits.prod.snd : colimit M ⨯ colimit N ⟶ colimit N)
          (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) := by
    simpa using
      congrFun (Types.binaryProductIso_hom_comp_snd (colimit M) (colimit N))
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))
  have hComp :
      (Limits.prod.snd : colimit M ⨯ colimit N ⟶ colimit N)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) =
        (colim.map (prod.snd : M ⨯ N ⟶ N)) (colimit.ι (M ⨯ N) k x) := by
    simpa using
      congrFun (prodComparison_snd (F := colim) (A := M) (B := N))
        (colimit.ι (M ⨯ N) k x)
  have hMap :
      (colim.map (prod.snd : M ⨯ N ⟶ N)) (colimit.ι (M ⨯ N) k x) =
        colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := by
    simpa using Types.Colimit.ι_map_apply (prod.snd : M ⨯ N ⟶ N) k x
  exact hIso.trans (hComp.trans hMap)

-- Proof sketch: represent the two coordinates of a point in
-- `colimit M × colimit N` at possibly different stages, move both representatives to a common
-- successor using the source hypothesis, and then use the induced element of `(M ⨯ N).obj k` to
-- build a preimage under `prodComparison`.
/-- Lemma 4.19.4 (1): if every pair of objects in the index category admits a common successor,
then the canonical comparison map
`colimit (M ⨯ N) ⟶ colimit M × colimit N`
is surjective for `Type`-valued diagrams `M` and `N`. -/
theorem prodComparison_colim_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (M N : I ⥤ Type w)
    : Function.Surjective (prodComparison colim M N) := by
  classical
  intro y
  let e := Types.binaryProductIso (colimit M) (colimit N)
  -- Choose representatives for the two coordinates of the target pair.
  obtain ⟨i, m, hm⟩ := Types.jointly_surjective' (e.hom y).1
  obtain ⟨j, n, hn⟩ := Types.jointly_surjective' (e.hom y).2
  -- Move both representatives to a common successor stage.
  obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hObj i j
  let x : (M ⨯ N).obj k := FunctorToTypes.prodMk (F := M) (G := N) (M.map f m) (N.map g n)
  refine ⟨colimit.ι (M ⨯ N) k x, ?_⟩
  -- Compare after applying the explicit `Type` product isomorphism and checking coordinates.
  have hxy :
      e.hom (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) = e.hom y := by
    ext
    · rw [prodComparison_colim_ι_fst]
      simpa [x, hm]
    · rw [prodComparison_colim_ι_snd]
      simpa [x, hn]
  exact by
    apply (congrArg e.inv) at hxy
    simpa [e] using hxy

/-- For a filtered-or-empty index category, the common-successor hypothesis is already available
from the owner field `CategoryTheory.IsFilteredOrEmpty.cocone_objs`, so the surjectivity
statement is just the preceding source-facing bridge specialized to that canonical API. -/
-- Proof sketch: apply `prodComparison_colim_surjective_of_commonSuccessor` and obtain the common
-- successor from `IsFilteredOrEmpty.cocone_objs`.
theorem prodComparison_colim_surjective_of_isFilteredOrEmpty [IsFilteredOrEmpty I]
    (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := by
  -- Extract the common successor promised by filteredness and invoke the source-facing theorem.
  apply prodComparison_colim_surjective_of_commonSuccessor
  intro i j
  obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
  exact ⟨k, ⟨f⟩, ⟨g⟩⟩

/-- Helper for Lemma 4.19.4: `OneObjCat G` is the one-object category in universe `u` whose
endomorphism monoid is `G`. -/
@[nolint unusedArguments]
def OneObjCat (_ : Type v) : Type u := ULift.{u} Unit

instance (G : Type v) [Monoid G] : Category.{v} (OneObjCat G) where
  Hom _ _ := G
  id _ := 1
  comp f g := g * f
  comp_id := by
    intro X Y f
    exact one_mul f
  id_comp := by
    intro X Y f
    exact mul_one f
  assoc := by
    intro W X Y Z f g h
    exact (mul_assoc h g f).symm

instance (G : Type v) : Subsingleton (OneObjCat G) := ⟨fun a b ↦ by
  cases a
  cases b
  rfl⟩

instance (G : Type v) : Small.{w} (OneObjCat G) := by
  infer_instance

/-- Helper for Lemma 4.19.4: the unique object of `OneObjCat G`. -/
abbrev oneObj (G : Type v) : OneObjCat G := ULift.up ()

/-- Helper for Lemma 4.19.4: a multiplicative action `G ↻ X` viewed as a `Type`-valued diagram on
the one-object category `OneObjCat G`. -/
def oneObjActionFunctor (G : Type v) [Monoid G] (X : Type w) [MulAction G X] :
    OneObjCat G ⥤ Type w where
  obj _ := X
  map := fun {_ _} g x ↦ g • x
  map_id := fun _ ↦ funext fun x ↦ one_smul G x
  map_comp := fun {_ _ _} f g ↦ funext fun x ↦ (smul_smul g f x).symm

/-- Helper for Lemma 4.19.4: `ULift P` acts on `ULift P` by left translation. -/
instance uliftLeftMulAction (P : Type) [Group P] : MulAction (ULift.{v} P) (ULift.{w} P) where
  smul g x := ULift.up (g.down * x.down)
  one_smul x := by
    -- Unfold the lifted action and reduce to the unit law in `P`.
    change ULift.up ((1 : P) * x.down) = x
    simpa
  mul_smul g h x := by
    -- Both sides reduce to the same multiplication expression in `P`.
    change ULift.up (((g * h).down) * x.down) = ULift.up (g.down * (h.down * x.down))
    simp [mul_assoc]

/-- Helper for Lemma 4.19.4: the colimit relation of a one-object action diagram is the orbit
relation of the underlying action. -/
theorem oneObjAction_colimitTypeRel_iff_orbitRel
    (G : Type v) [Group G] (X : Type w) [MulAction G X] (x y : X) :
    (oneObjActionFunctor G X).ColimitTypeRel ⟨oneObj G, x⟩ ⟨oneObj G, y⟩ ↔
      MulAction.orbitRel G X x y := by
  -- Rewrite the orbit relation as an existence statement and compare it to the explicit
  -- one-object colimit relation.
  have hshape :
      (oneObjActionFunctor G X).ColimitTypeRel ⟨oneObj G, x⟩ ⟨oneObj G, y⟩ ↔
        ∃ g : G, y = g • x := by
    rfl
  rw [hshape, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp⟩
  · rintro ⟨g, hg⟩
    have h' : g⁻¹ • x = y := by
      simpa [hg] using smul_smul g⁻¹ g y
    exact ⟨g⁻¹, h'.symm⟩

/-- Helper for Lemma 4.19.4: the sigma type of representatives for a one-object action diagram is
canonically equivalent to the underlying set. -/
noncomputable def oneObjAction_sigmaEquiv (G : Type v) (X : Type w) :
    (Sigma fun _ : OneObjCat G ↦ X) ≃ X where
  toFun p := p.2
  invFun x := ⟨oneObj G, x⟩
  left_inv p := by
    cases p with
    | mk j x =>
        rw [Subsingleton.elim j (oneObj G)]
  right_inv x := rfl

/-- Helper for Lemma 4.19.4: under `oneObjAction_sigmaEquiv`, the concrete one-object colimit
relation becomes the orbit relation. -/
theorem oneObjAction_colimitTypeRel_iff_orbitRel_all
    (G : Type v) [Group G] (X : Type w) [MulAction G X]
    (p q : Sigma fun _ : OneObjCat G ↦ X) :
    (oneObjActionFunctor G X).ColimitTypeRel p q ↔
      MulAction.orbitRel G X (oneObjAction_sigmaEquiv G X p) (oneObjAction_sigmaEquiv G X q) := by
  -- Reduce to the unique object and then apply the pointwise orbit-relation comparison.
  cases p
  cases q
  simpa [oneObjAction_sigmaEquiv] using oneObjAction_colimitTypeRel_iff_orbitRel G X _ _

/-- Helper for Lemma 4.19.4: the concrete colimit quotient of a one-object action diagram is the
orbit quotient. -/
noncomputable def oneObjAction_colimitTypeRelEquivOrbitRelQuotient
    (G : Type v) [Group G] (X : Type w) [MulAction G X] :
    (oneObjActionFunctor G X).ColimitType ≃ MulAction.orbitRel.Quotient G X :=
  Quot.congr (oneObjAction_sigmaEquiv G X) (oneObjAction_colimitTypeRel_iff_orbitRel_all G X)

/-- Helper for Lemma 4.19.4: the colimit of a one-object action diagram is the corresponding
orbit quotient. -/
noncomputable def oneObjAction_colimitEquivQuotient
    (G : Type v) [Group G] (X : Type w) [MulAction G X] :
    colimit (oneObjActionFunctor G X) ≃ MulAction.orbitRel.Quotient G X :=
  (Types.colimitEquivColimitType (oneObjActionFunctor G X)).trans
    (oneObjAction_colimitTypeRelEquivOrbitRelQuotient G X)

/-- Helper for Lemma 4.19.4: a stage representative of a one-object action diagram maps to its
orbit class under the colimit/orbit quotient equivalence. -/
theorem oneObjAction_colimitEquivQuotient_ι
    (G : Type v) [Group G] (X : Type w) [MulAction G X] (x : X) :
    oneObjAction_colimitEquivQuotient G X
      (colimit.ι (oneObjActionFunctor G X) (oneObj G) x) = Quotient.mk'' x := by
  -- Expand the explicit colimit model and evaluate both quotient maps on a representative.
  change oneObjAction_colimitTypeRelEquivOrbitRelQuotient G X
      ((Types.colimitEquivColimitType (oneObjActionFunctor G X))
        (colimit.ι (oneObjActionFunctor G X) (oneObj G) x)) = Quotient.mk'' x
  rw [Types.colimitEquivColimitType_apply]
  rfl

/-- Helper for Lemma 4.19.4: the orbit quotient of the regular left-translation action is a
singleton. -/
theorem left_translation_orbit_quotient_subsingleton (P : Type) [Group P] :
    Subsingleton (MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P)) := by
  -- Any two points differ by left translation by `x * y⁻¹`, so all orbit classes coincide.
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  apply Quotient.sound
  change MulAction.orbitRel (ULift.{v} P) (ULift.{w} P) x y
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨ULift.up (x.down * y.down⁻¹), ?_⟩
  change ULift.up ((x.down * y.down⁻¹) * y.down) = x
  simpa [mul_assoc]

/-- Helper for Lemma 4.19.4: all stage representatives coincide in the colimit of the regular
left-translation action. -/
theorem left_translation_colimit_eq (P : Type) [Group P] (x y : ULift.{w} P) :
    colimit.ι (oneObjActionFunctor (ULift.{v} P) (ULift.{w} P))
      (oneObj (ULift.{v} P)) x =
    colimit.ι (oneObjActionFunctor (ULift.{v} P) (ULift.{w} P))
      (oneObj (ULift.{v} P)) y := by
  -- Pass to orbit classes, where the regular-action quotient is already a singleton.
  apply (oneObjAction_colimitEquivQuotient (ULift.{v} P) (ULift.{w} P)).injective
  rw [oneObjAction_colimitEquivQuotient_ι, oneObjAction_colimitEquivQuotient_ι]
  let hsub : Subsingleton (MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P)) :=
    left_translation_orbit_quotient_subsingleton (P := P)
  exact @Subsingleton.elim _ hsub _ _

/-- Helper for Lemma 4.19.4: for the diagonal left-translation action, the orbit classes of
`(1, 1)` and `(1, s)` are distinct whenever `s ≠ 1`. -/
theorem diagonal_left_translation_orbit_classes_ne
    (P : Type) [Group P] (s : ULift.{w} P) (hs : s ≠ 1) :
    (Quotient.mk'' ((1 : ULift.{w} P), (1 : ULift.{w} P)) :
      MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P × ULift.{w} P)) ≠
      Quotient.mk'' ((1 : ULift.{w} P), s) := by
  -- Compare the two coordinates of a hypothetical diagonal-translation witness.
  intro hq
  have horbit :
      MulAction.orbitRel (ULift.{v} P) (ULift.{w} P × ULift.{w} P)
        ((1 : ULift.{w} P), (1 : ULift.{w} P)) ((1 : ULift.{w} P), s) := Quotient.eq''.mp hq
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  rcases horbit with ⟨g, hg⟩
  have hfst : g • (1 : ULift.{w} P) = (1 : ULift.{w} P) := by
    simpa using congrArg (fun z : ULift.{w} P × ULift.{w} P ↦ z.1) hg
  have hsnd : g • s = (1 : ULift.{w} P) := by
    simpa using congrArg (fun z : ULift.{w} P × ULift.{w} P ↦ z.2) hg
  cases s with
  | up t =>
      -- The first coordinate forces `g = 1`, and then the second forces `t = 1`.
      have hgdown : g.down = 1 := by
        have hfst' : g.down * 1 = 1 := by
          change ULift.down (g • (1 : ULift.{w} P)) = 1
          simpa using congrArg ULift.down hfst
        simpa using hfst'
      have hsdown : g.down * t = 1 := by
        simpa using congrArg ULift.down hsnd
      have ht : t = 1 := by
        simpa [hgdown] using hsdown
      apply hs
      change ULift.up t = ULift.up 1
      simp [ht]

-- Proof sketch: take the one-object category attached to a nontrivial group acting on itself by
-- translation; then the colimit of the diagonal action on `G × G` has more than one orbit, while
-- the product of the two quotient colimits is a singleton.
/-- Lemma 4.19.4 (2): even if every pair of objects in the index category admits a common
successor, colimits of `Type`-valued diagrams do not in general commute with finite nonempty
products; in fact, there is already a counterexample for binary products. -/
theorem colimits_of_set_valued_diagrams_need_not_commute_with_binary_products :
    ∃ (J : Type u) (_ : Category.{v} J) (_ : Small.{w} J)
      (_ : ∀ i j : J, ∃ k : J, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
      (F G : J ⥤ Type w),
        ¬ Function.Bijective (prodComparison colim F G) := by
  let G : Type v := ULift.{v} (Equiv.Perm Bool)
  let X : Type w := ULift.{w} (Equiv.Perm Bool)
  let F : OneObjCat G ⥤ Type w := oneObjActionFunctor G X
  refine ⟨OneObjCat G, inferInstance, inferInstance, ?_, F, F, ?_⟩
  · -- The witness category has one object, so any pair of objects has the same common successor.
    intro i j
    cases i
    cases j
    exact ⟨oneObj G, ⟨(1 : G)⟩, ⟨(1 : G)⟩⟩
  · -- Choose the two diagonal-orbit representatives that collapse after applying
    -- `prodComparison`, but remain distinct in the source colimit.
    let s : X := ULift.up (Equiv.swap true false)
    have hs : s ≠ 1 := by
      -- The transposition of `true` and `false` is not the identity permutation.
      intro hsEq
      have hdown : Equiv.swap true false = 1 := by
        change ULift.up (Equiv.swap true false) = ULift.up 1 at hsEq
        simpa using congrArg ULift.down hsEq
      have htrue := congrArg (fun e : Equiv.Perm Bool ↦ e true) hdown
      simp at htrue
    let ab : (F ⨯ F).obj (oneObj G) := FunctorToTypes.prodMk (F := F) (G := F) (1 : X) (1 : X)
    let as : (F ⨯ F).obj (oneObj G) := FunctorToTypes.prodMk (F := F) (G := F) (1 : X) s
    let a : colimit (F ⨯ F) :=
      colimit.ι (F ⨯ F) (oneObj G) ab
    let b : colimit (F ⨯ F) :=
      colimit.ι (F ⨯ F) (oneObj G) as
    intro hbij
    have hEqImage : prodComparison colim F F a = prodComparison colim F F b := by
      -- Compare after identifying the binary product in `Type`, and compute both projections.
      let e := Types.binaryProductIso (colimit F) (colimit F)
      have hxy : e.hom (prodComparison colim F F a) = e.hom (prodComparison colim F F b) := by
        ext
        · rw [prodComparison_colim_ι_fst, prodComparison_colim_ι_fst]
          simp [ab, as, F, FunctorToTypes.prodMk_fst]
        · rw [prodComparison_colim_ι_snd, prodComparison_colim_ι_snd]
          simpa [a, b, ab, as, F, FunctorToTypes.prodMk_snd] using
            left_translation_colimit_eq (P := Equiv.Perm Bool) (x := (1 : X)) (y := s)
      apply (congrArg e.inv) at hxy
      simpa [e] using hxy
    have hneq : a ≠ b := by
      -- Convert equality in the source colimit to equality of orbit classes and use the diagonal
      -- invariant.
      intro hab
      have hmap :
          colim.map ((FunctorToTypes.binaryProductIso F F).hom) a =
            colim.map ((FunctorToTypes.binaryProductIso F F).hom) b := by
        simpa [hab]
      have hq :
          (Quotient.mk'' ((1 : X), (1 : X)) :
            MulAction.orbitRel.Quotient G (X × X)) =
            Quotient.mk'' ((1 : X), s) := by
        have hqcolim :
            oneObjAction_colimitEquivQuotient G (X × X)
              (colim.map ((FunctorToTypes.binaryProductIso F F).hom) a) =
            oneObjAction_colimitEquivQuotient G (X × X)
              (colim.map ((FunctorToTypes.binaryProductIso F F).hom) b) := by
          exact congrArg (fun z ↦ oneObjAction_colimitEquivQuotient G (X × X) z) hmap
        have hqcolim' :
            colimit.ι (FunctorToTypes.prod F F) (oneObj G) ((1 : X), (1 : X)) =
              colimit.ι (FunctorToTypes.prod F F) (oneObj G) ((1 : X), s) := by
          simpa [a, b, ab, as, FunctorToTypes.prodMk, Types.Colimit.ι_map_apply] using hqcolim
        have hqcolim'' :
            colimit.ι (oneObjActionFunctor G (X × X)) (oneObj G) ((1 : X), (1 : X)) =
              colimit.ι (oneObjActionFunctor G (X × X)) (oneObj G) ((1 : X), s) := by
          simpa [F, oneObjActionFunctor] using hqcolim'
        simpa [oneObjAction_colimitEquivQuotient_ι] using
          congrArg (fun z ↦ oneObjAction_colimitEquivQuotient G (X × X) z) hqcolim''
      exact (diagonal_left_translation_orbit_classes_ne (P := Equiv.Perm Bool) (s := s) hs) hq
    exact hneq (hbij.1 hEqImage)

end CategoryTheory.Limits

/-! ### Lemma_4_19_5 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FunctorToTypes

universe u v

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable (M : I ⥤ AddCommGrpCat.{max u v})

/-
Domain-style sampling for Lemma 4.19.5:
- primary domain: comparison maps between `Type`-colimits and additive colimits
- inspected owner declarations:
  - `colimit.post`
  - `prodComparison_colim_surjective_of_commonSuccessor`
  - `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`
  - `CategoryTheory.epi_iff_surjective`
- source-facing hypotheses: nonemptiness of the index category and common successors for pairs of
  objects
- best owner abstraction: the canonical comparison morphism
  `colimit.post M (forget AddCommGrpCat)`; under the stronger hypothesis `[IsFiltered I]`, the
  filtered-colimit owner `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits` upgrades
  this comparison map to an isomorphism
- canonical bridge reused in the proof: `prodComparison_colim_surjective_of_commonSuccessor`
- primitive data: the additive diagram `M`, the source-level nonemptiness hypothesis `hI`, and
  the source-level common-successor hypothesis
- derived API: the surjectivity and epimorphism consequences for
  `colimit.post M (forget AddCommGrpCat)`
- target layer here: `bridge/view`, namely the surjectivity and epimorphism consequences for the
  comparison map from the `Type`-colimit to the underlying set of the additive colimit; the
  theorem stays at this layer because the source hypotheses are weaker than filteredness
-/

/-- Helper for Lemma 4.19.5: the comparison map from the `Type`-colimit to the additive colimit
agrees with the colimit inclusions on each stage. -/
theorem colimit_post_ι_apply (i : I) (x : (M ⋙ forget AddCommGrpCat).obj i) :
    colimit.post M (forget AddCommGrpCat) (colimit.ι (M ⋙ forget AddCommGrpCat) i x) =
      colimit.ι M i x := by
  -- The comparison map is characterized by compatibility with the colimit cocone.
  simpa using congrFun (colimit.ι_post M (forget AddCommGrpCat) i) x

/-- Helper for Lemma 4.19.5: the zero element of the additive colimit is represented by the zero
element at any stage. -/
theorem zero_single_stage_representative (i : I) :
    colimit.ι M i 0 = (0 : (colimit M : AddCommGrpCat.{max u v})) := by
  -- The colimit inclusion is an additive homomorphism, so it preserves zero.
  simp

/-- Helper for Lemma 4.19.5: the additive inverse of a single-stage representative is represented
at the same stage by the stagewise additive inverse. -/
theorem neg_single_stage_representative (i : I) (x : M.obj i) :
    colimit.ι M i (-x) = -(colimit.ι M i x : (colimit M : AddCommGrpCat.{max u v})) := by
  -- The colimit inclusion is an additive homomorphism, so it preserves negation.
  exact (colimit.ι M i).hom.map_neg x

/-- Helper for Lemma 4.19.5: two single-stage representatives in the additive colimit can be moved
to one common stage and summed there. -/
theorem sum_of_single_stage_representatives
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    {i j : I} (x : M.obj i) (y : M.obj j) :
    ∃ k : I, ∃ z : M.obj k, colimit.ι M k z = colimit.ι M i x + colimit.ι M j y := by
  classical
  let F : I ⥤ Type (max u v) := M ⋙ forget AddCommGrpCat
  let e := Types.binaryProductIso (colimit F) (colimit F)
  have hprodSurj : Function.Surjective (prodComparison colim F F) :=
    prodComparison_colim_surjective_of_commonSuccessor hObj F F
  -- Move the pair of representatives to one stage in the product diagram.
  obtain ⟨w, hw⟩ := hprodSurj (e.inv (colimit.ι F i x, colimit.ι F j y))
  obtain ⟨k, xy, hxy⟩ := Types.jointly_surjective' w
  let xk : M.obj k := (prod.fst : F ⨯ F ⟶ F).app k xy
  let yk : M.obj k := (prod.snd : F ⨯ F ⟶ F).app k xy
  refine ⟨k, xk + yk, ?_⟩
  have hpair :
      prodComparison colim F F (colimit.ι (F ⨯ F) k xy) =
        e.inv (colimit.ι F i x, colimit.ι F j y) := by
    rw [hxy]
    exact hw
  have hpair_fst :
      ((Types.binaryProductIso (colimit F) (colimit F)).hom
        (prodComparison colim F F (colimit.ι (F ⨯ F) k xy))).1 =
        colimit.ι F i x := by
    -- Projecting to the first factor identifies the first transported representative.
    simpa [e] using congrArg (fun p ↦ p.1) (congrArg e.hom hpair)
  have hpair_snd :
      ((Types.binaryProductIso (colimit F) (colimit F)).hom
        (prodComparison colim F F (colimit.ι (F ⨯ F) k xy))).2 =
        colimit.ι F j y := by
    -- Projecting to the second factor does the same for the second representative.
    simpa [e] using congrArg (fun p ↦ p.2) (congrArg e.hom hpair)
  have hxk : colimit.ι F k xk = colimit.ι F i x := by
    rw [← prodComparison_colim_ι_fst F F k xy]
    simpa [xk] using hpair_fst
  have hyk : colimit.ι F k yk = colimit.ι F j y := by
    rw [← prodComparison_colim_ι_snd F F k xy]
    simpa [yk] using hpair_snd
  have hxk' : colimit.ι M k xk = colimit.ι M i x := by
    -- Apply the comparison map to transport the equality back to the additive colimit.
    rw [← colimit_post_ι_apply M k xk, ← colimit_post_ι_apply M i x]
    exact congrArg (colimit.post M (forget AddCommGrpCat)) hxk
  have hyk' : colimit.ι M k yk = colimit.ι M j y := by
    rw [← colimit_post_ι_apply M k yk, ← colimit_post_ι_apply M j y]
    exact congrArg (colimit.post M (forget AddCommGrpCat)) hyk
  -- Once both terms live at one stage, their sum is represented by the stagewise sum.
  calc
    colimit.ι M k (xk + yk) = colimit.ι M k xk + colimit.ι M k yk := by
      exact (colimit.ι M k).hom.map_add xk yk
    _ = colimit.ι M i x + colimit.ι M j y := by
      rw [hxk', hyk']

/-- Helper for Lemma 4.19.5: every element of the additive colimit is already represented by one
element of one stage. -/
theorem every_colimit_element_has_single_stage_representative
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) (z : (colimit M : AddCommGrpCat.{max u v})) :
    ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = z := by
  classical
  let A : AddCommGrpCat.{max u v} := colimit M
  let i0 : I := Classical.choice hI
  let representedSet : Set A := fun a ↦ ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = a
  have hzero : (0 : A) ∈ representedSet := by
    -- Nonemptiness provides a stage at which the zero element represents the colimit zero.
    refine ⟨i0, 0, ?_⟩
    exact zero_single_stage_representative M i0
  have hadd : ∀ {a b : A}, a ∈ representedSet → b ∈ representedSet → a + b ∈ representedSet := by
    intro a b ha hb
    rcases ha with ⟨i, x, rfl⟩
    rcases hb with ⟨j, y, rfl⟩
    -- The common-successor lemma compresses two stage representatives to one.
    exact sum_of_single_stage_representatives M hObj x y
  have hneg : ∀ {a : A}, a ∈ representedSet → -a ∈ representedSet := by
    intro a ha
    rcases ha with ⟨i, x, rfl⟩
    -- Negation is represented at the same stage by the stagewise additive inverse.
    exact ⟨i, -x, neg_single_stage_representative M i x⟩
  let representedSubgroup : AddSubgroup A :=
    { toAddSubmonoid :=
        { carrier := representedSet
          zero_mem' := hzero
          add_mem' := fun ha hb ↦ hadd ha hb }
      neg_mem' := fun ha ↦ hneg ha }
  have hstage_mem : ∀ i : I, ∀ x : M.obj i, colimit.ι M i x ∈ representedSubgroup := by
    intro i x
    simpa [representedSubgroup, representedSet] using
      (show ∃ j : I, ∃ y : M.obj j, colimit.ι M j y = colimit.ι M i x from ⟨i, x, rfl⟩)
  have hmap_zero :
      ∀ i : I, (⟨colimit.ι M i 0, hstage_mem i 0⟩ : representedSubgroup) = 0 := by
    intro i
    apply Subtype.ext
    simp
  have hmap_add :
      ∀ i : I, ∀ x y : M.obj i,
        (⟨colimit.ι M i (x + y), hstage_mem i (x + y)⟩ : representedSubgroup) =
          ⟨colimit.ι M i x, hstage_mem i x⟩ + ⟨colimit.ι M i y, hstage_mem i y⟩ := by
    intro i x y
    apply Subtype.ext
    simp
  let representedMap :
      ∀ i : I, M.obj i ⟶ AddCommGrpCat.of representedSubgroup := fun i ↦
        AddCommGrpCat.ofHom
          { toFun := fun x ↦ ⟨colimit.ι M i x, hstage_mem i x⟩
            map_zero' := hmap_zero i
            map_add' := hmap_add i }
  have hnatural :
      ∀ i j : I, ∀ f : i ⟶ j, M.map f ≫ representedMap j = representedMap i := by
    intro i j f
    ext x
    change (M.map f ≫ colimit.ι M j) x = colimit.ι M i x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (colimit.w M f)) x
  let representedCocone : Cocone M :=
    { pt := AddCommGrpCat.of representedSubgroup
      ι :=
        { app := representedMap
          naturality := fun i j f ↦ hnatural i j f } }
  let representedIncl : AddCommGrpCat.of representedSubgroup ⟶ A :=
    AddCommGrpCat.ofHom representedSubgroup.subtype
  let descRepresented : A ⟶ AddCommGrpCat.of representedSubgroup :=
    colimit.desc M representedCocone
  have hdescRepresented : descRepresented ≫ representedIncl = 𝟙 A := by
    -- Both maps out of the colimit agree on each stage, so they agree globally.
    apply colimit.hom_ext
    intro i
    ext x
    change (((descRepresented ((colimit.ι M i) x) : representedSubgroup) : A)) = colimit.ι M i x
    have hx :
        descRepresented (colimit.ι M i x) = ⟨colimit.ι M i x, hstage_mem i x⟩ := by
      simp [descRepresented, representedCocone, representedMap]
    rw [hx]
  -- The section into the represented subgroup shows every colimit element lies there.
  let y : representedSubgroup := descRepresented z
  have hy : (y : A) = z := by
    simpa [y] using DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hdescRepresented) z
  have hy_mem : representedSet (y : A) := by
    exact y.2
  have hy_repr : ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = (y : A) := by
    simpa [representedSet] using hy_mem
  exact hy.symm ▸ hy_repr

/-- Lemma 4.19.5: if the index category is nonempty and every pair of its objects admits a common
successor, then the canonical comparison map from the colimit of `M` in sets to the underlying set
of the colimit of `M` in abelian groups is surjective. The nonemptiness hypothesis is necessary:
for the empty index category, the source colimit in `Type` is empty while the target is the
underlying singleton set of the zero abelian group. -/
-- Proof sketch: every element of the abelian-group colimit is represented by a finite sum of
-- images from objects of the diagram. The common-successor hypothesis lets us move finitely many
-- representatives to a single stage, where their sum is represented by one element, and that
-- element defines a preimage in the `Type`-colimit.
theorem addCommGrpColimitComparison_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Function.Surjective (colimit.post M (forget AddCommGrpCat)) := by
  -- First represent the target element at a single stage of the additive diagram.
  intro z
  rcases every_colimit_element_has_single_stage_representative M hObj hI z with ⟨i, x, hx⟩
  -- The stage representative lifts directly to the `Type`-colimit through the comparison map.
  refine ⟨colimit.ι (M ⋙ forget AddCommGrpCat) i x, ?_⟩
  exact (colimit_post_ι_apply M i x).trans hx

/-- Categorical reformulation of Lemma 4.19.5 via the canonical `epi_iff_surjective` bridge. -/
theorem addCommGrpColimitComparison_epi_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Epi (colimit.post M (forget AddCommGrpCat)) := by
  simpa using
    (epi_iff_surjective (colimit.post M (forget AddCommGrpCat))).mpr <|
      addCommGrpColimitComparison_surjective_of_commonSuccessor M hObj hI

end CategoryTheory.Limits

/-! ### Lemma_4_19_6 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits
open ConnectedComponents ObjectProperty

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

/-
Source/core/bridge triage for Lemma 4.19.6:
- `source-facing`: `HasSpanCocones`, the span-completion hypothesis appearing in the text.
- `core/canonical`: `IsFilteredOrEmpty` via `IsFiltered.span`, and `HasPushouts` via
  `pushout.inl`, `pushout.inr`, and `pushout.condition`.
- `bridge/view`: `hasSpanCocones_of_isFilteredOrEmpty`, `hasSpanCocones_of_hasPushouts`, and
  `ConnectedComponents.mk_eq_of_hom` together with
  `exists_common_successor_of_isPreconnected`.
- primitive data: the owner field `HasSpanCocones.span`; no separate exact-interface wrapper is
  kept for this field.
-/

class HasSpanCocones (I : Type u) [Category.{v} I] : Prop where
  span {x y z : I} (f : x ⟶ y) (g : x ⟶ z) :
    ∃ (w : I) (fy : y ⟶ w) (gz : z ⟶ w), f ≫ fy = g ≫ gz

instance hasSpanCocones_of_isFilteredOrEmpty [IsFilteredOrEmpty I] :
    HasSpanCocones I where
  span := IsFiltered.span

attribute [instance 100] hasSpanCocones_of_isFilteredOrEmpty

instance hasSpanCocones_of_hasPushouts [HasPushouts I] : HasSpanCocones I where
  span f g := ⟨pushout f g, pushout.inl f g, pushout.inr f g, pushout.condition⟩

attribute [instance 100] hasSpanCocones_of_hasPushouts

namespace ConnectedComponents

/-- A morphism stays inside a single connected component. -/
theorem mk_eq_of_hom {X Y : I} (f : X ⟶ Y) :
    mk X = mk Y := by
  change Quotient.mk'' X = Quotient.mk'' Y
  exact Quotient.sound' (Zigzag.of_hom f)

end ConnectedComponents

/-- Helper for Lemma 4.19.6: a morphism out of an object already lying in a connected
component `j` forces its target to lie in the same component. -/
theorem mk_eq_component_of_target_hom {j : ConnectedComponents I} {Y W : I}
    (hY : mk Y = j) (f : Y ⟶ W) : mk W = j := by
  -- Move the target back to the known source component using the canonical quotient equality.
  calc
    mk W = mk Y := (ConnectedComponents.mk_eq_of_hom f).symm
    _ = j := hY

/- Companion recall: `CategoryTheory.decomposedEquiv` is the canonical equivalence expressing any
category as the disjoint union of its connected components. -/
recall CategoryTheory.decomposedEquiv

section

variable [HasSpanCocones I]

/-- In a preconnected category satisfying the span-cocone hypothesis, any two objects admit a
common successor. -/
theorem exists_common_successor_of_isPreconnected [IsPreconnected I] (X Y : I) :
    ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  let r : I → I → Prop := fun X Y ↦ ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z)
  have hr : _root_.Equivalence r := by
    refine ⟨?_, ?_, ?_⟩
    · intro X
      exact ⟨X, ⟨𝟙 X⟩, ⟨𝟙 X⟩⟩
    · intro X Y
      rintro ⟨Z, hX, hY⟩
      exact ⟨Z, hY, hX⟩
    · intro X Y Z
      rintro ⟨W₁, hX, hY₁⟩ ⟨W₂, hY₂, hZ⟩
      obtain ⟨f⟩ := hY₁
      obtain ⟨g⟩ := hY₂
      obtain ⟨hXW₁⟩ := hX
      obtain ⟨hZW₂⟩ := hZ
      obtain ⟨W, k₁, k₂, _⟩ := HasSpanCocones.span f g
      exact ⟨W, ⟨hXW₁ ≫ k₁⟩, ⟨hZW₂ ≫ k₂⟩⟩
  exact equiv_relation r hr (fun {_ Y} f ↦ ⟨Y, ⟨f⟩, ⟨𝟙 Y⟩⟩) X Y

-- Proof sketch: a span inside a connected component is still a span in the ambient category, so
-- choose an ambient square completion; then show its cocone point lies in the same connected
-- component because it receives morphisms from objects already in that component.
/-- Lemma 4.19.6: in the canonical decomposition `CategoryTheory.decomposedEquiv`, each connected
component again satisfies the source-text span-completion condition. -/
theorem connected_components_have_span_cocones (j : ConnectedComponents I) : HasSpanCocones j.Component where
  span := by
    intro x y z f g
    -- Forget the componentwise span to the ambient category and complete it there.
    obtain ⟨w, fy, gz, hfg⟩ := HasSpanCocones.span f.hom g.hom
    -- Pull the ambient apex back into the same component using the map from `y`.
    have hw : mk w = j := mk_eq_component_of_target_hom y.property fy
    let w' : j.Component := ⟨w, hw⟩
    let fy' : y ⟶ w' := homMk fy
    let gz' : z ⟶ w' := homMk gz
    -- The lifted maps commute because equality in the full subcategory is detected ambiently.
    have hfg' : f ≫ fy' = g ≫ gz' := by
      apply hom_ext
      simpa [fy', gz'] using hfg
    exact ⟨w', fy', gz', hfg'⟩

/-- Each connected component inherits span cocones from the ambient category. -/
instance (j : ConnectedComponents I) : HasSpanCocones j.Component :=
  connected_components_have_span_cocones j

/-- Corollary form of Lemma 4.19.6: either `I` is empty, or its canonical indexing type of
connected components is nonempty and every component inherits span cocones. -/
theorem isEmpty_or_nonempty_connected_components_have_span_cocones
    : IsEmpty I ∨
        Nonempty (ConnectedComponents I) ∧
          ∀ j : ConnectedComponents I, HasSpanCocones j.Component := by
  rcases isEmpty_or_nonempty I with hI | hI
  · exact Or.inl hI
  · exact Or.inr ⟨hI.map mk, fun j ↦ inferInstance⟩

end

end CategoryTheory
