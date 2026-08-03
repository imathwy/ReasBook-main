module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Order

public section

open scoped Topology

universe u

/-- Helper for Remark 22.3: every point lies in the first-coordinate image of a function graph. -/
private lemma mem_fst_image_graph {α β : Type*} (f : α → β) (x : α) :
    x ∈ Prod.fst '' {z : α × β | z.2 = f z.1} := by
  -- The graph point `(x, f x)` projects to `x`.
  exact ⟨(x, f x), rfl, rfl⟩

/-- Helper for Remark 22.3: on a function graph, the second coordinate is the function value. -/
private lemma graph_snd_eq {α β : Type*} (f : α → β)
    (z : {z : α × β | z.2 = f z.1}) : f z.val.1 = z.val.2 := by
  -- The graph membership equation gives the desired equality in the reverse direction.
  exact z.property.symm

/-- Helper for Remark 22.3: a quotient first projection restricted to a graph forces the
graphing function to be continuous. -/
private lemma continuous_of_isQuotientMap_restrictFst_graph
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (f : α → β)
    (hquot : Topology.IsQuotientMap
      (Set.MapsTo.restrict Prod.fst {z : α × β | z.2 = f z.1}
        (Prod.fst '' {z : α × β | z.2 = f z.1})
        (Set.mapsTo_image Prod.fst {z : α × β | z.2 = f z.1}))) :
    Continuous f := by
  let graph : Set (α × β) := {z | z.2 = f z.1}
  let image : Set α := Prod.fst '' graph
  let induced : image → β := fun y ↦ f y.1
  let graphSection : α → image := fun x ↦ ⟨x, mem_fst_image_graph f x⟩
  have hcomp : Continuous
      (induced ∘ Set.MapsTo.restrict Prod.fst graph image
        (Set.mapsTo_image Prod.fst graph)) := by
    -- The composite on the graph is the continuous second projection.
    refine (continuous_snd.comp continuous_subtype_val).congr ?_
    intro z
    exact (graph_snd_eq f z).symm
  have hinduced : Continuous induced := hquot.continuous_iff.mpr hcomp
  have hsection : Continuous graphSection := by
    -- The first-coordinate image of the graph is all of the domain.
    exact Continuous.subtype_mk continuous_id fun x ↦ mem_fst_image_graph f x
  -- The induced map composed with the canonical section is definitionally `f`.
  exact hinduced.comp hsection

/-- Helper for Remark 22.3: negation is not continuous for the Sierpiński topology on `Prop`. -/
private lemma sierpinskiNegation_not_continuous :
    ¬ Continuous (fun x : Prop ↦ ¬ x) := by
  rw [continuous_Prop]
  intro hopen
  have hfalse : False ∈ {x : Prop | ¬ x} := fun h ↦ h
  -- The neighborhood characterization at `False` would make this proper set universal.
  have huniv : {x : Prop | ¬ x} = Set.univ := by
    simpa [nhds_false] using hopen.mem_nhds hfalse
  have htrue : True ∈ {x : Prop | ¬ x} := huniv.symm ▸ Set.mem_univ True
  exact htrue True.intro

/-- Helper for Remark 22.3: lifted Sierpiński negation is discontinuous in every universe. -/
private lemma uliftSierpinskiNegation_not_continuous :
    ¬ Continuous (fun x : ULift.{u} Prop ↦ ULift.up (¬ x.down)) := by
  intro hcontinuous
  -- Composing with the lift homeomorphism would make ordinary negation continuous.
  exact sierpinskiNegation_not_continuous
    (continuous_uliftDown.comp (hcontinuous.comp continuous_uliftUp))

/-- Remark 22.3: There is a quotient map `p : X → Y` whose restriction to a
subspace `A`, corestricted to `p '' A`, is not a quotient map. -/
theorem exists_quotientMap_restrictImage_not_isQuotientMap :
    ∃ (X Y : TopCat.{u}) (p : X → Y) (A : Set X),
      Topology.IsQuotientMap p ∧
        ¬ Topology.IsQuotientMap
          (Set.MapsTo.restrict p A (p '' A) (Set.mapsTo_image p A)) := by
  -- Use the first projection and restrict it to the graph of discontinuous negation.
  refine ⟨TopCat.of (ULift.{u} Prop × ULift.{u} Prop), TopCat.of (ULift.{u} Prop),
    TopCat.ofHom ContinuousMap.fst,
    {z : ULift.{u} Prop × ULift.{u} Prop | z.2 = ULift.up (¬ z.1.down)}, ?_, ?_⟩
  · exact isQuotientMap_fst
  · intro hquot
    -- A quotient restriction to this graph would force lifted negation to be continuous.
    exact uliftSierpinskiNegation_not_continuous
      (continuous_of_isQuotientMap_restrictFst_graph
        (fun x : ULift.{u} Prop ↦ ULift.up (¬ x.down)) hquot)
