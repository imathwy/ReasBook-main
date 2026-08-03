module

public import Topology_Munkres_2000.Book.Theorem_71_1.LoopClass
public import Topology_Munkres_2000.Book.Lemma_71_2
public import Topology_Munkres_2000.Book.Lemma_55_1
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_58_7
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Topology_Munkres_2000.Book.Theorem_71_1
import all Topology_Munkres_2000.Book.Theorem_71_1.LoopClass

public section

universe u v

open Path.Homotopic.Quotient Topology

/-- Helper for Theorem 71.3: the subspace formed by the circles whose indices lie in `A`. -/
private def circleSubwedge {J : Type v} {X : Type u}
    (S : J → Set X) (A : Set J) : Set X :=
  ⋃ α : A, S α.1

/-- Helper for Theorem 71.3: a selected circle regarded as a subspace of its subwedge. -/
private def circleSubwedgeComponent {J : Type v} {X : Type u}
    (S : J → Set X) (A : Set J) (α : A) : Set (circleSubwedge S A) :=
  Subtype.val ⁻¹' S α.1

/-- Helper for Theorem 71.3: every selected circle lies in its associated subwedge. -/
private lemma circleSubwedgeComponent_subset {J : Type v} {X : Type u}
    (S : J → Set X) (A : Set J) (α : A) :
    S α.1 ⊆ circleSubwedge S A := by
  -- Insert the point into the union at the selected index.
  intro x hx
  exact Set.mem_iUnion.mpr ⟨α, hx⟩

/-- Helper for Theorem 71.3: the common wedge point belongs to every nonempty subwedge. -/
private lemma circleSubwedge_mem_basepoint
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) : p ∈ circleSubwedge S A := by
  -- Any selected component contains the common point.
  obtain ⟨α, hα⟩ := hA
  exact Set.mem_iUnion.mpr
    ⟨⟨α, hα⟩, IsWedgeOfCircles.mem_basepoint α⟩

/-- Helper for Theorem 71.3: the common point as a point of a nonempty subwedge. -/
private def circleSubwedgePoint
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) : circleSubwedge S A :=
  ⟨p, circleSubwedge_mem_basepoint S p A hA⟩

/-- Helper for Theorem 71.3: collapse every circle outside a nonempty selected
subwedge to the common wedge point. -/
private noncomputable def circleSubwedgeProjection
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (x : X) : circleSubwedge S A :=
  letI : Decidable (x ∈ circleSubwedge S A) :=
    Classical.propDecidable (x ∈ circleSubwedge S A)
  if hx : x ∈ circleSubwedge S A then ⟨x, hx⟩ else circleSubwedgePoint S p A hA

/-- Helper for Theorem 71.3: the subwedge projection fixes every point already
in the selected subwedge. -/
private lemma circleSubwedgeProjection_of_mem
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (x : X) (hx : x ∈ circleSubwedge S A) :
    circleSubwedgeProjection S p A hA x = ⟨x, hx⟩ := by
  -- The selected branch has the same underlying ambient point.
  apply Subtype.ext
  simp only [circleSubwedgeProjection, dif_pos hx]

/-- Helper for Theorem 71.3: on an unselected component, the subwedge projection
is constantly the wedge point. -/
private lemma circleSubwedgeProjection_of_not_mem_index
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (α : J) (hα : α ∉ A) (x : S α) :
    circleSubwedgeProjection S p A hA x = circleSubwedgePoint S p A hA := by
  -- If the point also lies in a selected circle, the wedge intersection axiom
  -- forces it to be the common point; otherwise collapse is by definition.
  by_cases hx : (x : X) ∈ circleSubwedge S A
  · obtain ⟨β, hxβ⟩ := Set.mem_iUnion.mp hx
    have hαβ : α ≠ β.1 := by
      intro h
      exact hα (h ▸ β.2)
    have hxinter : (x : X) ∈ S α ∩ S β.1 := ⟨x.property, hxβ⟩
    rw [IsWedgeOfCircles.inter_eq (S := S) (p := p) hαβ] at hxinter
    calc
      circleSubwedgeProjection S p A hA x =
          ⟨(x : X), hx⟩ := circleSubwedgeProjection_of_mem S p A hA x hx
      _ = circleSubwedgePoint S p A hA := by
        apply Subtype.ext
        exact Set.mem_singleton_iff.mp hxinter
  · simp only [circleSubwedgeProjection, dif_neg hx]

/-- Helper for Theorem 71.3: collapse onto a nonempty subwedge is continuous. -/
private lemma continuous_circleSubwedgeProjection
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [h : IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    Continuous (circleSubwedgeProjection S p A hA) := by
  -- Coherence reduces continuity to the restriction on each component circle.
  rw [h.isCoherentWith.continuous_iff]
  rintro _ ⟨α, rfl⟩
  rw [continuousOn_iff_continuous_restrict]
  by_cases hα : α ∈ A
  · have hcomponent (x : S α) : (x : X) ∈ circleSubwedge S A :=
      Set.mem_iUnion.mpr ⟨⟨α, hα⟩, x.property⟩
    have hrestriction :
        (fun x : S α ↦ circleSubwedgeProjection S p A hA x) =
          fun x : S α ↦ ⟨(x : X), hcomponent x⟩ := by
      funext x
      exact circleSubwedgeProjection_of_mem S p A hA x (hcomponent x)
    have hcontinuous : Continuous (fun x : S α ↦
        (⟨(x : X), hcomponent x⟩ : circleSubwedge S A)) :=
      continuous_subtype_val.subtype_mk hcomponent
    rw [← hrestriction] at hcontinuous
    exact hcontinuous.congr (fun _ ↦ rfl)
  · have hrestriction :
        (fun x : S α ↦ circleSubwedgeProjection S p A hA x) =
          fun _ ↦ circleSubwedgePoint S p A hA := by
      funext x
      exact circleSubwedgeProjection_of_not_mem_index S p A hA α hα x
    have hcontinuous : Continuous (fun _ : S α ↦ circleSubwedgePoint S p A hA) :=
      continuous_const
    rw [← hrestriction] at hcontinuous
    exact hcontinuous.congr (fun _ ↦ rfl)

/-- Helper for Theorem 71.3: the collapse onto a nonempty subwedge as a bundled
continuous map. -/
private noncomputable def circleSubwedgeProjectionMap
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) : C(X, circleSubwedge S A) :=
  ⟨circleSubwedgeProjection S p A hA,
    continuous_circleSubwedgeProjection S p A hA⟩

/-- Helper for Theorem 71.3: inclusion of a circle subwedge into the ambient
wedge as a bundled continuous map. -/
private def circleSubwedgeInclusion
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (A : Set J) : C(circleSubwedge S A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Theorem 71.3: subwedge inclusion sends the selected subwedge
point to the ambient wedge point. -/
private lemma circleSubwedgeInclusion_basepoint
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    circleSubwedgeInclusion S A (circleSubwedgePoint S p A hA) = p := by
  -- Both sides have the same underlying ambient point by construction.
  rfl

/-- Helper for Theorem 71.3: the endpoint-adjusted homomorphism induced by
including a nonempty circle subwedge into the ambient wedge. -/
private noncomputable def circleSubwedgeInclusionHom
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    FundamentalGroup (circleSubwedge S A) (circleSubwedgePoint S p A hA) →*
      FundamentalGroup X p :=
  FundamentalGroup.mapOfEq (circleSubwedgeInclusion S A)
    (circleSubwedgeInclusion_basepoint S p A hA)

/-- Helper for Theorem 71.3: changing both endpoints of a path-homotopy class
along fixed equalities is injective. -/
private lemma pathHomotopicQuotientCast_injective
    {Y : Type u} [TopologicalSpace Y] {x y x' y' : Y}
    (hx : x' = x) (hy : y' = y) :
    Function.Injective
      (fun q : Path.Homotopic.Quotient x y ↦ q.cast hx hy) := by
  -- After eliminating the endpoint equalities, the cast is the identity.
  rintro a b hab
  cases hx
  cases hy
  simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using hab

/-- Helper for Theorem 71.3: collapse followed after subwedge inclusion is the
identity on the selected subwedge. -/
private lemma circleSubwedgeProjectionMap_leftInverse
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    Function.LeftInverse (circleSubwedgeProjectionMap S p A hA)
      (circleSubwedgeInclusion S A) := by
  intro x
  -- The projection's selected branch fixes the underlying point, and subtype
  -- extensionality discards the possibly different membership proof.
  exact circleSubwedgeProjection_of_mem S p A hA x x.property

/-- Helper for Theorem 71.3: inclusion of a nonempty circle subwedge induces
an injective homomorphism on fundamental groups. -/
private lemma circleSubwedgeInclusionHom_injective
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    Function.Injective (circleSubwedgeInclusionHom S p A hA) := by
  -- The endpoint cast is bijective; after normalizing its proof to reflexivity,
  -- injectivity is exactly injectivity of the raw induced map.
  have hinclusion := FundamentalGroup.mapInjectiveOfLeftInverse
    (circleSubwedgeInclusion S A)
    (circleSubwedgeProjectionMap S p A hA)
    (circleSubwedgeProjectionMap_leftInverse S p A hA)
    (circleSubwedgePoint S p A hA)
  intro a b hab
  have ha : circleSubwedgeInclusionHom S p A hA a =
      (Path.Homotopic.Quotient.map a (circleSubwedgeInclusion S A)).cast
        (circleSubwedgeInclusion_basepoint S p A hA).symm
        (circleSubwedgeInclusion_basepoint S p A hA).symm := by
    unfold circleSubwedgeInclusionHom
    exact FundamentalGroup.mapOfEq_apply _ _ _
  have hb : circleSubwedgeInclusionHom S p A hA b =
      (Path.Homotopic.Quotient.map b (circleSubwedgeInclusion S A)).cast
        (circleSubwedgeInclusion_basepoint S p A hA).symm
        (circleSubwedgeInclusion_basepoint S p A hA).symm := by
    unfold circleSubwedgeInclusionHom
    exact FundamentalGroup.mapOfEq_apply _ _ _
  have hcast := ha.symm.trans (hab.trans hb)
  have hmap := pathHomotopicQuotientCast_injective
    (circleSubwedgeInclusion_basepoint S p A hA).symm
    (circleSubwedgeInclusion_basepoint S p A hA).symm hcast
  apply hinclusion
  rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
  exact hmap

/-- Helper for Theorem 71.3: the selected components cover their subwedge. -/
private lemma circleSubwedgeComponent_covers
    {J : Type v} {X : Type u} (S : J → Set X) (A : Set J) :
    ⋃ α : A, circleSubwedgeComponent S A α = Set.univ := by
  -- Membership in the outer subtype is precisely membership in one selected circle.
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨α, hx⟩ := Set.mem_iUnion.mp x.property
    exact Set.mem_iUnion.mpr ⟨α, hx⟩

/-- Helper for Theorem 71.3: each selected component is homeomorphic to its original circle. -/
private lemma circleSubwedgeComponent_homeomorphic_circle
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (α : A) :
    Nonempty (circleSubwedgeComponent S A α ≃ₜ Circle) := by
  -- Forgetting the two subtype layers embeds this component with range `S α`.
  let inclusion : circleSubwedgeComponent S A α → X := fun x ↦ x.1.1
  have hinclusion : IsEmbedding inclusion :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hrange : Set.range inclusion = S α.1 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      have hxSubwedge : x ∈ circleSubwedge S A :=
        circleSubwedgeComponent_subset S A α hx
      exact ⟨⟨⟨x, hxSubwedge⟩, hx⟩, rfl⟩
  obtain ⟨e⟩ := IsWedgeOfCircles.homeomorphic_circle (S := S) (p := p) α.1
  exact ⟨hinclusion.toHomeomorph.trans (Homeomorph.setCongr hrange) |>.trans e⟩

/-- Helper for Theorem 71.3: distinct selected components meet only at the subwedge point. -/
private lemma circleSubwedgeComponent_inter_eq
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) :
    Pairwise (fun α β : A ↦
      circleSubwedgeComponent S A α ∩ circleSubwedgeComponent S A β =
        {circleSubwedgePoint S p A hA}) := by
  intro α β hαβ
  have hval : α.1 ≠ β.1 := by
    intro h
    exact hαβ (Subtype.ext h)
  ext x
  constructor
  · intro hx
    have hxAmbient : (x.1 : X) ∈ S α.1 ∩ S β.1 := hx
    rw [IsWedgeOfCircles.inter_eq (S := S) (p := p) hval] at hxAmbient
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact Set.mem_singleton_iff.mp hxAmbient
  · intro hx
    have hxp : x = circleSubwedgePoint S p A hA :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨IsWedgeOfCircles.mem_basepoint (S := S) (p := p) α.1,
      IsWedgeOfCircles.mem_basepoint (S := S) (p := p) β.1⟩

/-- Helper for Theorem 71.3: the circles in a finite nonempty subwedge form a finite wedge. -/
private lemma finiteCircleSubwedge_isFiniteWedge
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (F : Finset J) (hF : F.Nonempty) :
    IsFiniteWedgeOfCircles
      (circleSubwedgeComponent S (F : Set J))
      (circleSubwedgePoint S p (F : Set J) hF) := by
  -- Normality of the ambient wedge supplies the inherited Hausdorff structure.
  letI : T4Space X := IsWedgeOfCircles.t4Space (inferInstance : IsWedgeOfCircles S p)
  letI : T2Space (circleSubwedge S (F : Set J)) := inferInstance
  exact IsFiniteWedgeOfCircles.of
    (circleSubwedgeComponent_covers S (F : Set J))
    (circleSubwedgeComponent_homeomorphic_circle S p (F : Set J))
    (circleSubwedgeComponent_inter_eq S p (F : Set J) hF)

/-- Helper for Theorem 71.3: reindexing a finite wedge of circles along an
equivalence preserves the finite-wedge structure. -/
private lemma finiteCircleWedge_reindex
    {ι : Type v} {κ : Type*} [Fintype ι] [Fintype κ]
    {X : Type u} [TopologicalSpace X]
    (S : ι → Set X) (p : X) (e : κ ≃ ι)
    (h : IsFiniteWedgeOfCircles S p) :
    IsFiniteWedgeOfCircles (fun k ↦ S (e k)) p := by
  letI : T2Space X := h.t2Space
  refine IsFiniteWedgeOfCircles.of ?_ ?_ ?_
  · -- Surjectivity of the reindexing equivalence preserves the covering union.
    rw [← h.covers]
    ext x
    constructor
    · rintro hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e k, hxk⟩
    · rintro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa only [e.apply_symm_apply] using hxi⟩
  · -- Each reindexed component is literally one of the original circles.
    exact fun k ↦ h.homeomorphic_circle (e k)
  · -- Injectivity of the equivalence transports the pairwise intersection law.
    intro i j hij
    exact h.inter_eq (fun heq ↦ hij (e.injective heq))

/-- Helper for Theorem 71.3: nonemptiness of a finset gives nonemptiness of
its carrier viewed as a set. -/
private lemma finsetCoe_nonempty {J : Type v} {F : Finset J}
    (hF : F.Nonempty) : (F : Set J).Nonempty := by
  -- Repackage the same witness with set-membership notation.
  obtain ⟨α, hα⟩ := hF
  exact ⟨α, hα⟩

/-- Helper for Theorem 71.3: nonemptiness of a finset carrier as a set gives
nonemptiness of the finset. -/
private lemma finsetNonempty_of_coe_nonempty {J : Type v} {F : Finset J}
    (hF : (F : Set J).Nonempty) : F.Nonempty := by
  -- The set-level witness carries exactly the finset-membership proof required.
  obtain ⟨α, hα⟩ := hF
  exact ⟨α, hα⟩

/-- Helper for Theorem 71.3: every free-group word is induced from the free group
on some finite set of its letters. -/
private lemma FreeGroup.exists_finset_factorization {J : Type v} (w : FreeGroup J) :
    ∃ F : Finset J, ∃ wF : FreeGroup F, FreeGroup.map Subtype.val wF = w := by
  classical
  -- Build finite support simultaneously with the word by free-group induction.
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact ⟨∅, 1, FreeGroup.map_one _⟩
  · intro x
    let xF : ({x} : Finset J) := ⟨x, Finset.mem_singleton.mpr rfl⟩
    refine ⟨{x}, FreeGroup.of xF, ?_⟩
    rw [FreeGroup.map.of]
  · intro x hx
    obtain ⟨F, wF, hwF⟩ := hx
    refine ⟨F, wF⁻¹, ?_⟩
    rw [(FreeGroup.map Subtype.val).map_inv, hwF]
  · intro x y hx hy
    obtain ⟨F, wF, hwF⟩ := hx
    obtain ⟨G, wG, hwG⟩ := hy
    have hF (z : F) : z.1 ∈ F ∪ G := Finset.mem_union_left G z.property
    have hG (z : G) : z.1 ∈ F ∪ G := Finset.mem_union_right F z.property
    let includeF : F → (F ∪ G : Finset J) := fun z ↦ ⟨z.1, hF z⟩
    let includeG : G → (F ∪ G : Finset J) := fun z ↦ ⟨z.1, hG z⟩
    let wUnion : FreeGroup (F ∪ G : Finset J) :=
      FreeGroup.map includeF wF * FreeGroup.map includeG wG
    have hmapF :
        FreeGroup.map Subtype.val (FreeGroup.map includeF wF) =
          FreeGroup.map Subtype.val wF := by
      rw [FreeGroup.map.comp]
      congr 1
    have hmapG :
        FreeGroup.map Subtype.val (FreeGroup.map includeG wG) =
          FreeGroup.map Subtype.val wG := by
      rw [FreeGroup.map.comp]
      congr 1
    -- The two finite supports embed into their union without changing letters.
    refine ⟨F ∪ G, wUnion, ?_⟩
    unfold wUnion
    rw [(FreeGroup.map Subtype.val).map_mul, hmapF, hmapG, hwF, hwG]

/-- Helper for Theorem 71.3: every component circle admits a based loop whose
fundamental-group class generates the component fundamental group. -/
private lemma existsCircleWedgeGeneratorLoops
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p] :
    ∃ f : ∀ α, Path
        (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
        ⟨p, IsWedgeOfCircles.mem_basepoint α⟩,
      ∀ α, Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α))) = ⊤ := by
  classical
  have componentCyclic (α : J) :
      IsCyclic (FundamentalGroup (S α)
        ⟨p, IsWedgeOfCircles.mem_basepoint α⟩) := by
    -- Circle coordinates and basepoint change identify this group with `Multiplicative ℤ`.
    obtain ⟨e⟩ := IsWedgeOfCircles.homeomorphic_circle (S := S) (p := p) α
    let coordinates :=
      (e.fundamentalGroupMulEquiv
        ⟨p, IsWedgeOfCircles.mem_basepoint α⟩).trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
          (e ⟨p, IsWedgeOfCircles.mem_basepoint α⟩) 1).trans
          Circle.fundamentalGroupEquivInt)
    exact coordinates.isCyclic.mpr inferInstance
  choose g hg using fun α ↦
    isCyclic_iff_exists_zpowers_eq_top.mp (componentCyclic α)
  choose f hf using fun α ↦
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath (g α))
  refine ⟨f, ?_⟩
  intro α
  -- Replace the selected quotient representative by its chosen cyclic generator.
  have hclass : FundamentalGroup.fromPath (mk (f α)) = g α := hf α
  rw [hclass]
  exact hg α

/-- Helper for Theorem 71.3: a loop whose range lies in a circle subwedge
lifts continuously to that subwedge. -/
private lemma continuous_circleSubwedgeLoopLift
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    Continuous (fun t ↦
      (⟨q t, hq (Set.mem_range_self t)⟩ : circleSubwedge S A)) := by
  -- Subtype continuity follows from continuity of the ambient loop.
  exact q.continuous.subtype_mk _

/-- Helper for Theorem 71.3: the lifted subwedge loop starts at the selected
copy of the common wedge point. -/
private lemma circleSubwedgeLoopLift_source
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    (⟨q 0, hq (Set.mem_range_self 0)⟩ : circleSubwedge S A) =
      circleSubwedgePoint S p A hA := by
  -- Forgetting membership reduces the endpoint claim to `q.source`.
  exact Subtype.ext q.source

/-- Helper for Theorem 71.3: the lifted subwedge loop ends at the selected
copy of the common wedge point. -/
private lemma circleSubwedgeLoopLift_target
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    (⟨q 1, hq (Set.mem_range_self 1)⟩ : circleSubwedge S A) =
      circleSubwedgePoint S p A hA := by
  -- Forgetting membership reduces the endpoint claim to `q.target`.
  exact Subtype.ext q.target

/-- Helper for Theorem 71.3: a loop supported in a subwedge, regarded as a
based loop in that subwedge. -/
private def circleSubwedgeLoopLift
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    Path (circleSubwedgePoint S p A hA) (circleSubwedgePoint S p A hA) :=
  { toFun := fun t ↦ ⟨q t, hq (Set.mem_range_self t)⟩
    continuous_toFun := continuous_circleSubwedgeLoopLift S p A q hq
    source' := circleSubwedgeLoopLift_source S p A hA q hq
    target' := circleSubwedgeLoopLift_target S p A hA q hq }

/-- Helper for Theorem 71.3: forgetting the subwedge membership from the
lifted loop recovers the original ambient loop. -/
private lemma circleSubwedgeLoopLift_map_inclusion
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    (circleSubwedgeLoopLift S p A hA q hq).map continuous_subtype_val = q := by
  -- Both paths have the same ambient value at every parameter.
  ext t
  rfl

/-- Helper for Theorem 71.3: the class of a loop supported in a subwedge lies
in the range of the inclusion-induced homomorphism. -/
private lemma loopClass_mem_circleSubwedgeInclusionRange
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (q : Path p p)
    (hq : Set.range q ⊆ circleSubwedge S A) :
    FundamentalGroup.fromPath (mk q) ∈ Set.range
      (circleSubwedgeInclusionHom S p A hA) := by
  -- The concrete subtype-valued loop supplies the required preimage class.
  refine ⟨FundamentalGroup.fromPath
    (mk (circleSubwedgeLoopLift S p A hA q hq)), ?_⟩
  rw [circleSubwedgeInclusionHom, FundamentalGroup.mapOfEq_apply]
  apply Quotient.sound
  -- Endpoint casts do not alter the underlying path, and inclusion forgets
  -- exactly the membership proof added by the lift.
  suffices hpath :
      ((circleSubwedgeLoopLift S p A hA q hq).map
          (circleSubwedgeInclusion S A).continuous).cast
            (circleSubwedgeInclusion_basepoint S p A hA).symm
            (circleSubwedgeInclusion_basepoint S p A hA).symm = q by
    exact Eq.mp (congrArg (fun r ↦ r.Homotopic q) hpath.symm)
      (Path.Homotopic.refl q)
  ext t
  rfl

/-- Helper for Theorem 71.3: forgetting the subwedge layer sends a selected
component back to its original circle. -/
private def circleSubwedgeComponentToCircle
    {J : Type v} {X : Type u} (S : J → Set X) (A : Set J) (α : A) :
    circleSubwedgeComponent S A α → S α.1 :=
  fun x ↦ ⟨x.1.1, x.2⟩

/-- Helper for Theorem 71.3: a point of a selected circle determines the
corresponding point of the circle inside its subwedge. -/
private def circleToSubwedgeComponent
    {J : Type v} {X : Type u} (S : J → Set X) (A : Set J) (α : A) :
    S α.1 → circleSubwedgeComponent S A α :=
  fun x ↦ ⟨⟨x.1, circleSubwedgeComponent_subset S A α x.2⟩, x.2⟩

/-- Helper for Theorem 71.3: forgetting the subwedge layer after inserting a
circle point is the identity. -/
private lemma circleSubwedgeComponentToCircle_leftInverse
    {J : Type v} {X : Type u} (S : J → Set X) (A : Set J) (α : A) :
    Function.LeftInverse (circleSubwedgeComponentToCircle S A α)
      (circleToSubwedgeComponent S A α) := by
  intro x
  -- Both points have the same ambient coordinate.
  exact Subtype.ext rfl

/-- Helper for Theorem 71.3: inserting a selected-circle point after forgetting
the subwedge layer is the identity. -/
private lemma circleToSubwedgeComponent_leftInverse
    {J : Type v} {X : Type u} (S : J → Set X) (A : Set J) (α : A) :
    Function.LeftInverse (circleToSubwedgeComponent S A α)
      (circleSubwedgeComponentToCircle S A α) := by
  intro x
  -- Nested subtype extensionality discards both membership witnesses.
  apply Subtype.ext
  exact Subtype.ext rfl

/-- Helper for Theorem 71.3: insertion of a selected circle into its subwedge
component is continuous. -/
private lemma continuous_circleToSubwedgeComponent
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (A : Set J) (α : A) :
    Continuous (circleToSubwedgeComponent S A α) := by
  -- Build continuity through the two nested subtype constructors.
  exact (continuous_subtype_val.subtype_mk
    (fun x ↦ circleSubwedgeComponent_subset S A α x.2)).subtype_mk
      (fun x ↦ x.2)

/-- Helper for Theorem 71.3: forgetting the subwedge layer from a selected
component is continuous. -/
private lemma continuous_circleSubwedgeComponentToCircle
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (A : Set J) (α : A) :
    Continuous (circleSubwedgeComponentToCircle S A α) := by
  -- The ambient coordinate is the composite of the two subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x ↦ x.2)

/-- Helper for Theorem 71.3: a selected original circle is canonically
homeomorphic to its component inside the associated subwedge. -/
private def circleToSubwedgeComponentHomeomorph
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (A : Set J) (α : A) :
    S α.1 ≃ₜ circleSubwedgeComponent S A α :=
  Homeomorph.mk
    (Equiv.mk (circleToSubwedgeComponent S A α)
      (circleSubwedgeComponentToCircle S A α)
      (circleSubwedgeComponentToCircle_leftInverse S A α)
      (circleToSubwedgeComponent_leftInverse S A α))
    (continuous_circleToSubwedgeComponent S A α)
    (continuous_circleSubwedgeComponentToCircle S A α)

/-- Helper for Theorem 71.3: the common point regarded as a point of a selected
component inside a subwedge. -/
private abbrev circleSubwedgeComponentPoint
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (α : A) :
    circleSubwedgeComponent S A α :=
  ⟨circleSubwedgePoint S p A hA,
    IsWedgeOfCircles.mem_basepoint (S := S) (p := p) α.1⟩

/-- Helper for Theorem 71.3: the canonical component homeomorphism preserves
the common wedge point. -/
private lemma circleToSubwedgeComponentHomeomorph_basepoint
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (A : Set J) (hA : A.Nonempty) (α : A) :
    circleToSubwedgeComponentHomeomorph S A α
        (⟨p, IsWedgeOfCircles.mem_basepoint α.1⟩ : S α.1) =
      circleSubwedgeComponentPoint S p A hA α := by
  -- Both nested subtype points have ambient coordinate `p`.
  apply Subtype.ext
  exact Subtype.ext rfl

/-- Helper for Theorem 71.3: transport a prescribed component loop to the
corresponding component of a finite subwedge. -/
private noncomputable def circleSubwedgeGeneratorLoop
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (A : Set J) (hA : A.Nonempty) (α : A) :
    Path (circleSubwedgeComponentPoint S p A hA α)
      (circleSubwedgeComponentPoint S p A hA α) :=
  ((f α.1).map (circleToSubwedgeComponentHomeomorph S A α).continuous).cast
    (circleToSubwedgeComponentHomeomorph_basepoint S p A hA α).symm
    (circleToSubwedgeComponentHomeomorph_basepoint S p A hA α).symm

/-- Helper for Theorem 71.3: the induced component homeomorphism sends the
original loop class to its transported subwedge loop class. -/
private lemma circleSubwedgeGeneratorLoop_fromPath
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (A : Set J) (hA : A.Nonempty) (α : A) :
    FundamentalGroup.mapOfEq
        ⟨circleToSubwedgeComponentHomeomorph S A α,
          (circleToSubwedgeComponentHomeomorph S A α).continuous⟩
        (circleToSubwedgeComponentHomeomorph_basepoint S p A hA α)
        (FundamentalGroup.fromPath (mk (f α.1))) =
      FundamentalGroup.fromPath
        (mk (circleSubwedgeGeneratorLoop S p f A hA α)) := by
  -- Expand the induced map and expose the mapped-and-cast path representative.
  rw [FundamentalGroup.mapOfEq_apply, ← mk_map, ← mk_cast]
  rfl

/-- Helper for Theorem 71.3: transport into a selected subwedge component
preserves the property of generating the cyclic fundamental group. -/
private lemma circleSubwedgeGeneratorLoop_zpowers
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (hf : ∀ α, Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α))) = ⊤)
    (A : Set J) (hA : A.Nonempty) (α : A) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (mk (circleSubwedgeGeneratorLoop S p f A hA α))) = ⊤ := by
  let φ := FundamentalGroup.mapOfEq
    ⟨circleToSubwedgeComponentHomeomorph S A α,
      (circleToSubwedgeComponentHomeomorph S A α).continuous⟩
    (circleToSubwedgeComponentHomeomorph_basepoint S p A hA α)
  have hφSurjective : Function.Surjective φ := by
    -- A homeomorphism induces a bijection on fundamental groups.
    exact (ContinuousMap.HomotopyEquiv.fundamentalGroupMapOfEq_bijective
      (circleToSubwedgeComponentHomeomorph S A α).toHomotopyEquiv
      (⟨p, IsWedgeOfCircles.mem_basepoint α.1⟩ : S α.1)
      (circleSubwedgeComponentPoint S p A hA α)
      (circleToSubwedgeComponentHomeomorph_basepoint S p A hA α)).2
  have hmap :
      (Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α.1)))).map φ = ⊤ := by
    -- Surjectivity transports the top cyclic subgroup to the top subgroup.
    rw [hf α.1]
    exact Subgroup.map_top_of_surjective φ hφSurjective
  -- Compute the image of the generator and use the transported path formula.
  rw [MonoidHom.map_zpowers,
    circleSubwedgeGeneratorLoop_fromPath S p f A hA α] at hmap
  exact hmap

/-- Helper for Theorem 71.3: endpoint-adjusted fundamental-group maps respect
composition independently of the chosen endpoint proofs. -/
private lemma fundamentalGroupMapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (a : C(X, Y)) (b : C(Y, Z))
    {x : X} {y : Y} {z : Z} (ha : a x = y) (hb : b y = z)
    (hba : (b.comp a) x = z) :
    (FundamentalGroup.mapOfEq b hb).comp (FundamentalGroup.mapOfEq a ha) =
      FundamentalGroup.mapOfEq (b.comp a) hba := by
  -- Normalize the intermediate points, then invoke functoriality of path mapping.
  subst y
  subst z
  have hbRefl : hb = rfl := Subsingleton.elim _ _
  cases hbRefl
  ext q
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl,
    Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Theorem 71.3: equal continuous maps induce the same
endpoint-adjusted fundamental-group homomorphism. -/
private lemma fundamentalGroupMapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (a b : C(X, Y)) {x : X} {y : Y} (hab : a = b)
    (ha : a x = y) (hb : b x = y) :
    FundamentalGroup.mapOfEq a ha = FundamentalGroup.mapOfEq b hb := by
  -- Substitute the map equality; proof irrelevance then identifies the endpoint witnesses.
  subst b
  have hproof : ha = hb := Subsingleton.elim _ _
  subst hb
  rfl

/-- Helper for Theorem 71.3: including a transported component generator into
the ambient wedge recovers the originally prescribed ambient loop class. -/
private lemma circleSubwedgeGeneratorLoop_inclusion
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (A : Set J) (hA : A.Nonempty) (α : A) :
    circleSubwedgeInclusionHom S p A hA
        (CircleWedge.includedLoopClass
          (circleSubwedgeComponent S A) (circleSubwedgePoint S p A hA) α
          (circleSubwedgeGeneratorLoop S p f A hA α)) =
      CircleWedge.includedLoopClass S p α.1 (f α.1) := by
  let e : C(S α.1, circleSubwedgeComponent S A α) :=
    ⟨circleToSubwedgeComponentHomeomorph S A α,
      (circleToSubwedgeComponentHomeomorph S A α).continuous⟩
  let j : C(circleSubwedgeComponent S A α, circleSubwedge S A) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let i : C(circleSubwedge S A, X) := circleSubwedgeInclusion S A
  let k : C(S α.1, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have he : e (⟨p, IsWedgeOfCircles.mem_basepoint α.1⟩ : S α.1) =
      circleSubwedgeComponentPoint S p A hA α :=
    circleToSubwedgeComponentHomeomorph_basepoint S p A hA α
  have hj : j (circleSubwedgeComponentPoint S p A hA α) =
      circleSubwedgePoint S p A hA := rfl
  have hi : i (circleSubwedgePoint S p A hA) = p :=
    circleSubwedgeInclusion_basepoint S p A hA
  have hje : (j.comp e)
      (⟨p, IsWedgeOfCircles.mem_basepoint α.1⟩ : S α.1) =
      circleSubwedgePoint S p A hA := by
    -- First transport to the selected component, then forget that component layer.
    exact (congrArg j he).trans hj
  have hije : (i.comp (j.comp e))
      (⟨p, IsWedgeOfCircles.mem_basepoint α.1⟩ : S α.1) = p := by
    -- The outer subwedge inclusion sends the selected point back to `p`.
    exact (congrArg i hje).trans hi
  have hcontinuousMaps : i.comp (j.comp e) = k := by
    -- The three nested inclusions and the component homeomorphism retain the
    -- same ambient coordinate.
    ext x
    rfl
  have hhom :
      ((FundamentalGroup.mapOfEq i hi).comp
          (FundamentalGroup.mapOfEq j hj)).comp
          (FundamentalGroup.mapOfEq e he) =
        FundamentalGroup.mapOfEq k rfl := by
    calc
      ((FundamentalGroup.mapOfEq i hi).comp
          (FundamentalGroup.mapOfEq j hj)).comp
          (FundamentalGroup.mapOfEq e he) =
          (FundamentalGroup.mapOfEq i hi).comp
            ((FundamentalGroup.mapOfEq j hj).comp
              (FundamentalGroup.mapOfEq e he)) := by
            rw [MonoidHom.comp_assoc]
      _ = (FundamentalGroup.mapOfEq i hi).comp
            (FundamentalGroup.mapOfEq (j.comp e) hje) := by
          rw [fundamentalGroupMapOfEq_comp e j he hj hje]
      _ = FundamentalGroup.mapOfEq (i.comp (j.comp e)) hije :=
        fundamentalGroupMapOfEq_comp (j.comp e) i hje hi hije
      _ = FundamentalGroup.mapOfEq k rfl :=
        fundamentalGroupMapOfEq_congr (i.comp (j.comp e)) k
          hcontinuousMaps hije rfl
  -- Replace the transported path class by the homeomorphism-induced image,
  -- then apply the composite-map identity to the original generator class.
  unfold circleSubwedgeInclusionHom CircleWedge.includedLoopClass
  rw [← circleSubwedgeGeneratorLoop_fromPath S p f A hA α]
  exact DFunLike.congr_fun hhom (FundamentalGroup.fromPath (mk (f α.1)))

/-- Helper for Theorem 71.3: evaluating a free-group word in the elements of a
free basis is a bijection. -/
private lemma freeGroupBasisLift_bijective
    {ι G : Type*} [Group G] (b : FreeGroupBasis ι G) :
    Function.Bijective (FreeGroup.lift fun i ↦ b i) := by
  -- Generator extensionality identifies evaluation with the inverse basis
  -- representation, whose underlying function is bijective.
  have hevaluation : FreeGroup.lift (fun i ↦ b i) = b.repr.symm.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of]
    rfl
  rw [hevaluation]
  exact b.repr.symm.bijective

/-- Helper for Theorem 71.3: on a finite nonempty subwedge, choose component
generator classes whose free evaluation is bijective and whose inclusions are
the prescribed ambient generator classes. -/
private lemma finiteCircleSubwedgeGeneratorLift_bijective
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (hf : ∀ α, Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α))) = ⊤)
    (F : Finset J) (hF : (F : Set J).Nonempty) :
    ∃ g : F → FundamentalGroup (circleSubwedge S (F : Set J))
        (circleSubwedgePoint S p (F : Set J) hF),
      Function.Bijective (FreeGroup.lift g) ∧
        ∀ α, circleSubwedgeInclusionHom S p (F : Set J) hF (g α) =
            CircleWedge.includedLoopClass S p α.1 (f α.1) := by
  -- Reindex the finite subwedge by `Fin` so that Theorem 71.1 applies directly.
  have hFFinset : F.Nonempty := finsetNonempty_of_coe_nonempty hF
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let T : Fin (Fintype.card F) → Set (circleSubwedge S (F : Set J)) :=
    fun i ↦ circleSubwedgeComponent S (F : Set J) (e i)
  let pF := circleSubwedgePoint S p (F : Set J) hF
  letI : IsFiniteWedgeOfCircles T pF :=
    finiteCircleWedge_reindex
      (circleSubwedgeComponent S (F : Set J)) pF e
      (finiteCircleSubwedge_isFiniteWedge S p F hFFinset)
  let fFin : ∀ i, Path
      (⟨pF, IsFiniteWedgeOfCircles.mem_basepoint i⟩ : T i)
      ⟨pF, IsFiniteWedgeOfCircles.mem_basepoint i⟩ :=
    fun i ↦ circleSubwedgeGeneratorLoop S p f (F : Set J) hF (e i)
  have hfFin : ∀ i, Subgroup.zpowers
      (FundamentalGroup.fromPath (mk (fFin i))) = ⊤ := by
    intro i
    -- The canonical component homeomorphism preserves the chosen cyclic generator.
    exact circleSubwedgeGeneratorLoop_zpowers S p f hf (F : Set J) hF (e i)
  -- Route correction: the restored direct dependency now supplies the finite
  -- basis, avoiding a duplicate reconstruction of Theorem 71.1 in this file.
  obtain ⟨b, hb⟩ :=
    fundamentalGroup_freeBasis_of_finiteCircleWedge T pF fFin hfFin
  let bF : FreeGroupBasis F
      (FundamentalGroup (circleSubwedge S (F : Set J)) pF) := b.reindex e
  refine ⟨fun α ↦ bF α, freeGroupBasisLift_bijective bF, ?_⟩
  intro α
  -- Reindex the finite basis and use the verified inclusion compatibility of
  -- the transported component loop.
  simp only [bF, FreeGroupBasis.reindex_apply, hb]
  have hreindex :
      CircleWedge.includedLoopClass T pF (e.symm α) (fFin (e.symm α)) =
        CircleWedge.includedLoopClass (circleSubwedgeComponent S (F : Set J))
          pF α (circleSubwedgeGeneratorLoop S p f (F : Set J) hF α) := by
    -- Represent the selected component through `e`; inverse cancellation then
    -- happens before the dependent component loop is unfolded.
    obtain ⟨i, rfl⟩ := e.surjective α
    rw [e.symm_apply_apply]
    unfold T fFin CircleWedge.includedLoopClass
    apply DFunLike.congr_fun
    exact fundamentalGroupMapOfEq_congr _ _ rfl _ _
  rw [hreindex]
  exact circleSubwedgeGeneratorLoop_inclusion S p f (F : Set J) hF α

/-- Helper for Theorem 71.3: equality on the finite subwedge generators extends
to the commutative square between the two free-group evaluation maps. -/
private lemma circleSubwedgeGeneratorLift_naturality
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (F : Finset J) (hF : (F : Set J).Nonempty)
    (g : F → FundamentalGroup (circleSubwedge S (F : Set J))
      (circleSubwedgePoint S p (F : Set J) hF))
    (hg : ∀ α, circleSubwedgeInclusionHom S p (F : Set J) hF (g α) =
        CircleWedge.includedLoopClass S p α.1 (f α.1)) :
    (circleSubwedgeInclusionHom S p (F : Set J) hF).comp
        (FreeGroup.lift g) =
      (FreeGroup.lift
        (fun α ↦ CircleWedge.includedLoopClass S p α (f α))).comp
        (FreeGroup.map Subtype.val) := by
  -- Free-group homomorphisms agree once they agree on every free generator.
  apply FreeGroup.ext_hom
  intro α
  calc
    _ = circleSubwedgeInclusionHom S p (F : Set J) hF (g α) := by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    _ = CircleWedge.includedLoopClass S p α.1 (f α.1) := hg α
    _ = _ := by
      rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]

/-- Helper for Theorem 71.3: the ambient classes of chosen component generators
define a bijective evaluation map from the free group on the circle indices. -/
private lemma circleWedgeGeneratorLift_bijective
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (hf : ∀ α, Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α))) = ⊤) :
    Function.Bijective
      (FreeGroup.lift (fun α ↦ CircleWedge.includedLoopClass S p α (f α))) := by
  -- Route correction: the ambient-to-finite comparison is now organized through
  -- the verified continuous subwedge retraction above, rather than by transporting
  -- nullhomotopies directly through nested subtype paths.
  let ambientLift :=
    FreeGroup.lift (fun α ↦ CircleWedge.includedLoopClass S p α (f α))
  constructor
  · intro w₁ w₂ hw
    obtain ⟨F, wF, hwF⟩ :=
      FreeGroup.exists_finset_factorization (w₁ * w₂⁻¹)
    by_cases hF : F.Nonempty
    · obtain ⟨g, hgBijective, hg⟩ :=
        finiteCircleSubwedgeGeneratorLift_bijective S p f hf F
          (finsetCoe_nonempty hF)
      have hnaturality :=
        circleSubwedgeGeneratorLift_naturality S p f F (finsetCoe_nonempty hF) g hg
      have hambientWord : ambientLift (FreeGroup.map Subtype.val wF) = 1 := by
        rw [hwF]
        unfold ambientLift
        rw [map_mul, map_inv, hw, mul_inv_cancel]
      have hinclusionWord :
          circleSubwedgeInclusionHom S p (F : Set J) (finsetCoe_nonempty hF)
              (FreeGroup.lift g wF) = 1 := by
        calc
          _ = ambientLift (FreeGroup.map Subtype.val wF) :=
            DFunLike.congr_fun hnaturality wF
          _ = 1 := hambientWord
      have hinclusion : Function.Injective
          (circleSubwedgeInclusionHom S p (F : Set J) (finsetCoe_nonempty hF)) :=
        circleSubwedgeInclusionHom_injective S p (F : Set J)
          (finsetCoe_nonempty hF)
      have hfiniteWord : FreeGroup.lift g wF = 1 := by
        apply hinclusion
        simpa only [map_one] using hinclusionWord
      have hwFOne : wF = 1 := by
        apply hgBijective.1
        simpa only [map_one] using hfiniteWord
      have hquotient : w₁ * w₂⁻¹ = 1 := by
        calc
          w₁ * w₂⁻¹ = FreeGroup.map Subtype.val wF := hwF.symm
          _ = FreeGroup.map Subtype.val 1 := congrArg _ hwFOne
          _ = 1 := map_one _
      have hcancel := congrArg (fun z ↦ z * w₂) hquotient
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hcancel
    · letI : IsEmpty F := ⟨fun α ↦ hF ⟨α.1, α.2⟩⟩
      have hwFOne : wF = 1 := Subsingleton.elim wF 1
      have hquotient : w₁ * w₂⁻¹ = 1 := by
        calc
          w₁ * w₂⁻¹ = FreeGroup.map Subtype.val wF := hwF.symm
          _ = FreeGroup.map Subtype.val 1 := congrArg _ hwFOne
          _ = 1 := map_one _
      have hcancel := congrArg (fun z ↦ z * w₂) hquotient
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hcancel
  · intro y
    obtain ⟨q, rfl⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath y)
    obtain ⟨F, hqF⟩ :=
      IsWedgeOfCircles.isCompact_subset_iUnion_finset
        (inferInstance : IsWedgeOfCircles S p) (isCompact_range q.continuous)
    have hqSubwedge : Set.range q ⊆ circleSubwedge S (F : Set J) := by
      intro x hx
      obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (hqF hx)
      obtain ⟨hαF, hxS⟩ := Set.mem_iUnion.mp hα
      exact Set.mem_iUnion.mpr ⟨⟨α, hαF⟩, hxS⟩
    have hF : (F : Set J).Nonempty := by
      have hpSubwedge := hqSubwedge (Path.source_mem_range q)
      obtain ⟨α, _⟩ := Set.mem_iUnion.mp hpSubwedge
      exact ⟨α.1, α.2⟩
    obtain ⟨z, hz⟩ :=
      loopClass_mem_circleSubwedgeInclusionRange S p (F : Set J) hF q hqSubwedge
    obtain ⟨g, hgBijective, hg⟩ :=
      finiteCircleSubwedgeGeneratorLift_bijective S p f hf F hF
    obtain ⟨wF, hwF⟩ := hgBijective.2 z
    refine ⟨FreeGroup.map Subtype.val wF, ?_⟩
    have hnaturality :=
      circleSubwedgeGeneratorLift_naturality S p f F hF g hg
    calc
      ambientLift (FreeGroup.map Subtype.val wF) =
          circleSubwedgeInclusionHom S p (F : Set J) hF
            (FreeGroup.lift g wF) :=
        (DFunLike.congr_fun hnaturality wF).symm
      _ = circleSubwedgeInclusionHom S p (F : Set J) hF z :=
        congrArg _ hwF
      _ = FundamentalGroup.fromPath (mk q) := hz

/-- Helper for Theorem 71.3: the fundamental group of an arbitrarily indexed
coherent wedge of circles is a free group. -/
instance fundamentalGroup_isFree_of_circleWedge
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p] :
    IsFreeGroup (FundamentalGroup X p) := by
  -- Choose generators in the component circles and transport the resulting free basis.
  obtain ⟨f, hf⟩ := existsCircleWedgeGeneratorLoops S p
  have hbijective := circleWedgeGeneratorLift_bijective S p f hf
  let equivalence : FreeGroup J ≃* FundamentalGroup X p :=
    MulEquiv.ofBijective
      (FreeGroup.lift (fun α ↦ CircleWedge.includedLoopClass S p α (f α)))
      hbijective
  let basis : FreeGroupBasis J (FundamentalGroup X p) :=
    FreeGroupBasis.ofRepr equivalence.symm
  exact basis.isFreeGroup

/-- Theorem 71.3 (2): chosen generator loops in the component circles map to a
free basis of the ambient fundamental group. -/
theorem fundamentalGroup_freeBasis_of_circleWedge
    {J : Type v} {X : Type u} [TopologicalSpace X]
    (S : J → Set X) (p : X) [IsWedgeOfCircles S p]
    (f : ∀ α, Path
      (⟨p, IsWedgeOfCircles.mem_basepoint α⟩ : S α)
      ⟨p, IsWedgeOfCircles.mem_basepoint α⟩)
    (hf : ∀ α, Subgroup.zpowers (FundamentalGroup.fromPath (mk (f α))) = ⊤) :
    ∃ b : FreeGroupBasis J (FundamentalGroup X p),
      ∀ α, b α = CircleWedge.includedLoopClass S p α (f α) := by
  -- Turn bijectivity of the canonical evaluation map into the requested basis.
  have hbijective := circleWedgeGeneratorLift_bijective S p f hf
  let equivalence : FreeGroup J ≃* FundamentalGroup X p :=
    MulEquiv.ofBijective
      (FreeGroup.lift (fun α ↦ CircleWedge.includedLoopClass S p α (f α)))
      hbijective
  let basis : FreeGroupBasis J (FundamentalGroup X p) :=
    FreeGroupBasis.ofRepr equivalence.symm
  refine ⟨basis, ?_⟩
  intro α
  -- Evaluation on a free generator is exactly its chosen ambient loop class.
  exact @FreeGroup.lift_apply_of J (FundamentalGroup X p) _
    (fun i ↦ CircleWedge.includedLoopClass S p i (f i)) α
