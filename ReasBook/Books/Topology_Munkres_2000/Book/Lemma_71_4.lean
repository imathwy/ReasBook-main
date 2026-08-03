module

public import Topology_Munkres_2000.Book.Lemma_71_4.Wedge
public import Mathlib.Topology.Category.TopCat.Basic

public section

universe u

namespace Topology.Lemma714Wedge

variable {I : Type u} (X : I → Type u) (p : ∀ i, X i)

/-- Helper for Lemma 71.4: the normalized relation identifies all designated points. -/
def designatedRel (x y : Σ i, X i) : Prop :=
  x = y ∨ (x.2 = p x.1 ∧ y.2 = p y.1)

/-- Helper for Lemma 71.4: the normalized designated-point relation is reflexive. -/
lemma designatedRel_refl (x : Σ i, X i) : designatedRel X p x x := by
  -- Reflexivity uses the equality alternative.
  exact Or.inl rfl

/-- Helper for Lemma 71.4: the normalized designated-point relation is symmetric. -/
lemma designatedRel_symm {x y : Σ i, X i} :
    designatedRel X p x y → designatedRel X p y x := by
  -- Swap equality or the two designated-point equations.
  intro h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr ⟨h.2, h.1⟩

/-- Helper for Lemma 71.4: the normalized designated-point relation is transitive. -/
lemma designatedRel_trans {x y z : Σ i, X i} :
    designatedRel X p x y → designatedRel X p y z →
      designatedRel X p x z := by
  -- Equality transports the other relation; otherwise both endpoints stay designated.
  intro hxy hyz
  rcases hxy with hxy | hxy
  · subst y
    exact hyz
  · rcases hyz with hyz | hyz
    · subst z
      exact Or.inr hxy
    · exact Or.inr ⟨hxy.1, hyz.2⟩

/-- Helper for Lemma 71.4: the setoid collapsing all designated points. -/
def designatedSetoid : Setoid (Σ i, X i) :=
  ⟨designatedRel X p, designatedRel_refl X p, designatedRel_symm X p,
    designatedRel_trans X p⟩

/-- Helper for Lemma 71.4: the transparent quotient model of an indexed pointed wedge. -/
abbrev Space := Quotient (designatedSetoid X p)

/-- Helper for Lemma 71.4: the quotient map of the transparent pointed-wedge model. -/
def quotientMap : (Σ i, X i) → Space X p :=
  Quotient.mk (designatedSetoid X p)

/-- Helper for Lemma 71.4: the inclusion of one factor in the transparent quotient model. -/
def inclusion (i : I) : X i → Space X p :=
  fun x ↦ quotientMap X p ⟨i, x⟩

/-- Helper for Lemma 71.4: the common quotient point represented in one factor. -/
def point (i : I) : Space X p :=
  inclusion X p i (p i)

/-- Helper for Lemma 71.4: each factor inclusion is injective. -/
lemma inclusion_injective (i : I) : Function.Injective (inclusion X p i) := by
  -- Quotient equality inside one factor reduces to equality or two copies of the same basepoint.
  intro x y hxy
  have hrel := Quotient.exact hxy
  rcases hrel with h | h
  · exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  · exact h.1.trans h.2.symm

/-- Helper for Lemma 71.4: every quotient point lies in a factor image. -/
lemma iUnion_range_inclusion : ⋃ i, Set.range (inclusion X p i) = Set.univ := by
  -- Choose a sigma representative of the quotient class.
  ext q
  constructor
  · intro _
    exact Set.mem_univ q
  · intro _
    induction q using Quotient.inductionOn with
    | _ x => exact Set.mem_iUnion.mpr ⟨x.1, x.2, rfl⟩

/-- Helper for Lemma 71.4: all factor representatives of the designated point agree. -/
lemma point_eq (i k : I) : point X p i = point X p k := by
  -- Both representatives satisfy the designated-point alternative of the setoid.
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl⟩

/-- Helper for Lemma 71.4: distinct factor images intersect at the common point. -/
lemma range_inclusion_inter (i k : I) (hik : i ≠ k) :
    Set.range (inclusion X p i) ∩ Set.range (inclusion X p k) = {point X p i} := by
  -- Analyze quotient equality between representatives from two distinct factors.
  ext q
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
    rcases Quotient.exact hxy with h | h
    · exact (hik (Sigma.mk.inj_iff.mp h.symm).1).elim
    · rw [Set.mem_singleton_iff, point]
      exact congrArg (inclusion X p i) h.2
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨⟨p i, rfl⟩, ⟨p k, point_eq X p k i⟩⟩

variable [∀ i, TopologicalSpace (X i)]

/-- Helper for Lemma 71.4: the designated points form a closed subset of the sigma
coproduct when every factor is a `T1Space`. -/
lemma isClosed_range_designated [∀ i, T1Space (X i)] :
    IsClosed (Set.range fun i ↦ (⟨i, p i⟩ : Σ i, X i)) := by
  -- On each sigma component the designated range restricts to one closed singleton.
  rw [isClosed_sigma_iff]
  intro i
  have hrange :
      Sigma.mk i ⁻¹' Set.range (fun k ↦ (⟨k, p k⟩ : Σ k, X k)) = {p i} := by
    ext x
    constructor
    · rintro ⟨k, hk⟩
      have hik : k = i := (Sigma.mk.inj_iff.mp hk).1
      subst k
      rw [Set.mem_singleton_iff]
      exact eq_of_heq (Sigma.mk.inj_iff.mp hk).2.symm
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨i, congrArg (Sigma.mk i) hx.symm⟩
  rw [hrange]
  exact isClosed_singleton

omit [∀ i, TopologicalSpace (X i)] in
/-- Helper for Lemma 71.4: being a designated sigma point is membership in the
range of the designated-point section. -/
lemma setOf_designated_eq_range :
    {x : Σ i, X i | x.2 = p x.1} = Set.range (fun i ↦ (⟨i, p i⟩ : Σ i, X i)) := by
  -- A point satisfying the fiber equation is represented by its own index.
  ext x
  constructor
  · intro hx
    exact ⟨x.1, Sigma.ext rfl (heq_of_eq hx.symm)⟩
  · rintro ⟨i, rfl⟩
    exact rfl

omit [∀ i, TopologicalSpace (X i)] in
/-- Helper for Lemma 71.4: the saturation of a closed subset of one factor is its
sigma image, together with every designated point exactly when it contains its own. -/
lemma preimage_image_inclusion (i : I) (C : Set (X i)) :
    quotientMap X p ⁻¹' (inclusion X p i '' C) =
      Sigma.mk i '' C ∪ {x | p i ∈ C ∧ x.2 = p x.1} := by
  -- Quotient equality is already in the normalized equality-or-designated form.
  ext x
  constructor
  · rintro ⟨c, hc, hqc⟩
    rcases Quotient.exact hqc with h | h
    · exact Or.inl ⟨c, hc, h⟩
    · have hp : p i ∈ C := by
        rwa [← h.1]
      exact Or.inr ⟨hp, h.2⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · refine ⟨p i, hx.1, ?_⟩
      apply Quotient.sound
      exact Or.inr ⟨rfl, hx.2⟩

/-- Helper for Lemma 71.4: each factor inclusion is a closed topological embedding. -/
lemma isClosedEmbedding_inclusion [∀ i, T1Space (X i)] (i : I) :
    IsClosedEmbedding (inclusion X p i) := by
  -- Continuity and injectivity are direct; closedness follows from the saturation formula.
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_quotient_mk'.comp continuous_sigmaMk
  · exact inclusion_injective X p i
  · intro C hC
    rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
    change IsClosed (quotientMap X p ⁻¹' (inclusion X p i '' C))
    rw [preimage_image_inclusion X p i C]
    apply IsClosed.union
    · exact IsClosedEmbedding.sigmaMk.isClosedMap C hC
    · by_cases hp : p i ∈ C
      · have heq : {x : Σ i, X i | p i ∈ C ∧ x.2 = p x.1} =
            Set.range (fun k ↦ (⟨k, p k⟩ : Σ k, X k)) := by
          rw [← setOf_designated_eq_range X p]
          ext x
          simp only [Set.mem_setOf_eq, hp, true_and]
        rw [heq]
        exact isClosed_range_designated X p
      · have heq : {x : Σ i, X i | p i ∈ C ∧ x.2 = p x.1} = ∅ := by
          ext x
          constructor
          · intro hx
            exact (hp hx.1).elim
          · intro hx
            exact hx.elim
        rw [heq]
        exact isClosed_empty

/-- Helper for Lemma 71.4: the quotient topology is coherent with the factor images. -/
lemma isCoherentWith_range_inclusion [∀ i, T1Space (X i)] :
    IsCoherentWith (Set.range fun i ↦ Set.range (inclusion X p i)) := by
  -- Pull closedness from every image to every sigma component, then use the quotient topology.
  apply IsCoherentWith.of_isClosed
  intro D hD
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage, isClosed_sigma_iff]
  intro i
  have himage : Set.range (inclusion X p i) ∈
      Set.range (fun i ↦ Set.range (inclusion X p i)) := ⟨i, rfl⟩
  have hrestricted := hD (Set.range (inclusion X p i)) himage
  have hemb := isClosedEmbedding_inclusion X p i
  have hpreimage : IsClosed (inclusion X p i ⁻¹' D) := by
    simpa only [IsEmbedding.toHomeomorph_apply_coe, Set.preimage_preimage,
      Function.comp_def] using
      hemb.isEmbedding.toHomeomorph.isClosed_preimage.mpr hrestricted
  change IsClosed (inclusion X p i ⁻¹' D)
  exact hpreimage

end Topology.Lemma714Wedge

/-- Lemma 71.4: For every nonempty index type, there is a space that is a wedge of
circles indexed by that type. -/
theorem Topology.IsWedgeOfCircles.exists (J : Type u) [Nonempty J] :
    ∃ (X : TopCat.{u}) (S : J → Set X) (p : X), IsWedgeOfCircles S p := by
  -- Use the transparent quotient model so every wedge axiom follows from the local interface.
  let ⟨j⟩ := ‹Nonempty J›
  let family : J → Type u := fun _ ↦ ULift.{u} Circle
  let base : ∀ k, family k := fun _ ↦ ULift.up CircleWedge.basepoint
  let space := Lemma714Wedge.Space family base
  let circles : J → Set space := fun k ↦ Set.range (Lemma714Wedge.inclusion family base k)
  let wedgePoint : space := Lemma714Wedge.point family base j
  refine ⟨TopCat.of space, circles, wedgePoint, ?_⟩
  apply IsWedgeOfCircles.of
  · -- The factor images cover the quotient.
    exact Lemma714Wedge.iUnion_range_inclusion family base
  · -- Each closed factor inclusion identifies its range homeomorphically with `Circle`.
    intro k
    have hemb := Lemma714Wedge.isClosedEmbedding_inclusion family base k
    exact ⟨hemb.isEmbedding.toHomeomorph.symm.trans Homeomorph.ulift⟩
  · -- Distinct factor ranges intersect at the chosen common quotient point.
    intro k l hkl
    have hinter := Lemma714Wedge.range_inclusion_inter family base k l hkl
    have hpoint : Lemma714Wedge.point family base k = wedgePoint := by
      exact Lemma714Wedge.point_eq family base k j
    rwa [hpoint] at hinter
  · -- Closedness on every factor range is exactly closedness in the quotient topology.
    exact Lemma714Wedge.isCoherentWith_range_inclusion family base
