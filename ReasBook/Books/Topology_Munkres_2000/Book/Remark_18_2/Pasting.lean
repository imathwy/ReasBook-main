module

public import Mathlib.Topology.ContinuousMap.Basic

public section

open scoped Topology

universe u v

namespace ContinuousMap

private def twoOpenCover {X : Type u} (A B : Set X) : Bool → Set X :=
  fun i ↦ if i then A else B

private def twoOpenMaps
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (f : ContinuousMap A Y) (g : ContinuousMap B Y) :
    ∀ i, ContinuousMap (twoOpenCover A B i) Y :=
  fun i ↦ Bool.casesOn i g f

private theorem twoOpenMaps_compatible
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    ∀ (i j) (x : X) (hxi : x ∈ twoOpenCover A B i) (hxj : x ∈ twoOpenCover A B j),
      twoOpenMaps f g i ⟨x, hxi⟩ = twoOpenMaps f g j ⟨x, hxj⟩ := by
  intro i j x hxi hxj
  cases i <;> cases j
  · rfl
  · exact (hfg ⟨x, hxj, hxi⟩).symm
  · exact hfg ⟨x, hxi, hxj⟩
  · rfl

private theorem twoOpenCover_nhds
    {X : Type u} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    ∀ x : X, ∃ i, twoOpenCover A B i ∈ 𝓝 x := by
  intro x
  have hx : x ∈ A ∨ x ∈ B := by
    rw [← Set.mem_union, hcover]
    exact Set.mem_univ x
  obtain hxA | hxB := hx
  · exact ⟨true, hA.mem_nhds hxA⟩
  · exact ⟨false, hB.mem_nhds hxB⟩

/-- Glue continuous maps on two open sets that cover the domain and agree on their
intersection, as a two-set specialization of `ContinuousMap.liftCover`. -/
noncomputable def pasteOpen
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    ContinuousMap X Y :=
  liftCover (twoOpenCover A B) (twoOpenMaps f g) (twoOpenMaps_compatible f g hfg)
    (twoOpenCover_nhds hA hB hcover)

/-- Restricting `pasteOpen` to the left open set recovers the left map. -/
@[simp]
theorem pasteOpen_restrict_left
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    (pasteOpen hA hB hcover f g hfg).restrict A = f := by
  change
    (liftCover (twoOpenCover A B) (twoOpenMaps f g) (twoOpenMaps_compatible f g hfg)
      (twoOpenCover_nhds hA hB hcover)).restrict (twoOpenCover A B true) =
        twoOpenMaps f g true
  exact liftCover_restrict

/-- Restricting `pasteOpen` to the right open set recovers the right map. -/
@[simp]
theorem pasteOpen_restrict_right
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (f : ContinuousMap A Y) (g : ContinuousMap B Y)
    (hfg : ∀ x : (A ∩ B : Set X), f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩) :
    (pasteOpen hA hB hcover f g hfg).restrict B = g := by
  change
    (liftCover (twoOpenCover A B) (twoOpenMaps f g) (twoOpenMaps_compatible f g hfg)
      (twoOpenCover_nhds hA hB hcover)).restrict (twoOpenCover A B false) =
        twoOpenMaps f g false
  exact liftCover_restrict

end ContinuousMap
