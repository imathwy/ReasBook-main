module

public import Topology_Munkres_2000.Book.Example_30_4
public import Topology_Munkres_2000.Book.Exercise_37_3.Maximal
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Topology.Constructions
import Topology_Munkres_2000.Book.Exercise_37_2

public section

open Set

universe u v

namespace Set.CountableIntersectionProperty

/-- Helper for Exercise 37.3: pointwise images of a family preserve the countable
intersection property. -/
theorem imageFamily {X : Type u} {Y : Type v} {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.CountableIntersectionProperty) (f : X → Y) :
    ((fun A ↦ f '' A) '' 𝒜).CountableIntersectionProperty := by
  classical
  have hRange :
      (Set.range (fun A : 𝒜 ↦ f '' (A : Set X))).CountableIntersectionProperty := by
    refine (Set.CountableIntersectionProperty.range_iff _).mpr ?_
    intro s hs
    letI : Countable s := hs.to_subtype
    -- Apply the original property to the selected source sets.
    obtain ⟨x, hx⟩ := h𝒜.iInter_nonempty
      (fun A : s ↦ (A.1 : Set X)) (fun A ↦ A.1.property)
    refine ⟨f x, Set.mem_iInter₂.mpr ?_⟩
    intro A hA
    -- The common source point maps into each selected image.
    exact ⟨x, Set.mem_iInter.mp hx ⟨A, hA⟩, rfl⟩
  simpa only [Set.image_eq_range] using hRange

end Set.CountableIntersectionProperty

/-- Helper for Exercise 37.3: a coordinate neighborhood pulls back to a member of a
maximal family when the coordinate lies in every projected closure. -/
private theorem IsMaximalCountableIntersection.preimage_mem_of_mem_iInter_closure_image
    {X : Type u} {Y : Type v} [TopologicalSpace Y] {𝒟 : Set (Set X)}
    (h𝒟 : IsMaximalCountableIntersection 𝒟) {f : X → Y} {y : Y}
    (hy : y ∈ ⋂ B ∈ 𝒟, closure (f '' B)) {U : Set Y} (hU : IsOpen U) (hyU : y ∈ U) :
    f ⁻¹' U ∈ 𝒟 := by
  refine h𝒟.mem_of_intersects_all ?_
  intro B hB
  -- Closure membership supplies a point of the image in the chosen neighborhood.
  obtain ⟨z, hzU, hzImage⟩ :=
    mem_closure_iff.mp (Set.mem_iInter₂.mp hy B hB) U hU hyU
  obtain ⟨x, hxB, rfl⟩ := hzImage
  exact ⟨x, hzU, hxB⟩

/-- Helper for Exercise 37.3: coordinatewise membership in all projected closures gives
membership in all closures of the original maximal family in a product. -/
private theorem IsMaximalCountableIntersection.mem_iInter_closure_of_eval_images
    {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
    {𝒟 : Set (Set (∀ i, X i))} (h𝒟 : IsMaximalCountableIntersection 𝒟)
    {x : ∀ i, X i}
    (hx : ∀ i, x i ∈ ⋂ B ∈ 𝒟, closure ((fun y ↦ y i) '' B)) :
    x ∈ ⋂ B ∈ 𝒟, closure B := by
  refine Set.mem_iInter₂.mpr ?_
  intro D hD
  rw [mem_closure_iff]
  intro U hU hxU
  -- Refine the product neighborhood to a finite coordinate box around `x`.
  obtain ⟨I, V, hIV, hBoxSubset⟩ := isOpen_pi_iff.mp hU x hxU
  have hCylindersSubset :
      ((fun i ↦ (fun y : ∀ i, X i ↦ y i) ⁻¹' V i) '' (I : Set ι)) ⊆ 𝒟 := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := hC
    exact h𝒟.preimage_mem_of_mem_iInter_closure_image
      (hx i) (hIV i hi).1 (hIV i hi).2
  have hCylindersCountable :
      ((fun i ↦ (fun y : ∀ i, X i ↦ y i) ⁻¹' V i) '' (I : Set ι)).Countable :=
    I.finite_toSet.image _ |>.countable
  have hBoxEq :
      ⋂₀ ((fun i ↦ (fun y : ∀ i, X i ↦ y i) ⁻¹' V i) '' (I : Set ι)) =
        (I : Set ι).pi V := by
    rw [Set.sInter_image, Set.pi_def]
  have hBoxMem : (I : Set ι).pi V ∈ 𝒟 := by
    rw [← hBoxEq]
    exact h𝒟.countable_sInter_mem hCylindersSubset hCylindersCountable
  -- The countable intersection property makes the box meet `D`.
  let pair : Fin 2 → Set (∀ i, X i) :=
    fun j ↦ Fin.cases ((I : Set ι).pi V) (fun _ ↦ D) j
  have hPairMem : ∀ j, pair j ∈ 𝒟 := by
    intro j
    refine Fin.cases hBoxMem ?_ j
    intro _
    exact hD
  obtain ⟨z, hz⟩ := h𝒟.countableIntersectionProperty.iInter_nonempty pair hPairMem
  have hzBox : z ∈ (I : Set ι).pi V := by
    simpa only [pair, Fin.cases_zero] using Set.mem_iInter.mp hz (0 : Fin 2)
  have hzD : z ∈ D := by
    simpa only [pair, Fin.cases_succ] using
      Set.mem_iInter.mp hz (Fin.succ (0 : Fin 1))
  exact ⟨z, hBoxSubset hzBox, hzD⟩

/- Exercise 37.3 (2): a countable intersection of members of a maximal family with the
countable intersection property is again a member of the family. -/
#check IsMaximalCountableIntersection.countable_sInter_mem

/- Exercise 37.3 (3): a set intersecting every member of a maximal family with the
countable intersection property belongs to that family. -/
#check IsMaximalCountableIntersection.mem_of_intersects_all

/-- Exercise 37.3 (1): the maximal-extension principle, together with the two properties
of maximal countable-intersection families, implies that arbitrary products of Lindelöf
spaces are Lindelöf. -/
theorem maximalCountableIntersection_implies_lindelofPi
    (exists_maximal : ∀ {Y : Type u} {𝒜 : Set (Set Y)},
      𝒜.CountableIntersectionProperty →
        ∃ 𝒟 : Set (Set Y), 𝒜 ⊆ 𝒟 ∧ IsMaximalCountableIntersection 𝒟)
    (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, LindelofSpace (X i)] :
    LindelofSpace (∀ i, X i) := by
  classical
  refine LindelofSpace.of_iInter_closure_nonempty ?_
  intro 𝒜 h𝒜
  -- Extend the family and apply the Lindelöf closure criterion in each coordinate.
  obtain ⟨𝒟, h𝒜𝒟, h𝒟⟩ := exists_maximal h𝒜
  have hCoordinateNonempty (i : ι) :
      (⋂ B ∈ 𝒟, closure ((fun y : ∀ i, X i ↦ y i) '' B)).Nonempty :=
    by
      simpa only [Set.biInter_image] using
        LindelofSpace.iInter_closure_nonempty
          ((fun B ↦ (fun y : ∀ i, X i ↦ y i) '' B) '' 𝒟)
          (h𝒟.countableIntersectionProperty.imageFamily (fun y : ∀ i, X i ↦ y i))
  choose x hx using hCoordinateNonempty
  have hx𝒟 : x ∈ ⋂ B ∈ 𝒟, closure B :=
    h𝒟.mem_iInter_closure_of_eval_images hx
  -- Restrict the common closure point from the maximal extension to the original family.
  refine ⟨x, Set.mem_iInter₂.mpr ?_⟩
  intro A hA
  exact Set.mem_iInter₂.mp hx𝒟 A (h𝒜𝒟 hA)

/- Exercise 37.3 (4): the Sorgenfrey plane is a product of Lindelöf spaces that is not
Lindelöf. -/
#check (inferInstance : NonLindelofSpace (SorgenfreyLine × SorgenfreyLine))

/-- Exercise 37.3 (5): not every family with the countable intersection property extends
to a maximal family with that property. -/
theorem not_all_countableIntersection_extend_maximal :
    ¬(∀ (X : Type u) (𝒜 : Set (Set X)), 𝒜.CountableIntersectionProperty →
      ∃ 𝒟 : Set (Set X), 𝒜 ⊆ 𝒟 ∧ IsMaximalCountableIntersection 𝒟) := by
  intro hExtension
  -- Lift both the two-point index and the factors into the fixed universe `u`.
  letI : LindelofSpace (ULift.{u} SorgenfreyLine) :=
    LindelofSpace.of_continuous_surjective continuous_uliftUp ULift.up_surjective
  letI : LindelofSpace (ULift.{u} (Fin 2) → ULift.{u} SorgenfreyLine) :=
    maximalCountableIntersection_implies_lindelofPi
      (fun {Y} {𝒜} h𝒜 ↦ hExtension Y 𝒜 h𝒜)
      (ULift.{u} (Fin 2)) (fun _ ↦ ULift.{u} SorgenfreyLine)
  -- Evaluating at the two lifted coordinates and lowering values maps onto the plane.
  have hContinuous : Continuous
      (fun f : ULift.{u} (Fin 2) → ULift.{u} SorgenfreyLine ↦
        ((f ⟨0⟩).down, (f ⟨1⟩).down)) :=
    (continuous_uliftDown.comp
      (continuous_apply (⟨(0 : Fin 2)⟩ : ULift.{u} (Fin 2)))).prodMk
      (continuous_uliftDown.comp
        (continuous_apply (⟨(1 : Fin 2)⟩ : ULift.{u} (Fin 2))))
  have hSurjective : Function.Surjective
      (fun f : ULift.{u} (Fin 2) → ULift.{u} SorgenfreyLine ↦
        ((f ⟨0⟩).down, (f ⟨1⟩).down)) := by
    intro p
    refine ⟨fun i ↦ ULift.up (Fin.cases p.1 (fun _ ↦ p.2) i.down), ?_⟩
    rfl
  have hPlane : LindelofSpace (SorgenfreyLine × SorgenfreyLine) :=
    LindelofSpace.of_continuous_surjective hContinuous hSurjective
  exact SorgenfreyPlane.notLindelof hPlane

/-- Helper for Exercise 37.3: the bounded family of natural-number tails through stage `n`. -/
private def boundedNatTailFamily (n : ℕ) : Set (Set ℕ) :=
  (fun k : ℕ ↦ Set.Ici k) '' Set.Iic n

/-- Helper for Exercise 37.3: every bounded family of natural-number tails has the
countable intersection property. -/
private theorem boundedNatTailFamilyCountableIntersectionProperty (n : ℕ) :
    (boundedNatTailFamily n).CountableIntersectionProperty := by
  have hRange :
      (Set.range (fun k : Set.Iic n ↦ Set.Ici (k : ℕ))).CountableIntersectionProperty := by
    refine (Set.CountableIntersectionProperty.range_iff _).mpr ?_
    intro s _
    -- The endpoint `n` belongs to every selected bounded tail.
    refine ⟨n, Set.mem_iInter₂.mpr ?_⟩
    intro k _
    exact Set.mem_Ici.mpr (Set.mem_Iic.mp k.property)
  simpa only [boundedNatTailFamily, Set.image_eq_range] using hRange

/-- Exercise 37.3 (6): the countable intersection property is not preserved by taking the
union of a chain of families, which obstructs the corresponding Zorn argument. -/
theorem countableIntersection_not_closed_under_chain_sUnion :
    ∃ 𝒞 : Set (Set (Set ℕ)), IsChain (· ⊆ ·) 𝒞 ∧
      (∀ 𝒜 ∈ 𝒞, 𝒜.CountableIntersectionProperty) ∧
      ¬(⋃₀ 𝒞).CountableIntersectionProperty := by
  refine ⟨Set.range boundedNatTailFamily, ?_, ?_, ?_⟩
  · -- Increasing the bound enlarges the corresponding family of tails.
    have hMonotone : Monotone boundedNatTailFamily := by
      intro m n hmn A hA
      obtain ⟨k, hk, rfl⟩ := hA
      exact ⟨k, Set.mem_Iic.mpr ((Set.mem_Iic.mp hk).trans hmn), rfl⟩
    exact hMonotone.isChain_range
  · intro 𝒜 h𝒜
    obtain ⟨n, rfl⟩ := h𝒜
    exact boundedNatTailFamilyCountableIntersectionProperty n
  · intro hUnion
    -- Every natural-number tail occurs at its own finite stage.
    have hTailsSubset :
        Set.range (fun k : ℕ ↦ Set.Ici k) ⊆ ⋃₀ Set.range boundedNatTailFamily := by
      intro A hA
      obtain ⟨k, rfl⟩ := hA
      refine Set.mem_sUnion.mpr ⟨boundedNatTailFamily k, ?_, ?_⟩
      · exact ⟨k, rfl⟩
      · exact ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩
    obtain ⟨x, hx⟩ := hUnion.iInter_nonempty (fun k : ℕ ↦ Set.Ici k)
      (fun k ↦ hTailsSubset ⟨k, rfl⟩)
    -- A common point would have to lie in the strictly later tail `Ici (x + 1)`.
    have hxTail : x ∈ Set.Ici (x + 1) :=
      Set.mem_iInter.mp hx (x + 1)
    have hxImpossible : x + 1 ≤ x := by
      simpa only [Set.mem_Ici] using hxTail
    exact Nat.not_succ_le_self x (Nat.succ_eq_add_one x ▸ hxImpossible)
