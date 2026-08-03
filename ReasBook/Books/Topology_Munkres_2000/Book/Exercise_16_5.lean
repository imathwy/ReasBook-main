module

public import Topology_Munkres_2000.Book.Exercise_16_5.ProductTopology

public section

universe u v

/- Exercise 16.5 (a): If `𝒯'` and `𝒰'` are finer than `𝒯` and `𝒰`, respectively,
then their product topology is finer as well. A finer topology is smaller in Lean's
order on `TopologicalSpace`. -/
#check TopologicalSpace.prod_mono

/-- Helper for Exercise 16.5: a constant-right-coordinate section induces the
left factor topology from an explicit product topology. -/
lemma TopologicalSpace.induced_prodMkLeft_prod {X : Type u} {Y : Type v}
    (𝒯 : TopologicalSpace X) (𝒰 : TopologicalSpace Y) (y : Y) :
    induced (fun x : X ↦ (x, y)) (prod 𝒯 𝒰) = 𝒯 := by
  -- Pull the two projection topologies back along the section, obtaining `𝒯 ⊓ ⊤`.
  letI : TopologicalSpace X := 𝒯
  letI : TopologicalSpace Y := 𝒰
  simp only [prod, induced_inf, induced_compose, Function.comp_def, induced_fun_id,
    induced_const, inf_top_eq]

/-- Helper for Exercise 16.5: a constant-left-coordinate section induces the
right factor topology from an explicit product topology. -/
lemma TopologicalSpace.induced_prodMkRight_prod {X : Type u} {Y : Type v}
    (𝒯 : TopologicalSpace X) (𝒰 : TopologicalSpace Y) (x : X) :
    induced (fun y : Y ↦ (x, y)) (prod 𝒯 𝒰) = 𝒰 := by
  -- Pull the two projection topologies back along the section, obtaining `⊤ ⊓ 𝒰`.
  letI : TopologicalSpace X := 𝒯
  letI : TopologicalSpace Y := 𝒰
  simp only [prod, induced_inf, induced_compose, Function.comp_def, induced_fun_id,
    induced_const, top_inf_eq]

/-- Exercise 16.5 (b): For nonempty factors, refinement of product topologies
implies refinement of each factor topology. Thus the converse of part (a) holds. -/
theorem TopologicalSpace.prod_le_prod_iff {X : Type u} {Y : Type v}
    [Nonempty X] [Nonempty Y] {𝒯 𝒯' : TopologicalSpace X} {𝒰 𝒰' : TopologicalSpace Y} :
    prod 𝒯' 𝒰' ≤ prod 𝒯 𝒰 ↔ 𝒯' ≤ 𝒯 ∧ 𝒰' ≤ 𝒰 := by
  constructor
  · intro hprod
    rcases (inferInstance : Nonempty X) with ⟨x⟩
    rcases (inferInstance : Nonempty Y) with ⟨y⟩
    constructor
    · -- Pull back the product refinement along `x ↦ (x, y)` to recover `𝒯' ≤ 𝒯`.
      calc
        𝒯' = induced (fun z : X ↦ (z, y)) (prod 𝒯' 𝒰') :=
          (induced_prodMkLeft_prod 𝒯' 𝒰' y).symm
        _ ≤ induced (fun z : X ↦ (z, y)) (prod 𝒯 𝒰) := induced_mono hprod
        _ = 𝒯 := induced_prodMkLeft_prod 𝒯 𝒰 y
    · -- Pull back along `y ↦ (x, y)` to recover the second factor refinement.
      calc
        𝒰' = induced (fun z : Y ↦ (x, z)) (prod 𝒯' 𝒰') :=
          (induced_prodMkRight_prod 𝒯' 𝒰' x).symm
        _ ≤ induced (fun z : Y ↦ (x, z)) (prod 𝒯 𝒰) := induced_mono hprod
        _ = 𝒰 := induced_prodMkRight_prod 𝒯 𝒰 x
  · rintro ⟨h𝒯, h𝒰⟩
    -- Coordinatewise refinement gives product refinement by Mathlib's monotonicity theorem.
    exact prod_mono h𝒯 h𝒰
