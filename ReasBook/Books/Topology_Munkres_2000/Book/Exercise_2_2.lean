module

public import Topology_Munkres_2000.Book.Exercise_2_1

public section

open Set

universe u v

/- Exercise 2.2 (1): Preimages preserve inclusions. -/
#check Set.preimage_mono

/- Exercise 2.2 (2): Preimages preserve binary unions. -/
#check Set.preimage_union

/- Exercise 2.2 (3): Preimages preserve binary intersections. -/
#check Set.preimage_inter

/- Exercise 2.2 (4): Preimages preserve set difference. -/
#check Set.preimage_sdiff

/- Exercise 2.2 (5): Images preserve inclusions. -/
#check Set.image_mono

/- Exercise 2.2 (6): Images preserve binary unions. -/
#check Set.image_union

/- Exercise 2.2 (7): The image of an intersection is contained in the intersection
of the images. -/
#check Set.image_inter_subset

/- Exercise 2.2 (8): For an injective function, the image of an intersection is the
intersection of the images. -/
#check Set.image_inter

/-- Exercise 2.2 (9): The difference of two images is contained in the image of the
difference. -/
theorem Set.subset_image_sdiff {A : Type u} {B : Type v} (f : A → B) (A₀ A₁ : Set A) :
    f '' A₀ \ f '' A₁ ⊆ f '' (A₀ \ A₁) := by
  rw [sdiff_subset_iff, ← image_union, union_sdiff_self]
  exact image_mono subset_union_right

/- Exercise 2.2 (10): For an injective function, images preserve set difference. -/
#check Set.image_sdiff
