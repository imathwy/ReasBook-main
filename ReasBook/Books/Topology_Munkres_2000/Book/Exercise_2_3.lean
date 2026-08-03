module

public import Topology_Munkres_2000.Book.Exercise_2_2

public section

open Set

universe u v w

/- Exercise 2.3 (b): Preimages preserve arbitrary indexed unions. -/
#check Set.preimage_iUnion

/- Exercise 2.3 (c): Preimages preserve arbitrary indexed intersections. -/
#check Set.preimage_iInter

/- Exercise 2.3 (f): Images preserve arbitrary indexed unions. -/
#check Set.image_iUnion

/- Exercise 2.3 (g): The image of an arbitrary indexed intersection is contained in
the intersection of the images. -/
#check Set.image_iInter_subset

/-- Exercise 2.3 (g), equality case: An injective function preserves intersections of nonempty
indexed families under images. -/
theorem Function.Injective.image_iInter_eq {A : Type u} {B : Type v} {ι : Type w}
    [Nonempty ι] {f : A → B} (hf : f.Injective) (s : ι → Set A) :
    f '' (⋂ i, s i) = ⋂ i, f '' s i :=
  hf.injOn.image_iInter_eq
