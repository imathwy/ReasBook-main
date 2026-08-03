module

public import Mathlib.Data.Set.Lattice.Image

open Set

/- Exercise 2.1 (1): Every set is contained in the preimage of its image. -/
#check subset_preimage_image

/- Exercise 2.1 (2): For an injective function, the preimage of the image of a set
equals the original set. -/
#check preimage_image_eq

/- Exercise 2.1 (3): The image of the preimage of a set is contained in that set. -/
#check image_preimage_subset

/- Exercise 2.1 (4): For a surjective function, the image of the preimage of a set
equals the original set. -/
#check image_preimage_eq
