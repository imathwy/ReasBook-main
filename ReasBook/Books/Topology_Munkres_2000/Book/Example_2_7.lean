module

import Mathlib.Data.Set.Image

/- Example 2.7 (1): Every set is contained in the preimage of its image. -/
#check Set.subset_preimage_image

/- Example 2.7 (2): The image of a preimage is contained in the original set. -/
#check Set.image_preimage_subset

/- Example 2.7 (3): For an injective function, the preimage of an image equals the original set. -/
#check Set.preimage_image_eq

/- Example 2.7 (4): For a surjective function, the image of a preimage equals the original set. -/
#check Set.image_preimage_eq
