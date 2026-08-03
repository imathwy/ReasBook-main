module

public import Topology_Munkres_2000.Book.Exercise_31_6.ClosedMap
public import Topology_Munkres_2000.Book.Proposition_73_1

public section

namespace DunceCap

/-- Remark 73.1 (1): The `n`-fold dunce cap is compact, since its quotient map is
continuous and surjective and the closed disk is compact. -/
instance instCompactSpaceSpace (n : ℕ) : CompactSpace (Space n) :=
  ⟨by
    rw [← Set.image_univ_of_surjective (quotientMap_isQuotientMap n).surjective]
    exact isCompact_univ.image (quotientMap_isQuotientMap n).continuous⟩

/-- Remark 73.1 (2): The `n`-fold dunce cap is normal and `T₁`, hence Hausdorff,
by the closed-map normality result cited in the remark. -/
instance instT4SpaceSpace (n : ℕ) : T4Space (Space n) :=
  (quotientMap_isClosedMap n).t4Space
    (quotientMap_isQuotientMap n).continuous (quotientMap_isQuotientMap n).surjective

end DunceCap
