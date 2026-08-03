import BauschkeLean.Chap09.Proposition_9_18

universe u v

namespace ERealFunction

section ProductL2Scope

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Scoped `ℓ²` pseudometric structure on the raw product `H × K`, transported from
`WithLp 2 (H × K)`. Open `ERealFunctionProductL2` when a file needs the textbook Hilbert geometry
on the raw product type. -/
noncomputable instance instProdPseudoMetricSpaceL2 :
    PseudoMetricSpace (H × K) :=
  prod_pseudoMetricSpace_l2 (H := H) (K := K)

/-- Scoped `ℓ²` seminormed additive group structure on the raw product `H × K`. -/
noncomputable instance instProdSeminormedAddCommGroupL2 :
    SeminormedAddCommGroup (H × K) :=
  prod_seminormedAddCommGroup_l2 (H := H) (K := K)

/-- Scoped `ℓ²` normed additive group structure on the raw product `H × K`. -/
noncomputable instance instProdNormedAddCommGroupL2 :
    NormedAddCommGroup (H × K) :=
  prod_normedAddCommGroup_l2 (H := H) (K := K)

/-- Scoped `ℓ²` scalar-action structure on the raw product `H × K`. -/
noncomputable instance instProdNormedSpaceL2 :
    NormedSpace ℝ (H × K) :=
  prod_normedSpace_l2 (H := H) (K := K)

/-- Scoped `ℓ²` completeness on the raw product `H × K`. -/
noncomputable instance instProdCompleteSpaceL2
    [CompleteSpace H] [CompleteSpace K] : CompleteSpace (H × K) :=
  prod_completeSpace_l2 (H := H) (K := K)

/-- Scoped `ℓ²` Hilbert structure on the raw product `H × K`. -/
noncomputable instance instProdInnerProductSpaceL2 :
    InnerProductSpace ℝ (H × K) :=
  prod_innerProductSpace_l2 (H := H) (K := K)

end ProductL2Scope

namespace ProductL2

attribute [scoped instance]
  ERealFunction.instProdPseudoMetricSpaceL2
  ERealFunction.instProdSeminormedAddCommGroupL2
  ERealFunction.instProdNormedAddCommGroupL2
  ERealFunction.instProdNormedSpaceL2
  ERealFunction.instProdCompleteSpaceL2
  ERealFunction.instProdInnerProductSpaceL2

end ProductL2

end ERealFunction
