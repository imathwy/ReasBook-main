module

public import Book.Ch4.Example_4_5_1.JointModel

public section

/- Exercise 4.20. The source-facing verification is that, under the normalization
hypotheses already packaged as `K.IsColStochasticRect` and `f ∈ stdSimplex ℝ (Fin n)`,
the mass from equation `(4.60)`, `(j, i) ↦ ENNReal.ofReal (K i j * f j)`, has total
mass `1`. -/
#check NonnegativeEM.jointMass_sum_eq_one

/- With that normalization established, the same source mass defines the canonical
finite joint law `PMF (Fin n × Fin m)`. -/
#check NonnegativeEM.jointPmf

/- The same model is exposed as the parameterized joint family `NonnegativeEM.jointFamily`
for reuse with the generic `DiscreteEM` API. -/
#check NonnegativeEM.jointFamily
