module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

public section

/- Definition 57.2: If `x` is a point of `Sⁿ`, then its antipode is `-x`.
A map `h : Sⁿ → Sᵐ` is antipode-preserving when `h (-x) = -h x` for every
`x ∈ Sⁿ`, which is exactly `Function.Odd h`. -/
#check StandardSphere.antipodal

#check fun {n m : ℕ}
    (h : StandardSphere n → StandardSphere m) ↦ Function.Odd h
