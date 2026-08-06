import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SuspensionSphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1

noncomputable section

open scoped Topology Topology.Homotopy

-- Semantic recall: `lean_leansearch` surfaced `HomotopyGroup.Pi` as the canonical owner for
-- homotopy groups, and local Chapter 11 precedent already fixes `suspensionSphere n := Σ^n S⁰`
-- and `suspensionPiMap`/`suspensionHomomorphism` as the sphere/suspension owners used here.

/-- Theorem 11.2.3 (1): for every positive `n`, the `n`th homotopy group `π_ n(S^n)` at the
Chapter 11 sphere owner `suspensionSphere (n : ℕ) = Σ^n S^0`, representing `S^n`, is infinite
cyclic. -/
theorem spherePiSelfMulEquivInt (n : ℕ+) :
    Nonempty
      (π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
          (suspensionSphere (n : ℕ)).point ≃* Multiplicative ℤ) := sorry

/-- Theorem 11.2.3 (2): for every positive `n`, the suspension map on the canonical pointed
Chapter 11 sphere owner `suspensionSphere (n : ℕ) = Σ^n S^0`, representing `S^n`, induces a
bijective map on homotopy groups. This is the source map
`π_ n(S^n) → π_ (n + 1)(S^(n + 1))` expressed on the quotient-level owner
`suspensionPiMap (n : ℕ) (suspensionSphere (n : ℕ))`. -/
theorem sphereSuspensionPiMap_bijective (n : ℕ+) :
    Function.Bijective
      (suspensionPiMap (n : ℕ) (suspensionSphere (n : ℕ))) := sorry

/-- Theorem 11.2.3 (2) can also be read on the positive-degree group-hom owner
`suspensionHomomorphism (n : ℕ) (suspensionSphere (n : ℕ))`. -/
theorem sphereSuspensionHomomorphism_bijective (n : ℕ+) :
    Function.Bijective
      (suspensionHomomorphism (n : ℕ) (suspensionSphere (n : ℕ))) := by
  change Function.Bijective (suspensionPiMap (n : ℕ) (suspensionSphere (n : ℕ)))
  exact sphereSuspensionPiMap_bijective n
