module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public section

/- Proposition 50.1 (1): A family consisting of one point is affinely independent. -/
#check affineIndependent_of_subsingleton

/- Proposition 50.1 (2): A family is affinely independent exactly when its difference
vectors from any chosen point are linearly independent. -/
#check affineIndependent_iff_linearIndependent_vsub

/- Proposition 50.1 (3): Two distinct points are affinely independent. -/
#check affineIndependent_of_ne

/- Proposition 50.1 (4): Three points are affinely independent exactly when they are not
collinear. -/
#check affineIndependent_iff_not_collinear

/-- Four points are affinely independent exactly when they are not coplanar. -/
theorem affineIndependent_iff_not_coplanar {k V P : Type*} [DivisionRing k]
    [AddCommGroup V] [Module k V] [AddTorsor V P] (p : Fin 4 → P) :
    AffineIndependent k p ↔ ¬ Coplanar k (Set.range p) := by
  have hcard : Fintype.card (Fin 4) = 3 + 1 := by decide
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hcard, coplanar_iff_finrank_le_two]
  have h := finrank_vectorSpan_range_le k p hcard
  omega

/-- Proposition 50.1 (5): Four noncoplanar points are affinely independent. In particular,
this applies to four points in `ℝ³`. -/
theorem affineIndependent_of_not_coplanar {k V P : Type*} [DivisionRing k]
    [AddCommGroup V] [Module k V] [AddTorsor V P] {p : Fin 4 → P}
    (h : ¬ Coplanar k (Set.range p)) : AffineIndependent k p :=
  (affineIndependent_iff_not_coplanar p).2 h
