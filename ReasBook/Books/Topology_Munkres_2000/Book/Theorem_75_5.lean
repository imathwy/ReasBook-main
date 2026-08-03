module

public import Topology_Munkres_2000.Book.Theorem_75_5.Classification

import Topology_Munkres_2000.Book.Corollary_60_7
import Topology_Munkres_2000.Book.Theorem_75_3
import Topology_Munkres_2000.Book.Theorem_75_4

public section

open NonorientableSurfacePresentation OrientableSurfacePresentation

/-- Theorem 75.5 (1). The 2-sphere is not homeomorphic to any positive-genus
orientable surface. -/
theorem twoSphere_not_homeomorphic_nFoldTorus (n : ℕ) (hn : 0 < n) :
    ¬ Nonempty (StandardSphere 2 ≃ₜ nFoldTorus n hn) := sorry

/- Theorem 75.5 (2). The 2-sphere is not homeomorphic to the real projective plane. -/
#check twoSphere_not_homeomorphic_realProjectivePlane

/-- Theorem 75.5 (3). The 2-sphere is not homeomorphic to any higher-genus
nonorientable surface. -/
theorem twoSphere_not_homeomorphic_mFoldProjectivePlane (m : ℕ) (hm : 1 < m) :
    ¬ Nonempty (StandardSphere 2 ≃ₜ mFoldProjectivePlane m hm) := sorry

/-- Theorem 75.5 (4). Orientable surfaces of distinct positive genera are not
homeomorphic. -/
theorem nFoldTorus_not_homeomorphic_of_ne (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hne : n ≠ k) :
    ¬ Nonempty (nFoldTorus n hn ≃ₜ nFoldTorus k hk) := sorry

/-- Theorem 75.5 (5). No positive-genus orientable surface is homeomorphic to the
real projective plane. -/
theorem nFoldTorus_not_homeomorphic_realProjectivePlane (n : ℕ) (hn : 0 < n) :
    ¬ Nonempty (nFoldTorus n hn ≃ₜ RealProjectivePlane) := sorry

/-- Theorem 75.5 (6). No positive-genus orientable surface is homeomorphic to a
higher-genus nonorientable surface. -/
theorem nFoldTorus_not_homeomorphic_mFoldProjectivePlane (n m : ℕ) (hn : 0 < n)
    (hm : 1 < m) :
    ¬ Nonempty (nFoldTorus n hn ≃ₜ mFoldProjectivePlane m hm) := sorry

/-- Theorem 75.5 (7). The real projective plane is not homeomorphic to any
higher-genus nonorientable surface. -/
theorem realProjectivePlane_not_homeomorphic_mFoldProjectivePlane (m : ℕ)
    (hm : 1 < m) :
    ¬ Nonempty (RealProjectivePlane ≃ₜ mFoldProjectivePlane m hm) := sorry

/-- Theorem 75.5 (8). Nonorientable surfaces of distinct genera greater than one
are not homeomorphic. -/
theorem mFoldProjectivePlane_not_homeomorphic_of_ne (m r : ℕ) (hm : 1 < m)
    (hr : 1 < r) (hne : m ≠ r) :
    ¬ Nonempty (mFoldProjectivePlane m hm ≃ₜ mFoldProjectivePlane r hr) := sorry

end
