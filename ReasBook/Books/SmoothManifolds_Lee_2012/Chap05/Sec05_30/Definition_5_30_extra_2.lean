import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Proposition_4_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold

universe uE uE' uH uH' uM uN

-- Semantic search note: `lean_leansearch` was unavailable in this environment; local project
-- precedent was checked against the nearby regular-value and submersion files.

namespace Manifold

section RegularPoints

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}

/-- Definition 5.30-extra-2 (1): a point `p` is a regular point of `Φ : M → N` when the manifold
derivative `mfderiv I J Φ p` is surjective. -/
def IsRegularPoint (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (p : M) : Prop :=
  Function.Surjective (mfderiv I J Φ p)

/-- `IsRegularPoint` means surjectivity of the manifold derivative at the given point. -/
theorem isRegularPoint_iff_surjective_mfderiv (Φ : M → N) (p : M) :
    IsRegularPoint I J Φ p ↔ Function.Surjective (mfderiv I J Φ p) := sorry

/-- Definition 5.30-extra-2 (2): a point `p` is a critical point of `Φ : M → N` when `p` is not a
regular point of `Φ`. -/
def IsCriticalPoint (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (p : M) : Prop :=
  ¬ IsRegularPoint I J Φ p

/-- A point is critical exactly when it is not regular. -/
theorem isCriticalPoint_iff_not_isRegularPoint (Φ : M → N) (p : M) :
    IsCriticalPoint I J Φ p ↔ ¬ IsRegularPoint I J Φ p := sorry

/-- Definition 5.30-extra-2 (3): a value `c` is regular exactly when every point of the level set
`Φ⁻¹({c})` is a regular point of `Φ`. This uses the canonical local definition
`Manifold.IsRegularValue`. -/
theorem isRegularValue_iff_forall_isRegularPoint (Φ : M → N) (c : N) :
    IsRegularValue I J Φ c ↔ ∀ p : M, Φ p = c → IsRegularPoint I J Φ p := sorry

/-- A value with empty fiber is a regular value. -/
theorem isRegularValue_of_preimage_eq_empty {Φ : M → N} {c : N}
    (h : Φ ⁻¹' ({c} : Set N) = ∅) :
    IsRegularValue I J Φ c := sorry

/-- Definition 5.30-extra-2 (4): a value `c` is a critical value of `Φ : M → N` when `c` is not a
regular value of `Φ`. -/
def IsCriticalValue (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (c : N) : Prop :=
  ¬ IsRegularValue I J Φ c

/-- A value is critical exactly when some point of its level set is a critical point. -/
theorem isCriticalValue_iff_exists_critical_point (Φ : M → N) (c : N) :
    IsCriticalValue I J Φ c ↔ ∃ p : M, Φ p = c ∧ IsCriticalPoint I J Φ p := sorry

/-- Definition 5.30-extra-2 (5): the level set `Φ⁻¹({c})` is a regular level set when `c` is a
regular value of `Φ`. -/
def IsRegularLevelSet (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (Φ : M → N) (c : N) : Prop :=
  IsRegularValue I J Φ c

/-- A level set is regular exactly when every point of that level set is a regular point. -/
theorem isRegularLevelSet_iff_forall_mem_preimage_isRegularPoint (Φ : M → N) (c : N) :
    IsRegularLevelSet I J Φ c ↔
      ∀ p : M, p ∈ Φ ⁻¹' ({c} : Set N) → IsRegularPoint I J Φ p := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- If the source manifold dimension is smaller than the target manifold dimension, then every
point is critical. -/
theorem isCriticalPoint_of_model_finrank_lt {Φ : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') (p : M) :
    IsCriticalPoint I J Φ p := sorry

/-- A smooth map is a smooth submersion exactly when every point of the source is a regular
point. -/
theorem isSmoothSubmersion_iff_forall_isRegularPoint {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ) :
    IsSmoothSubmersion I J Φ ↔ ∀ p : M, IsRegularPoint I J Φ p := sorry

/-- The regular points of a smooth map form an open subset of the source manifold. -/
theorem isOpen_setOf_isRegularPoint {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ) :
    IsOpen {p : M | IsRegularPoint I J Φ p} := sorry

end FiniteDimensional

end RegularPoints

end Manifold
