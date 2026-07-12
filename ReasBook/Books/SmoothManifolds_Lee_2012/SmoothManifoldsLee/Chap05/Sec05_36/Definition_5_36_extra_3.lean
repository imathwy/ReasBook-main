import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold

universe uE uE' uH uH' uM uN

-- Semantic search note: `lean_leansearch` was unavailable in this environment; local project
-- precedent was checked against nearby defining-map and regular-value files.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H)
variable (J : ModelWithCorners ℝ E' H')
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

namespace Manifold

/-- A point `c` is a regular value of a smooth map `F : M → N` if every point of the fiber
`F⁻¹({c})` has surjective manifold derivative. -/
def IsRegularValue (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') (F : M → N)
    (c : N) : Prop :=
  ∀ x : M, F x = c → Function.Surjective (mfderiv I J F x)

/-- A regular value is characterized by surjectivity of the manifold derivative on the level set. -/
theorem isRegularValue_iff (F : M → N) (c : N) :
    IsRegularValue I J F c ↔
      ∀ x : M, F x = c → Function.Surjective (mfderiv I J F x) := sorry

end Manifold

variable [IsManifold I ∞ M]

/-- Definition 5.36-extra-3: a subset `D` is a regular sublevel set of `f` if
`D = f⁻¹' (-∞, b]` for some regular value `b` of `f`. -/
class IsRegularSublevelSet (I : ModelWithCorners ℝ E H) (f : M → ℝ) (D : Set M) : Prop where
  /-- The given subset is the closed sublevel set cut out by some regular value of `f`. -/
  exists_regular_value :
    ∃ b : ℝ, Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b ∧ D = f ⁻¹' Set.Iic b

/-- An `IsRegularSublevelSet` hypothesis canonically yields the witnessing regular value data. -/
instance (f : M → ℝ) (D : Set M) [h : IsRegularSublevelSet I f D] :
    Fact (∃ b : ℝ, Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b ∧ D = f ⁻¹' Set.Iic b) :=
  ⟨h.exists_regular_value⟩

/-- A smooth function is a defining function for `D` if `D` is one of its regular sublevel sets. -/
class IsDefiningFunction (I : ModelWithCorners ℝ E H) (D : Set M) (f : M → ℝ) : Prop where
  /-- The defining function is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  /-- The given domain is a regular sublevel set of the defining function. -/
  isRegularSublevelSet : IsRegularSublevelSet I f D

/-- A regular sublevel set is exactly the inverse image of a closed ray `(-∞, b]` for some regular
value `b`. -/
-- Proof sketch: unfold `IsRegularSublevelSet` and expose the witnessing regular value.
theorem isRegularSublevelSet_iff (f : M → ℝ) (D : Set M) :
    IsRegularSublevelSet I f D ↔
      ∃ b : ℝ, Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b ∧ D = f ⁻¹' Set.Iic b := sorry

/-- A defining function is a smooth function whose given domain is one of its regular sublevel
sets. -/
-- Proof sketch: unfold `IsDefiningFunction` and read off its two defining clauses.
theorem isDefiningFunction_iff (D : Set M) (f : M → ℝ) :
    IsDefiningFunction I D f ↔ ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ IsRegularSublevelSet I f D := sorry
