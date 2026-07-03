import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_36_extra_1 (from Chap05/Sec05_36) -/
open scoped Manifold

universe u𝕜 uE uH uM uE' uH'

section SubmanifoldsWithBoundary

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/- Definition 5.36-extra-1, immersed form: once the manifold-with-boundary structure on the
subtype `S` is fixed, the owner abstraction is the canonical immersion predicate for the subtype
inclusion. -/
#check Manifold.IsImmersion J I ⊤ (Subtype.val : S → M)

/- Definition 5.36-extra-1, embedded form: the corresponding embedded notion is the canonical
smooth-embedding predicate for the same subtype inclusion. -/
#check Manifold.IsSmoothEmbedding J I ⊤ (Subtype.val : S → M)

end SubmanifoldsWithBoundary

/-! ### Definition_5_36_extra_2 (from Chap05/Sec05_36) -/
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "dimM" => Module.finrank ℝ E

/-- Definition 5.36-extra-2: A regular domain in `M` is a properly embedded codimension-`0`
submanifold with boundary. The codimension-`0` owner is the chapter's
`SmoothManifoldWithBoundary dimM S`; `Set.IsRegularDomain` adds the ambient compatibility data
that the subtype inclusion is a smooth embedding and a proper map. -/
class Set.IsRegularDomain (S : Set M) [SmoothManifoldWithBoundary dimM S] : Prop where
  /-- The subtype inclusion of a regular domain into the ambient manifold is a smooth embedding. -/
  isSmoothEmbedding_subtype_val :
    Manifold.IsSmoothEmbedding
      (leeBoundaryModelWithCorners dimM)
      I
      ∞
      (Subtype.val : S → M)
  /-- A regular domain is properly embedded in the ambient manifold. -/
  isProperlyEmbedded : S.IsProperlyEmbedded

/-- The empty subset is a regular domain for any chosen smooth manifold-with-boundary structure on
the empty subtype in the ambient dimension. -/
instance instIsRegularDomainEmpty
    [SmoothManifoldWithBoundary dimM (∅ : Set M)] :
    Set.IsRegularDomain I (∅ : Set M) where
  isSmoothEmbedding_subtype_val := by
    refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
    exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩
  isProperlyEmbedded := isClosed_empty.isProperlyEmbedded

/-! ### Definition_5_36_extra_3 (from Chap05/Sec05_36) -/
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

/-! ### Definition_5_36_extra_4 (from Chap05/Sec05_36) -/
open Set
open scoped Manifold

universe uM

section

variable {n k : ℕ}
variable {M : Type uM}
variable [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The last free coordinate of a `k`-dimensional half-slice, viewed as a coordinate of the
ambient space `ℝ^n`. -/
private def lastFreeCoordinate (hk : 0 < k) (hkn : k ≤ n) : Fin n :=
  ⟨k - 1, lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hk)) hkn⟩

namespace Set

/-- The standard Euclidean `k`-dimensional half-slice of `U ⊆ ℝ^n` obtained by fixing the last
`n - k` coordinates to the values `c` and requiring the last free coordinate to be nonnegative.
This is the boundary analogue of `euclideanSlice`, with the same primitive tail-coordinate data;
the free coordinates carry the standard `k`-dimensional boundary-model geometry. -/
def euclideanHalfSlice (U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (c : Fin (n - k) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { x ∈ euclideanSlice U k hkn c | 0 ≤ x (lastFreeCoordinate hk hkn) }

/-- A subset `S` of an open set `U ⊆ ℝ^n` is a `k`-dimensional half-slice if it is obtained by
fixing the last `n - k` coordinates to constants and requiring the last free coordinate to be
nonnegative. -/
def IsEuclideanHalfSlice (S U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ hk : 0 < k, ∃ hkn : k ≤ n, ∃ c : Fin (n - k) → ℝ, S = euclideanHalfSlice U k hk hkn c

/-- A subset `S ⊆ M` is a `k`-dimensional half-slice in the chart `e` when its image in Euclidean
coordinates is a Euclidean `k`-dimensional half-slice of the chart image `e.target`. -/
def IsHalfSliceInChart (S : Set M) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ℕ) : Prop :=
  (e '' (S ∩ e.source)).IsEuclideanHalfSlice e.target k

end Set

namespace OpenPartialHomeomorph

/-- A boundary slice chart for `S` is a smooth chart in the maximal atlas whose local image of `S`
is a Euclidean `k`-dimensional half-slice. -/
def IsBoundarySliceChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (S : Set M)
    (k : ℕ) : Prop :=
  e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧ S.IsHalfSliceInChart e k

/-- Every boundary slice chart lies in the smooth maximal atlas. -/
theorem IsBoundarySliceChart.mem_maximalAtlas
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {S : Set M} {k : ℕ}
    (he : e.IsBoundarySliceChart S k) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
  he.1

end OpenPartialHomeomorph

namespace Set

section

variable (n : ℕ) {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Definition 5.36-extra-4: A subset `S ⊆ M` satisfies the local `k`-slice condition for
submanifolds with boundary if each point of `S` lies in a smooth chart whose local image of `S`
is either a Euclidean `k`-slice or a Euclidean `k`-dimensional half-slice. -/
class SatisfiesLocalSliceConditionWithBoundary (S : Set M) (k : ℕ) : Prop where
  /-- Every point of `S` lies in the source of some interior or boundary slice chart for `S`. -/
  exists_sliceChart (x : M) (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧ (e.IsSliceChart S k ∨ e.IsBoundarySliceChart S k)

/-- The empty subset satisfies the local slice condition with boundary vacuously. -/
instance satisfiesLocalSliceConditionWithBoundary_empty (k : ℕ) :
    Set.SatisfiesLocalSliceConditionWithBoundary n (∅ : Set M) k := by
  refine ⟨?_⟩
  intro x hx
  cases hx

end

end Set

end

/-! ### Remark_5_36_extra_5 (from Chap05/Sec05_36) -/
-- Semantic recall note: `lean_leansearch` was unavailable in this environment; this remark is
-- matched against the owner theorem already used in the Theorem 5.29 codomain-restriction
-- formalization and recalled again in `Theorem_5_53.lean`.

/-
Remark 5.36-extra-5: as in Theorem 5.29, the boundaryless ambient-manifold hypothesis is not
mathematically needed for part (b), the codomain-restriction statement. In the local
formalization, that observation is represented by the canonical owner theorem already recalled in
Theorem 5.53 (2).
-/
recall Manifold.IsSmoothEmbedding.contMDiff_toSubtype

/-! ### Exercise_5_36 (from Chap05/Sec05_35) -/
-- Semantic Lean search tool unavailable in this environment; the exercise is matched directly
-- against the locally formalized preceding proposition.

/- Exercise 5.36: this exercise asks for the proof of the preceding proposition, whose
formalization in this project is `tangentVector_mem_submanifold_iff_exists_curve`. -/
recall tangentVector_mem_submanifold_iff_exists_curve
