import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_29_extra_1 (from Chap05/Sec05_29) -/
open Set ChartedSpace
open scoped Manifold

universe u

namespace Set

private def tailCoordinate {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k)

/-- The standard Euclidean `k`-slice of `U ⊆ ℝ^n` obtained by fixing the last `n - k`
coordinates to the values `c`. -/
def euclideanSlice {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { x ∈ U | ∀ i : Fin (n - k), x (tailCoordinate hk i) = c i }

/-- A subset `S` of an open set `U ⊆ ℝ^n` is a `k`-slice if it is obtained by fixing the last
`n - k` coordinates to constants. -/
def IsEuclideanSlice {n : ℕ} (S U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ hk : k ≤ n, ∃ c : Fin (n - k) → ℝ, S = euclideanSlice U k hk c

/-- A subset `S ⊆ M` is a `k`-slice in the chart `e` when its image in Euclidean coordinates is
a Euclidean `k`-slice of the chart image `e.target`. -/
def IsSliceInChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (S : Set M) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  (e '' (S ∩ e.source)).IsEuclideanSlice e.target k

end Set

namespace OpenPartialHomeomorph

/-- A slice chart for `S` is a smooth chart in the maximal atlas whose local image of `S`
is a Euclidean `k`-slice. -/
def IsSliceChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (S : Set M)
    (k : ℕ) : Prop :=
  e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧
    S.IsSliceInChart e k

/-- Every slice chart lies in the smooth maximal atlas. -/
theorem IsSliceChart.mem_maximalAtlas
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {S : Set M} {k : ℕ}
    (he : e.IsSliceChart S k) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
  he.1

end OpenPartialHomeomorph

namespace Set

section

variable (n : ℕ) {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Definition 5.29-extra-1: a subset `S` of an `n`-manifold satisfies the local `k`-slice
condition if each point of `S` lies in the source of some smooth slice chart for `S`; any such
chart gives slice coordinates for `S`. -/
class SatisfiesLocalSliceCondition (S : Set M) (k : ℕ) : Prop where
  /-- Every point of `S` lies in the source of some slice chart for `S`. -/
  exists_sliceChart (x : M) (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧ e.IsSliceChart S k

/-- The empty subset satisfies the local `k`-slice condition vacuously. -/
instance satisfiesLocalSliceCondition_empty (k : ℕ) :
    Set.SatisfiesLocalSliceCondition n (∅ : Set M) k := by
  refine ⟨?_⟩
  intro x hx
  cases hx

end

end Set

/-! ### Remark_5_29_extra_2 (from Chap05/Sec05_29) -/
open scoped ContDiff Manifold

section LocalSliceUniqueness

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
variable (S : Set M)

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was chosen from the local `Set.SatisfiesLocalSliceCondition`,
-- `local_slice_condition_has_embedded_submanifold_structure`, and
-- `immersed_submanifold_structure_unique_of_same_carrier` APIs.

/- Remark 5.29-extra-2 (1): `Set.SatisfiesLocalSliceCondition n S k` is already a predicate on the
subset `S ⊆ M` inside the ambient manifold `M`; it does not assume any topology or smooth
structure on the subtype `S` itself. -/
recall Set.SatisfiesLocalSliceCondition

/-- Remark 5.29-extra-2: a subset satisfying the local `k`-slice condition carries the
canonical embedded-submanifold structure from Theorem 5.8, and any immersed submanifold structure
on the same underlying subset is diffeomorphic to it through the ambient inclusion. In
particular, `S` can be regarded as an embedded submanifold of `M` in only one way. -/
theorem local_slice_condition_unique_submanifold_structure
    (hS : Set.SatisfiesLocalSliceCondition n S k) :
    ∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S,
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
        ∃ hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S,
          ∀ T : Manifold.ImmersedSubmanifold (𝓡 n) M,
            T.carrier = S →
            ∃ Φ : T ≃ₘ⟮modelWithCornersSelf ℝ T.ModelSpace, 𝓡 k⟯ S,
              ∀ x : T, (Φ x : M) = T.inclusion x := sorry

end LocalSliceUniqueness

/-! ### Remark_5_29_extra_3 (from Chap05/Sec05_29) -/
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this remark is
-- matched directly against the later local formalization in `Theorem_5_31.lean`.

/- Remark 5.29-extra-3: the claim that the smooth structure on `∂ M` is unique is deferred to
Theorem 5.31; in the local formalization, it is represented by the general uniqueness theorem for
immersed submanifold structures on a fixed underlying subset, applied to the boundary subset. -/
recall immersed_submanifold_structure_unique_of_same_carrier

/-! ### Theorem_5_29 (from Chap05/Sec05_32) -/
open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH' uE'' uH'' uN

section RestrictingCodomainOfSmoothMaps

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M] [BoundarylessManifold I M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S] [BoundarylessManifold J S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was checked against the local `IsImmersedSubmanifold` and `contMDiff_toSubtype` APIs.
/-- Theorem 5.29 (Restricting the Codomain of a Smooth Map): if `S ⊆ M` is an immersed
submanifold, `F : N → M` is smooth with image contained in `S`, and the codomain-restricted map
`N → S` is continuous, then `F` is smooth as a map to `S`. -/
theorem contMDiff_toSubtype_of_isImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S)
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S)
    (hcont : Continuous (Set.codRestrict F S hFS)) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := sorry

end RestrictingCodomainOfSmoothMaps
