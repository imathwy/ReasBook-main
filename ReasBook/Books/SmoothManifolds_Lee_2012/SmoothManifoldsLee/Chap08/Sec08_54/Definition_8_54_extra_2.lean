import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item uses
-- the local dependent-section pattern from `Lemma_8_6.lean` together with mathlib's canonical
-- tangent-bundle owner `TangentBundle I M` and smooth-section notation `CMDiff[V] n (T% X)`.

section

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I (∞ : ℕ∞ω) M]

namespace VectorField

/-- Definition 8.54-extra-2 (1): a vector field along `A ⊆ M` is represented in Lean by a
dependent section `X : ∀ x : A, TangentSpace I (x : M)` whose associated map into the ambient
tangent bundle is continuous. The condition `π ∘ X = id_A` is built into the dependent type of the
values. -/
structure Along (A : Set M) where
  toSection : ∀ x : A, TangentSpace I (x : M)
  continuous_toTangentMap :
    Continuous (fun x : A ↦ (⟨(x : M), toSection x⟩ : TangentBundle I M))

/-- A vector field along `A` can be evaluated pointwise as a tangent vector based at a point of
`A`. -/
instance {A : Set M} : CoeFun (Along A) (fun _ ↦ ∀ x : A, TangentSpace I (x : M)) where
  coe X := X.toSection

/-- The ambient tangent-bundle-valued map associated to a vector field along `A`. -/
def Along.toTangentMap {A : Set M} (X : Along A) : A → TangentBundle I M :=
  fun x ↦ ⟨(x : M), X.toSection x⟩

/-- Unfolding of the ambient tangent-bundle-valued map associated to a vector field along `A`. -/
theorem Along.toTangentMap_apply {A : Set M} (X : Along A) (x : A) :
    X.toTangentMap x = (⟨(x : M), X.toSection x⟩ : TangentBundle I M) := sorry

/-- The ambient tangent-bundle-valued map of a vector field along `A` projects to the identity on
`A`. -/
theorem Along.proj_toTangentMap {A : Set M} (X : Along A) (x : A) :
    (X.toTangentMap x).proj = (x : M) := sorry

/-- Definition 8.54-extra-2 (2): a vector field along `A` is smooth if every point of `A` has an
open neighborhood in `M` on which the field agrees with a smooth ambient vector field. -/
class Along.IsSmooth {A : Set M} (X : Along A) : Prop where
  /-- Every point of `A` has a neighborhood on which `X` agrees with a smooth ambient vector
  field. -/
  local_extension :
      ∀ x : A, ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      ∃ Xloc : ∀ y : M, TangentSpace I y,
        CMDiff[V] (∞ : ℕ∞ω) (T% Xloc) ∧
          ∀ y : A, (y : M) ∈ V → Xloc y = X.toSection y

/-- A smooth vector field along `A` has a continuous ambient tangent-bundle-valued map. -/
instance {A : Set M} {X : Along A} [_hX : Along.IsSmooth X] :
    Continuous X.toTangentMap :=
  X.continuous_toTangentMap

/-- Local ambient smooth extension is the defining criterion for a smooth vector field along a
subset. -/
theorem Along.isSmooth_iff {A : Set M} (X : Along A) :
    Along.IsSmooth X ↔
      ∀ x : A, ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
        ∃ Xloc : ∀ y : M, TangentSpace I y,
          CMDiff[V] (∞ : ℕ∞ω) (T% Xloc) ∧
            ∀ y : A, (y : M) ∈ V → Xloc y = X.toSection y := sorry

end VectorField

end
