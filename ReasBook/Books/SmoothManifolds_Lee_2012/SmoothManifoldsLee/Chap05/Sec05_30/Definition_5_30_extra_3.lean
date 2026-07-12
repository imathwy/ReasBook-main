import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Sets.Opens

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section DefiningMaps

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

namespace Set

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against local project precedent for regular-value and local-open-subset APIs.
/-- Definition 5.30-extra-3 (1): a smooth map `Φ : M → N` is a defining map for `S ⊆ M` if `S` is
the level set of some value `c : N` and the manifold derivative of `Φ` is surjective at every
point of `S`. -/
class IsDefiningMap (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (Φ : M → N) where
  level : N
  contMDiff : ContMDiff I J ∞ Φ
  isLevelSet : S = Φ ⁻¹' {level}
  surj_mfderiv : ∀ x : M, x ∈ S → Function.Surjective (mfderiv I J Φ x)

/-- A defining map canonically provides the smoothness hypothesis as a `Fact`. -/
instance instFactContMDiffIsDefiningMap (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (Φ : M → N) (h : IsDefiningMap I J S Φ) :
    Fact (ContMDiff I J ∞ Φ) where
  out := h.contMDiff

/-- A defining function is a defining map whose codomain is a finite-dimensional real vector
space `ℝ^k`, represented in Lean as `Fin k → ℝ`. -/
abbrev IsDefiningFunction (I : ModelWithCorners ℝ E H) (S : Set M) {k : ℕ}
    (f : M → Fin k → ℝ) :=
  IsDefiningMap I 𝓘(ℝ, Fin k → ℝ) S f

/-- Definition 5.30-extra-3 (2): a smooth map `Φ : U → N` on an open subset `U ⊆ M` is a local
defining map for `S ⊆ M` if the points of `S` lying in `U` are exactly one level set of `Φ` and
the manifold derivative of `Φ` is surjective at each such point. -/
class IsLocalDefiningMapOn (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N) where
  level : N
  contMDiff : ContMDiff I J ∞ Φ
  isLevelSet : {x : U | (x : M) ∈ S} = Φ ⁻¹' {level}
  surj_mfderiv : ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I J Φ x)

/-- A local defining map canonically provides the smoothness hypothesis as a `Fact`. -/
instance instFactContMDiffIsLocalDefiningMapOn (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N)
    (h : IsLocalDefiningMapOn I J S U Φ) :
    Fact (ContMDiff I J ∞ Φ) where
  out := h.contMDiff

/-- A local defining function is a local defining map whose codomain is `ℝ^k`, represented as
`Fin k → ℝ`. -/
abbrev IsLocalDefiningFunctionOn (I : ModelWithCorners ℝ E H) (S : Set M)
    (U : TopologicalSpace.Opens M) {k : ℕ} (f : U → Fin k → ℝ) :=
  IsLocalDefiningMapOn I 𝓘(ℝ, Fin k → ℝ) S U f

/-- Existence of a `Set.IsDefiningMap` structure is equivalent to specifying the chosen level
value, smoothness, level-set equation, and surjective derivative condition. -/
theorem isDefiningMap_iff (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (S : Set M) (Φ : M → N) :
    Nonempty (IsDefiningMap I J S Φ) ↔
      ∃ c : N,
        ContMDiff I J ∞ Φ ∧
          S = Φ ⁻¹' {c} ∧
          ∀ x : M, x ∈ S → Function.Surjective (mfderiv I J Φ x) := sorry

/-- Existence of a `Set.IsDefiningFunction` structure is equivalent to the corresponding explicit
`ℝ^k`-valued defining-map conditions. -/
theorem isDefiningFunction_iff (I : ModelWithCorners ℝ E H) (S : Set M) {k : ℕ}
    (f : M → Fin k → ℝ) :
    Nonempty (IsDefiningFunction I S f) ↔
      ∃ c : Fin k → ℝ,
        ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ f ∧
          S = f ⁻¹' {c} ∧
          ∀ x : M, x ∈ S → Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) f x) := sorry

/-- Existence of a `Set.IsLocalDefiningMapOn` structure is equivalent to specifying the chosen
level value on the open subset, the smoothness of `Φ`, the level-set equation, and surjectivity of
the derivative along `S ∩ U`. -/
theorem isLocalDefiningMapOn_iff (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E' H') (S : Set M) (U : TopologicalSpace.Opens M) (Φ : U → N) :
    Nonempty (IsLocalDefiningMapOn I J S U Φ) ↔
      ∃ c : N,
        ContMDiff I J ∞ Φ ∧
          {x : U | (x : M) ∈ S} = Φ ⁻¹' {c} ∧
          ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I J Φ x) := sorry

/-- Existence of a `Set.IsLocalDefiningFunctionOn` structure is equivalent to the corresponding
explicit `ℝ^k`-valued local defining-map conditions. -/
theorem isLocalDefiningFunctionOn_iff (I : ModelWithCorners ℝ E H) (S : Set M)
    (U : TopologicalSpace.Opens M) {k : ℕ} (f : U → Fin k → ℝ) :
    Nonempty (IsLocalDefiningFunctionOn I S U f) ↔
      ∃ c : Fin k → ℝ,
        ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ f ∧
          {x : U | (x : M) ∈ S} = f ⁻¹' {c} ∧
          ∀ x : U, (x : M) ∈ S → Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) f x) := sorry

end Set

end DefiningMaps
