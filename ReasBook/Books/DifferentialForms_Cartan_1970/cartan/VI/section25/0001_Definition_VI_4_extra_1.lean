import Mathlib
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0006_Definition_VI_1_extra_4»

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the owner/API choice was verified directly against mathlib's `OpenPartialHomeomorph` atlas
-- infrastructure, `ChartedSpace`, and `HasGroupoid` files, together with the chapter's upstream
-- owner `OpenPartialHomeomorph.IsHolomorphicIsoOn` for holomorphic coordinate changes. The
-- textbook item here is still at the atlas layer, so this file keeps the covering family explicit
-- instead of introducing a public `ChartedSpace` owner that would require a noncanonical choice
-- of preferred chart.

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Manifold
open Set

variable (X : Type u) [TopologicalSpace X]

/-- Definition VI.4-extra-1: complex-atlas data of complex dimension `1` on a topological space
`X` is an open cover by local coordinates `zᵢ : Uᵢ → Aᵢ ⊆ ℂ`, represented here by open partial
homeomorphisms `X ⇿ ℂ`, such that every transition map `zᵢ ∘ zⱼ⁻¹` is holomorphic with
holomorphic inverse on its natural domain. Hausdorffness is imposed later at the
`ComplexManifold` owner. -/
structure ComplexManifoldAtlas where
  /-- The index type of the chosen open cover by coordinate charts. -/
  Index : Type v
  /-- The local coordinate chart attached to an index. -/
  chart : Index → OpenPartialHomeomorph X ℂ
  /-- The chart sources form an open cover of the underlying space. -/
  cover : ∀ x : X, ∃ i : Index, x ∈ (chart i).source
  /-- Each coordinate change map `zᵢ ∘ zⱼ⁻¹` is a holomorphic isomorphism of open subsets of `ℂ`
  on its natural source and target. -/
  holomorphic_transition (i j : Index) :
    ((chart j).symm ≫ₕ chart i).IsHolomorphicIsoOn
      (((chart j).symm ≫ₕ chart i).source) (((chart j).symm ≫ₕ chart i).target)
