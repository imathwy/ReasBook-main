import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {ι : Type u} {X : Type v} {Y : Type w}

section EMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-
Source/core/bridge triage:
- `source-facing`: Definition 10.5.4 introduces the notion that a family of functions on a subset
  `S` shares one common `ε`-`δ` modulus on `S`.
- `core/canonical`: mathlib's owner notion for this is `UniformEquicontinuousOn`.
- `bridge/view`: the canonical pseudoemetric `edist` formulation is the primary specialization of
  `UniformEquicontinuousOn`; metric and norm formulations are thin downstream specializations.
- Primitive data vs derived API: the item adds no new owner object beyond the canonical
  uniform-space notion; the displayed `ε`-`δ` condition is a thin source-facing specification view.

Domain-style sampling used here:
- `UniformEquicontinuousOn`;
- `uniformity_basis_edist_le`;
- `Filter.HasBasis.uniformEquicontinuousOn_iff`.

Layer target: `bridge/view`, with `UniformEquicontinuousOn` kept as the main owner-facing recall
and the pseudoemetric `edist` criterion used as the primary bridge surface; metric and norm
formulas are retained as thin downstream specialization companions. In particular, norm-output
specializations are kept first at the primitive mixed layer (domain metric, codomain norm), with
domain norm-difference formulas as downstream companions.
-/

/- Definition 10.5.4: the canonical mathlib notion of a family of functions on `S` being uniformly
equicontinuous relative to `S` is `UniformEquicontinuousOn`. -/
recall UniformEquicontinuousOn

-- Proof sketch: specialize `Filter.HasBasis.uniformEquicontinuousOn_iff` to the closed-ball
-- pseudoemetric bases on the canonical subtype-indexed family `((↑) : F → X → Y)`.
/-- Intrinsic owner bridge (set-family layer): `F.UniformEquicontinuousOn S` is equivalent to one
common `ε`-`δ` modulus on subtype points `x y : S`, uniformly for all `g ∈ F`. -/
theorem Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype
    {F : Set (X → Y)} {S : Set X} :
    F.UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ g ∈ F, edist (g x) (g y) ≤ ε := by
  have hX := uniformity_basis_edist_le.inf_principal (S ×ˢ S)
  rw [Set.UniformEquicontinuousOn]
  rw [Filter.HasBasis.uniformEquicontinuousOn_iff hX uniformity_basis_edist_le]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    exact hF x y ⟨hxy, x.2, y.2⟩ ⟨g, hg⟩
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g
    rcases g with ⟨g, hg⟩
    rcases hxy with ⟨hxy, hx, hy⟩
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy g hg

/-- Textbook ambient owner bridge (set-family layer): `F.UniformEquicontinuousOn S` is equivalent
to one common `ε`-`δ` modulus with ambient hypotheses `x ∈ S`, `y ∈ S`, uniformly for all
`g ∈ F`. -/
theorem Set.uniformEquicontinuousOn_iff_forall_edist_le
    {F : Set (X → Y)} {S : Set X} :
    F.UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ δ → ∀ g ∈ F, edist (g x) (g y) ≤ ε := by
  rw [Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy g hg
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy g hg
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    exact hF x x.2 y y.2 hxy g hg

-- Proof sketch: pass through the intrinsic set-owner theorem on `Set.range F` and reindex via
-- `uniformEquicontinuousOn_iff_range`.
/-- Intrinsic pseudoemetric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus on subtype points `x y : S`. -/
theorem UniformEquicontinuousOn.iff_forall_edist_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε := by
  rw [uniformEquicontinuousOn_iff_range]
  change (Set.range F).UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε
  rw [Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype (F := Set.range F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x y hxy (F i) ⟨i, rfl⟩
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    rcases hg with ⟨i, rfl⟩
    exact hF x y hxy i

/-- Textbook ambient pseudoemetric bridge: uniform equicontinuity on `S` is equivalent to one
common `ε`-`δ` modulus written with hypotheses `x ∈ S` and `y ∈ S`. -/
theorem UniformEquicontinuousOn.iff_forall_edist_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε := by
  rw [UniformEquicontinuousOn.iff_forall_edist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy i
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x x.2 y y.2 hxy i

end EMetric

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

-- Proof sketch: specialize the owner theorem
-- `Filter.HasBasis.uniformEquicontinuousOn_iff` to the closed-ball metric bases
-- `Metric.uniformity_basis_dist_le` on both the domain and codomain. This yields the relative
-- metric `ε`-`δ` criterion directly.
/-- Intrinsic metric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus on subtype points `x y : S`. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, dist x y ≤ δ → ∀ i, dist (F i x) (F i y) ≤ ε := by
  have hX := Metric.uniformity_basis_dist_le.inf_principal (S ×ˢ S)
  rw [Filter.HasBasis.uniformEquicontinuousOn_iff hX Metric.uniformity_basis_dist_le]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x y ⟨hxy, x.2, y.2⟩ i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    rcases hxy with ⟨hxy, hx, hy⟩
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i

/-- Textbook ambient metric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus written with hypotheses `x ∈ S` and `y ∈ S`. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ → ∀ i, dist (F i x) (F i y) ≤ ε := by
  rw [UniformEquicontinuousOn.iff_forall_dist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy i
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x x.2 y y.2 hxy i

end Metric

section NormCodomain

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the metric bridge and rewrite codomain distances as norm
-- differences in the additive codomain.
/-- Intrinsic mixed bridge: with a metric domain and seminormed additive codomain, uniform
equicontinuity on `S` is equivalent to one common `ε`-`δ` modulus on subtype points `x y : S`,
measured by `dist` in the domain and `‖· - ·‖` in the codomain. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, dist x y ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le_subtype (F := F) (S := S))

/-- Ambient mixed bridge companion: with a metric domain and seminormed additive codomain, uniform
equicontinuity on `S` is equivalent to one common `ε`-`δ` modulus written with hypotheses
`x ∈ S` and `y ∈ S`, measured by `dist` in the domain and `‖· - ·‖` in the codomain. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le (F := F) (S := S))

end NormCodomain

section NormValued

variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the mixed metric/norm bridge
-- `UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le` by rewriting domain distances as
-- norm differences.
/-- For families between seminormed additive commutative groups, the metric
criterion with codomain norm differences specializes to the full norm-difference `ε`-`δ`
criterion on both domain and codomain. -/
theorem UniformEquicontinuousOn.iff_forall_norm_sub_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le (F := F) (S := S))

end NormValued

end
