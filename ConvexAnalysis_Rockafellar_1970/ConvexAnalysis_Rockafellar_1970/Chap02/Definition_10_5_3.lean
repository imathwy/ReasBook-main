import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 10.5.3 names the family-level condition that one nonnegative
  Lipschitz constant works uniformly for every member of a family on a subset `S`.
- `core/canonical`: the intrinsic owner abstraction is the set-level predicate
  `Set.EquiLipschitzOn F S := ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S`, independent of any
  indexing model.
- `bridge/view`: the chapter indexed owner is the thin bridge
  `EquiLipschitzOn f S := Set.EquiLipschitzOn (Set.range f) S`; the bundled `UniformFun` view is
  a derived bridge via `UniformFun.lipschitzOnWith_ofFun_iff`; then `LipschitzOnWith` gives the
  canonical emetric inequality bridge,
  `lipschitzOnWith_iff_dist_le_mul` gives the metric inequality bridge, and
  `dist_eq_norm` gives the norm specialization.

Domain-style sampling used here:
- `LipschitzOnWith`;
- `lipschitzOnWith_iff_dist_le_mul`;
- `UniformFun.lipschitzOnWith_ofFun_iff`;
- `dist_eq_norm`;

Primitive data vs derived API:
- primitive data: a single `α : NNReal` and one family-set owner
  `∀ g ∈ F, LipschitzOnWith α g S`;
- derived API: the indexed-family bridge through `Set.range`, the bundled `UniformFun` bridge,
  and the emetric/metric/norm inequality reformulations, plus uniform-equicontinuity
  consequences.

Layer target: `source-facing`, with `EquiLipschitzOn` as the chapter vocabulary for the family
notion built on the intrinsic set owner, with indexed and bundled formulations provided as thin
bridges.
-/

/-- Intrinsic owner for equi-Lipschitz families on `S`: one nonnegative constant works for every
member of a function family set `F`. -/
def Set.EquiLipschitzOn (F : Set (X → Y)) (S : Set X) : Prop :=
  ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S

/-- Primitive-owner unfolding of `Set.EquiLipschitzOn`. -/
theorem Set.equiLipschitzOn_iff_exists_forall_lipschitzOnWith
    {F : Set (X → Y)} {S : Set X} :
    F.EquiLipschitzOn S ↔ ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S :=
  Iff.rfl

/-- Intrinsic bundled bridge: the set-owner `F.EquiLipschitzOn S` is equivalent to one
`LipschitzOnWith` witness for the canonical subtype-indexed bundled family. -/
theorem Set.equiLipschitzOn_iff_exists_lipschitzOnWith_uniformFun
    {F : Set (X → Y)} {S : Set X} :
    F.EquiLipschitzOn S ↔
      ∃ α : NNReal,
        LipschitzOnWith α (fun x ↦ UniformFun.ofFun (fun g : F ↦ (g : X → Y) x)) S := by
  rw [Set.equiLipschitzOn_iff_exists_forall_lipschitzOnWith]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, (UniformFun.lipschitzOnWith_ofFun_iff).2 ?_⟩
    intro g
    exact hα g g.2
  · rintro ⟨α, hα⟩
    have hα' :
        ∀ g : F, LipschitzOnWith α (fun x ↦ (g : X → Y) x) S :=
      (UniformFun.lipschitzOnWith_ofFun_iff).1 hα
    refine ⟨α, ?_⟩
    intro g hg
    exact hα' ⟨g, hg⟩

/-- Definition 10.5.3: a family of functions on a subset `S` is equi-Lipschitzian relative to `S`
if one nonnegative Lipschitz constant works uniformly for every member of the family on `S`. -/
def EquiLipschitzOn (f : ι → X → Y) (S : Set X) : Prop :=
  (Set.range f).EquiLipschitzOn S

/-- The source-facing family predicate `EquiLipschitzOn f S` is exactly the existence of one
common nonnegative Lipschitz constant for all coordinate functions `f i` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_lipschitzOnWith
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, LipschitzOnWith α (f i) S := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, fun i ↦ hα (f i) ⟨i, rfl⟩⟩
  · rintro ⟨α, hα⟩
    exact ⟨α, fun g hg ↦ by
      rcases hg with ⟨i, rfl⟩
      exact hα i⟩

/-- The source-facing owner `EquiLipschitzOn f S` is equivalent to the bundled `UniformFun`
Lipschitz owner for a `Type`-indexed family. -/
theorem equiLipschitzOn_iff_exists_lipschitzOnWith_uniformFun
    {ι' : Type u} (f : ι' → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal,
        LipschitzOnWith α (fun x ↦ UniformFun.ofFun (fun i : ι' ↦ f i x)) S := by
  rw [equiLipschitzOn_iff_exists_forall_lipschitzOnWith]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, (UniformFun.lipschitzOnWith_ofFun_iff).2 ?_⟩
    intro i
    simpa using hα i
  · rintro ⟨α, hα⟩
    have hα' : ∀ i : ι', LipschitzOnWith α (fun x ↦ f i x) S :=
      (UniformFun.lipschitzOnWith_ofFun_iff).1 hα
    refine ⟨α, ?_⟩
    intro i
    simpa using hα' i

/-- Owner-style bridge: from `hf : EquiLipschitzOn f S`, extract one common coordinatewise
Lipschitz witness for all members of the family on `S`. -/
theorem EquiLipschitzOn.exists_forall_lipschitzOnWith
    {f : ι → X → Y} {S : Set X} (hf : EquiLipschitzOn f S) :
    ∃ α : NNReal, ∀ i, LipschitzOnWith α (f i) S :=
  (equiLipschitzOn_iff_exists_forall_lipschitzOnWith f S).1 hf

section Core

-- Proof sketch: unfold `EquiLipschitzOn` and each coordinate `LipschitzOnWith` owner.
/-- Canonical emetric bridge for Definition 10.5.3: a family is equi-Lipschitz on `S` iff one
nonnegative constant controls all coordinatewise extended metric differences
`edist (f i x) (f i y) ≤ α * edist x y` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_edist_le_mul
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, edist (f i x) (f i y) ≤ α * edist x y := by
  simp [equiLipschitzOn_iff_exists_forall_lipschitzOnWith, LipschitzOnWith]

end Core

section Metric

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

-- Proof sketch: unfold `EquiLipschitzOn` and rewrite each coordinate owner with
-- `lipschitzOnWith_iff_dist_le_mul`.
/-- Canonical metric bridge for Definition 10.5.3: a family is equi-Lipschitz on `S` iff one
nonnegative constant controls all coordinatewise metric differences
`dist (f i x) (f i y) ≤ α * dist x y` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_dist_le_mul
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, dist (f i x) (f i y) ≤ α * dist x y := by
  simp [equiLipschitzOn_iff_exists_forall_lipschitzOnWith, lipschitzOnWith_iff_dist_le_mul]

end Metric

section Normed

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the metric bridge and rewrite distances by norms.
/-- Normed-group specialization of the canonical metric bridge: a family is equi-Lipschitz on `S`
iff one nonnegative constant bounds every coordinatewise norm difference
`‖f_i x - f_i y‖` by `α ‖x - y‖` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_norm_sub_le
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, ‖f i x - f i y‖ ≤ α * ‖x - y‖ := by
  simpa [dist_eq_norm] using
    (equiLipschitzOn_iff_exists_forall_dist_le_mul (f := f) (S := S))

end Normed

end
