import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

universe u v w

-- `UCompactlyGeneratedSpace.isClosed` uses compact Hausdorff test spaces. The source-facing
-- predicate below is stronger, since it tests pullbacks along maps from arbitrary compact spaces;
-- using bundled continuous maps keeps that bridge to the canonical `CompHaus` API direct.

/-- Definition 5.1.7: A subset `A` of `X` is compactly closed if `g ⁻¹' A` is closed in `K`
for every continuous map `g : K → X` from a compact space `K`. -/
def IsCompactlyClosed {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ ⦃K : Type v⦄ [TopologicalSpace K] [CompactSpace K], ∀ g : C(K, X), IsClosed (g ⁻¹' A)

/-- A compactly closed subset pulls back to a closed subset along any continuous map from a compact
space. -/
theorem IsCompactlyClosed.isClosed_preimage {X : Type u} [TopologicalSpace X] {A : Set X}
    (hA : IsCompactlyClosed.{u, v} A) {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (g : K → X) (hg : Continuous g) : IsClosed (g ⁻¹' A) :=
  hA ⟨g, hg⟩

/-- Every closed subset is compactly closed. -/
theorem IsClosed.isCompactlyClosed {X : Type u} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : IsCompactlyClosed.{u, v} A :=
  fun {_} _ _ g ↦ IsClosed.preimage g.continuous hA

/-- The preimage of a compactly closed subset along a continuous map is compactly closed. -/
theorem IsCompactlyClosed.preimage {X : Type u} [TopologicalSpace X] {A : Set X}
    (hA : IsCompactlyClosed.{u, w} A) {Y : Type v} [TopologicalSpace Y]
    {f : Y → X} (hf : Continuous f) : IsCompactlyClosed.{v, w} (f ⁻¹' A) := by
  intro K _ _ g
  simpa [Set.preimage_comp] using hA.isClosed_preimage (f ∘ g) (hf.comp g.continuous)

/-- In a `UCompactlyGeneratedSpace.{v}`, every compactly closed subset is closed. -/
theorem IsCompactlyClosed.isClosed {X : Type u} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{v} X]
    {A : Set X} (hA : IsCompactlyClosed.{u, v} A) : IsClosed A := by
  exact UCompactlyGeneratedSpace.isClosed fun K g ↦ hA g

/-- In a `UCompactlyGeneratedSpace.{v}`, compactly closed subsets are exactly the closed subsets. -/
theorem isCompactlyClosed_iff_isClosed {X : Type u} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{v} X] {A : Set X} :
    IsCompactlyClosed.{u, v} A ↔ IsClosed A :=
  ⟨IsCompactlyClosed.isClosed, IsClosed.isCompactlyClosed⟩
