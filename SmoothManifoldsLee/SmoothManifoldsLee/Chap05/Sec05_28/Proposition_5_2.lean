import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (∞ : ℕ∞ω) M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J (∞ : ℕ∞ω) N]

/-- A charted-space structure on `Set.range F` is adapted to `F` if it makes the image into a
smooth manifold for which the subtype inclusion is a smooth embedding and `F` becomes a
diffeomorphism onto its image. -/
def IsInducedImageManifoldStructure (F : N → M) (cs : ChartedSpace H' (Set.range F)) : Prop :=
  let _ : ChartedSpace H' (Set.range F) := cs
  ∃ (_im : IsManifold J (∞ : ℕ∞ω) (Set.range F)),
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := _im
    Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : Set.range F → M) ∧
      ∃ Φ : N ≃ₘ⟮J, J⟯ Set.range F, ∀ x, (Φ x : M) = F x

/-- Proposition 5.2: the image of a smooth embedding inherits a smooth manifold structure with the
subspace topology for which the subtype inclusion is a smooth embedding and the original map is a
diffeomorphism onto its image. -/
-- Proof sketch: the topological embedding part of `hF` gives a homeomorphism
-- `N ≃ₜ Set.range F`; transport the charted-space and smooth-manifold structures of `N` across
-- this homeomorphism. Under the transported structure, the induced map `N → Set.range F` is a
-- diffeomorphism by construction, and composing it with `Subtype.val` recovers `F`, so the
-- subtype inclusion is a smooth embedding.
theorem smooth_embedding_range_has_induced_manifold_structure {F : N → M}
    (hF : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) F) :
    ∃ cs : ChartedSpace H' (Set.range F),
      @IsInducedImageManifoldStructure 𝕜 _ E _ _ H _ M _ _ I E' _ _ H' _ J N _ _ F cs := sorry

/-- Two diffeomorphisms from `N` onto the same image manifold structure that both realize `F` agree
pointwise, hence are equal. -/
-- Proof sketch: for each `x : N`, the equalities in `M` force the corresponding points of
-- `Set.range F` to coincide because `Subtype.val` is injective. Then apply extensionality for
-- diffeomorphisms.
theorem image_diffeomorph_eq_of_comp_subtype_val {F : N → M}
    [ChartedSpace H' (Set.range F)] [IsManifold J (∞ : ℕ∞ω) (Set.range F)]
    {Φ Ψ : N ≃ₘ⟮J, J⟯ Set.range F}
    (hΦ : ∀ x, (Φ x : M) = F x) (hΨ : ∀ x, (Ψ x : M) = F x) :
    Φ = Ψ := sorry

end
