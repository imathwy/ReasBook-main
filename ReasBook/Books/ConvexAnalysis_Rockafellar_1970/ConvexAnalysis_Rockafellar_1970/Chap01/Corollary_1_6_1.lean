import ConvexAnalysis_Rockafellar_1970.Chap01.AffineDimension
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open AffineSubspace
open scoped AffineSubspace

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 1.6.1 says that affine subspaces with the same affine dimension are
  related by an ambient affine automorphism.
- `core/canonical`: the owner abstractions are `AffineSubspace.affineDim`, `AffineBasis`,
  `AffineIndependent`, and `AffineEquiv`.
- `bridge/view`: the theorem below is the source-facing bridge from equal affine dimensions to the
  ambient transport theorem `AffineIndependent.exists_affineEquiv_of_finite`.
- Layer target: `source-facing`, but stated on the owner affine-space abstraction rather than the
  concrete coordinate model `ℝ^n`; specializing to `EuclideanSpace ℝ (Fin n)` recovers the
  textbook statement unchanged.
- Primitive data vs derived API: the affine subspaces and their affine dimensions are primitive;
  the ambient affine automorphism is derived theorem-level API and should not be repackaged.
- Domain-style sampling used here: `AffineSubspace.affineDim`,
  `AffineBasis.exists_affineBasis_of_finiteDimensional`,
  `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`, and
  `AffineIndependent.exists_affineEquiv_of_finite`.
-/

section AffineSpace

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace AffineSubspace

/-- Source-facing owner for ambient affine-equivalence of affine subspaces. -/
abbrev IsAffineEquivalent (M₁ M₂ : AffineSubspace 𝕜 P) : Prop :=
  ∃ T : P ≃ᵃ[𝕜] P, M₁.map T = M₂

-- Source-facing relation notation: `M₁ ≈ᵃ M₂` means that an ambient affine automorphism of `P`
-- maps `M₁` onto `M₂`.
scoped[AffineSubspace] notation:50 M₁ " ≈ᵃ " M₂ =>
  AffineSubspace.IsAffineEquivalent M₁ M₂

/-- Internal bridge theorem: two nonempty affine subspaces with finite-dimensional directions and
equal direction `finrank` are related by an ambient affine automorphism. -/
private theorem exists_map_eq_of_ne_bot_of_finrank_direction_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥)
    (hfinrank : Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction) :
    M₁ ≈ᵃ M₂ := by
  classical
  letI : Nonempty M₁ := ((nonempty_iff_ne_bot M₁).2 hM₁).to_subtype
  letI : Nonempty M₂ := ((nonempty_iff_ne_bot M₂).2 hM₂).to_subtype
  let ι := Fin (Module.finrank 𝕜 M₁.direction + 1)
  have hι₁ : Fintype.card ι = Module.finrank 𝕜 M₁.direction + 1 := by
    simp [ι]
  have hι₂ : Fintype.card ι = Module.finrank 𝕜 M₂.direction + 1 := by
    simp [ι, hfinrank]
  obtain ⟨B₁⟩ : Nonempty (AffineBasis ι 𝕜 M₁) :=
    AffineBasis.exists_affineBasis_of_finiteDimensional hι₁
  obtain ⟨B₂⟩ : Nonempty (AffineBasis ι 𝕜 M₂) :=
    AffineBasis.exists_affineBasis_of_finiteDimensional hι₂
  let b₁ : ι → P := M₁.subtype ∘ B₁
  let b₂ : ι → P := M₂.subtype ∘ B₂
  have hb₁ : AffineIndependent 𝕜 b₁ :=
    B₁.ind.map' M₁.subtype M₁.subtype_injective
  have hb₂ : AffineIndependent 𝕜 b₂ :=
    B₂.ind.map' M₂.subtype M₂.subtype_injective
  have hle₁ : affineSpan 𝕜 (Set.range b₁) ≤ M₁ := by
    rw [affineSpan_le]
    rintro _ ⟨i, rfl⟩
    exact (B₁ i).property
  have hle₂ : affineSpan 𝕜 (Set.range b₂) ≤ M₂ := by
    rw [affineSpan_le]
    rintro _ ⟨i, rfl⟩
    exact (B₂ i).property
  have hspan₁ : affineSpan 𝕜 (Set.range b₁) = M₁ := by
    exact hb₁.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle₁ hι₁
  have hspan₂ : affineSpan 𝕜 (Set.range b₂) = M₂ := by
    exact hb₂.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle₂ hι₂
  obtain ⟨T, hT⟩ := AffineIndependent.exists_affineEquiv_of_finite hb₁ hb₂
  refine ⟨T, ?_⟩
  calc
    M₁.map T = (affineSpan 𝕜 (Set.range b₁)).map T := by
      rw [hspan₁]
    _ = affineSpan 𝕜 (T.toAffineMap '' Set.range b₁) := by
      rw [AffineSubspace.map_span]
    _ = affineSpan 𝕜 (Set.range b₂) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simpa using (hT i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b₁ i, ⟨i, rfl⟩, hT i⟩
    _ = M₂ := hspan₂

/-- Corollary 1.6.1, stated at the affine-space owner level: if two affine subspaces have the
same affine dimension, then an ambient affine automorphism maps one onto the other. Specializing
to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
-- Corollary bridge: equal affine dimensions imply equal direction `finrank` in the nonempty case,
-- then apply `exists_map_eq_of_ne_bot_of_finrank_direction_eq`.
theorem exists_map_eq_of_affineDim_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (hdim : M₁.affineDim = M₂.affineDim) :
    M₁ ≈ᵃ M₂ := by
  by_cases hM₁ : M₁ = ⊥
  · have hM₂ : M₂ = ⊥ := by
      by_contra hM₂
      rw [affineDim, if_pos hM₁, affineDim, if_neg hM₂] at hdim
      omega
    refine ⟨AffineEquiv.refl 𝕜 P, ?_⟩
    simp [hM₁, hM₂]
  · have hM₂ : M₂ ≠ ⊥ := by
      intro hM₂
      rw [affineDim, if_neg hM₁, affineDim, if_pos hM₂] at hdim
      omega
    have hfinrank :
        Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction := by
      rw [affineDim, if_neg hM₁, affineDim, if_neg hM₂] at hdim
      exact Int.ofNat.inj hdim
    exact exists_map_eq_of_ne_bot_of_finrank_direction_eq M₁ M₂ hM₁ hM₂ hfinrank

/-- Affine dimension is invariant under affine equivalences. -/
theorem affineDim_map_eq {V₂ : Type*} {P₂ : Type*}
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    (M : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 M.direction]
    (T : P ≃ᵃ[𝕜] P₂) :
    ((M.map T : AffineSubspace 𝕜 P₂)).affineDim = M.affineDim := by
  by_cases hM : M = ⊥
  · subst hM
    have hmap : ((⊥ : AffineSubspace 𝕜 P).map T : AffineSubspace 𝕜 P₂) = ⊥ := by
      simp
    rw [affineDim, if_pos hmap, affineDim, if_pos rfl]
  · have hmap : (M.map T : AffineSubspace 𝕜 P₂) ≠ ⊥ := by
      intro hbot
      exact hM ((AffineSubspace.map_eq_bot_iff (s := M) (f := (T : P →ᵃ[𝕜] P₂))).1 hbot)
    have hfinrank :
        Module.finrank 𝕜 (M.map T : AffineSubspace 𝕜 P₂).direction =
          Module.finrank 𝕜 M.direction := by
      rw [AffineSubspace.map_direction]
      simpa using (LinearEquiv.finrank_eq (T.linear.submoduleMap M.direction)).symm
    rw [affineDim, if_neg hmap, affineDim, if_neg hM]
    exact_mod_cast hfinrank

/-- If one affine subspace is the image of another under an ambient affine automorphism, then they
have the same affine dimension. -/
theorem affineDim_eq_of_exists_map_eq {M₁ M₂ : AffineSubspace 𝕜 P}
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction]
    (h : M₁ ≈ᵃ M₂) :
    M₁.affineDim = M₂.affineDim := by
  rcases h with ⟨T, hT⟩
  simpa [hT] using (affineDim_map_eq (M := M₁) T).symm

/-- Classification at the owner layer: two affine subspaces are related by an ambient affine
automorphism exactly when their affine dimensions are equal. -/
theorem exists_map_eq_iff_affineDim_eq
    (M₁ M₂ : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 M₁.direction] [FiniteDimensional 𝕜 M₂.direction] :
    (M₁ ≈ᵃ M₂) ↔ M₁.affineDim = M₂.affineDim := by
  constructor
  · exact affineDim_eq_of_exists_map_eq
  · exact exists_map_eq_of_affineDim_eq M₁ M₂

end AffineSubspace

end AffineSpace
