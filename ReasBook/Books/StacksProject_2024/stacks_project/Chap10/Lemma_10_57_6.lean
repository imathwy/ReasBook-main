import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open HomogeneousIdeal

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage:
* source-facing: a homogeneous ideal inside the irrelevant ideal contains a positive-degree
  homogeneous element avoiding finitely many homogeneous prime ideals.
* core/canonical owner: `ProjectiveSpectrum 𝒜`.
* bridge/view: the private theorem works at the owner level, and the public theorem upgrades a
  finite family of homogeneous prime ideals to points of `Proj` by deriving relevance from
  `I ≤ 𝒜₊` and `¬ I ≤ p i`.
-/

/-- Internal owner-level bridge: a homogeneous ideal contains a homogeneous element avoiding
finitely many relevant homogeneous primes as soon as it is not contained in any of them. -/
private theorem exists_isHomogeneousElem_mem_and_avoid
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → ProjectiveSpectrum 𝒜)
    (havoid : ∀ i, ¬ I ≤ (p i).asHomogeneousIdeal) :
    ∃ x ∈ I, SetLike.IsHomogeneousElem 𝒜 x ∧ ∀ i, x ∉ (p i).asHomogeneousIdeal := by
  sorry

/-- Lemma 10.57.6: if a homogeneous ideal `I` is contained in the irrelevant ideal and is not
contained in any of finitely many homogeneous prime ideals, then `I` contains a homogeneous element
of positive degree that avoids all of those prime ideals. -/
theorem exists_pos_degree_mem_avoid_homogeneous_primes
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → HomogeneousIdeal 𝒜)
    (hprime : ∀ i, (p i).toIdeal.IsPrime) (hI_irrelevant : I ≤ 𝒜₊) (havoid : ∀ i, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ ∀ i, x ∉ p i := by
  let q : Fin r → ProjectiveSpectrum 𝒜 := fun i ↦
    ⟨p i, hprime i, fun hpirr ↦ havoid i <| hI_irrelevant.trans hpirr⟩
  obtain ⟨x, hxI, ⟨d, hxd⟩, hxavoid⟩ :=
    exists_isHomogeneousElem_mem_and_avoid 𝒜 I q (fun i ↦ havoid i)
  by_cases hx0 : x = 0
  · refine ⟨x, hxI, 1, zero_lt_one, ?_, hxavoid⟩
    simp [hx0]
  · refine ⟨x, hxI, d, ?_, hxd, hxavoid⟩
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    have hxirr0 : GradedRing.proj 𝒜 0 x = 0 := by
      simpa [mem_irrelevant_iff] using hI_irrelevant hxI
    have hproj0 : GradedRing.proj 𝒜 0 x = x := by
      simpa [GradedRing.proj_apply, hd0] using
        (DirectSum.decompose_of_mem_same 𝒜 (hd0 ▸ hxd))
    exact hx0 <| by
      rw [← hproj0, hxirr0]

end
