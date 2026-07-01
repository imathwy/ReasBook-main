import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Module

universe u v

section

variable {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [Module K V]

namespace LinearMap

/-- Helper for Exercise 1.4.29: an endomorphism sends its range to itself. -/
lemma mapsTo_range (f : Module.End K V) : ∀ x ∈ f.range, f x ∈ f.range := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨f y, rfl⟩

/-- Helper for Exercise 1.4.29: the endomorphism induced by `f` on `Im(f)`. -/
def restrictRange (f : Module.End K V) : Module.End K f.range :=
  f.restrict (mapsTo_range f)

/-- Helper for Exercise 1.4.29: surjectivity on `Im(f)` is exactly the condition
`Im(f) = Im(f²)`. -/
lemma range_restrict_range_eq_top_iff_range_eq_range_sq (f : Module.End K V) :
    (restrictRange f).range = ⊤ ↔ f.range = (f ∘ₗ f).range := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro hsurj
    apply le_antisymm
    · intro x hx
      -- Pull `x ∈ Im(f)` back through the induced map to write it as `f (f z)`.
      rcases hsurj ⟨x, hx⟩ with ⟨y, hy⟩
      rcases y.property with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa [restrictRange, hz] using congrArg Subtype.val hy
    · intro x hx
      -- Every element of `Im(f²)` already lies in `Im(f)`.
      rcases hx with ⟨y, rfl⟩
      exact ⟨f y, rfl⟩
  · intro h y
    -- Rewrite membership in `Im(f)` using the assumed equality with `Im(f²)`.
    have hy : y.1 ∈ (f ∘ₗ f).range := by
      rw [← h]
      exact y.property
    rcases hy with ⟨x, hx⟩
    refine ⟨⟨f x, ⟨x, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [restrictRange] using hx

/-- Helper for Exercise 1.4.29: injectivity on `Im(f)` is exactly the disjointness of
`Im(f)` and `Ker(f)`. -/
lemma ker_restrict_range_eq_bot_iff_disjoint (f : Module.End K V) :
    (restrictRange f).ker = ⊥ ↔ Disjoint f.range f.ker := by
  constructor
  · intro hker
    rw [Submodule.disjoint_def]
    intro x hxrange hxker'
    -- View a vector in `Im(f) ∩ Ker(f)` as an element of the kernel of the restricted map.
    have hx : (⟨x, hxrange⟩ : f.range) ∈ (restrictRange f).ker := by
      rw [LinearMap.mem_ker]
      ext
      simpa [restrictRange, LinearMap.mem_ker] using hxker'
    have hxbot : (⟨x, hxrange⟩ : f.range) ∈ (⊥ : Submodule K f.range) := by
      simpa [hker] using hx
    simpa using hxbot
  · intro hdisj
    rw [Submodule.eq_bot_iff]
    intro x hx
    -- Disjointness forces a vector in the kernel of the restricted map to vanish.
    have hxker : x.1 ∈ f.ker := by
      rw [LinearMap.mem_ker]
      exact congrArg Subtype.val ((LinearMap.mem_ker.mp hx))
    have hzero : x.1 = 0 := (Submodule.disjoint_def.mp hdisj) x.1 x.property hxker
    simpa using hzero

-- Proof sketch: use rank-nullity for `f` and for the restriction of `f` to `LinearMap.range f`.
-- The condition `LinearMap.range f = LinearMap.range (f ∘ₗ f)` identifies the kernel of that
-- restriction with `LinearMap.range f ⊓ LinearMap.ker f`, and finite-dimensionality turns the
-- resulting dimension equality into the complement relation.
/-- Exercise 1.4.29 (1): for a finite-dimensional vector space, the decomposition
`V = Im(f) ⊕ Ker(f)` is equivalent to the stabilization `Im(f) = Im(f²)`. -/
theorem isCompl_range_ker_iff_range_eq_range_sq [FiniteDimensional K V]
    (f : Module.End K V) :
    IsCompl f.range f.ker ↔ f.range = (f ∘ₗ f).range := by
  constructor
  · intro hcompl
    -- A complementary decomposition makes the induced map on `Im(f)` injective.
    have hker : (restrictRange f).ker = ⊥ :=
      (ker_restrict_range_eq_bot_iff_disjoint f).2 hcompl.disjoint
    have hinj : Function.Injective (restrictRange f) := (LinearMap.ker_eq_bot).1 hker
    have hsurj : Function.Surjective (restrictRange f) :=
      (LinearMap.injective_iff_surjective).1 hinj
    exact (range_restrict_range_eq_top_iff_range_eq_range_sq f).1
      ((LinearMap.range_eq_top).2 hsurj)
  · intro hsq
    -- In finite dimension, surjectivity on `Im(f)` upgrades back to injectivity.
    have hsurj : Function.Surjective (restrictRange f) :=
      (LinearMap.range_eq_top).1
        ((range_restrict_range_eq_top_iff_range_eq_range_sq f).2 hsq)
    have hinj : Function.Injective (restrictRange f) :=
      (LinearMap.injective_iff_surjective).2 hsurj
    have hdisj : Disjoint f.range f.ker :=
      (ker_restrict_range_eq_bot_iff_disjoint f).1 ((LinearMap.ker_eq_bot).2 hinj)
    have hdim : finrank K V ≤ finrank K f.range + finrank K f.ker := by
      exact le_of_eq (LinearMap.finrank_range_add_finrank_ker f).symm
    exact (Submodule.isCompl_iff_disjoint f.range f.ker hdim).2 hdisj

/-- Helper for Exercise 1.4.29: the left shift on `ℕ →₀ K` is surjective. -/
lemma succ_lcomap_surjective :
    Function.Surjective
      (Finsupp.lcomapDomain Nat.succ Nat.succ_injective : (ℕ →₀ K) →ₗ[K] (ℕ →₀ K)) := by
  exact (Finsupp.leftInverse_lcomapDomain_mapDomain
    Nat.succ Nat.succ_injective).surjective

/-- Helper for Exercise 1.4.29: the left shift on `ℕ →₀ K` has nontrivial kernel. -/
lemma succ_lcomap_ker_ne_bot :
    (Finsupp.lcomapDomain Nat.succ Nat.succ_injective : (ℕ →₀ K) →ₗ[K] (ℕ →₀ K)).ker ≠ ⊥ := by
  intro hker
  -- The basis vector at `0` is killed because `0` is not in the image of `Nat.succ`.
  have hs : Finsupp.single 0 (1 : K) ∈
      (Finsupp.lcomapDomain Nat.succ Nat.succ_injective : (ℕ →₀ K) →ₗ[K] (ℕ →₀ K)).ker := by
    rw [LinearMap.mem_ker]
    ext n
    simp [Finsupp.lcomapDomain_apply]
  have hsbot : Finsupp.single 0 (1 : K) ∈ (⊥ : Submodule K (ℕ →₀ K)) := by
    rwa [hker] at hs
  have hzero : Finsupp.single 0 (1 : K) = 0 := hsbot
  exact one_ne_zero (Finsupp.single_eq_zero.mp hzero)

-- Proof sketch: take the left-shift endomorphism on the infinite-dimensional space `ℕ →₀ K`.
-- It is surjective, so `Im(f) = Im(f²) = ⊤`, but its kernel is nontrivial, so the range and
-- kernel are not complementary.
/-- Exercise 1.4.29 (2): the equivalence above fails in infinite dimension; a counterexample
exists on the infinite-dimensional space `ℕ →₀ K`. -/
theorem exists_range_eq_range_sq_not_isCompl_range_ker :
    ∃ f : Module.End K (ℕ →₀ K),
      f.range = (f ∘ₗ f).range ∧ ¬ IsCompl f.range f.ker := by
  classical
  let shift : Module.End K (ℕ →₀ K) := Finsupp.lcomapDomain Nat.succ Nat.succ_injective
  refine ⟨shift, ?_, ?_⟩
  · -- Surjectivity forces both `Im(shift)` and `Im(shift²)` to be all of `ℕ →₀ K`.
    have hrange : shift.range = ⊤ := by
      exact LinearMap.range_eq_top_of_surjective shift succ_lcomap_surjective
    have hrange_sq : (shift ∘ₗ shift).range = ⊤ := by
      have hsurj_sq : Function.Surjective (shift ∘ₗ shift) :=
        succ_lcomap_surjective.comp succ_lcomap_surjective
      exact LinearMap.range_eq_top_of_surjective (shift ∘ₗ shift) hsurj_sq
    rw [hrange, hrange_sq]
  · intro hcompl
    -- If the range were complementary to the kernel, the kernel would have to be trivial.
    have hrange : shift.range = ⊤ := by
      exact LinearMap.range_eq_top_of_surjective shift succ_lcomap_surjective
    have hdisj : Disjoint (⊤ : Submodule K (ℕ →₀ K)) shift.ker := by
      simpa [hrange] using hcompl.disjoint
    have hker : shift.ker = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact (Submodule.disjoint_def.mp hdisj) x (by simp) hx
    exact succ_lcomap_ker_ne_bot (K := K) hker

end LinearMap

namespace Submodule

/-- Helper for Exercise 1.4.29: if two finite-dimensional subspaces have dimensions whose sum
exceeds the ambient dimension, then their intersection is nontrivial. -/
lemma inf_ne_bot_of_finrank_add_gt [FiniteDimensional K V]
    (W₁ W₂ : Submodule K V)
    (hfinrank : finrank K V < finrank K W₁ + finrank K W₂) :
    W₁ ⊓ W₂ ≠ ⊥ := by
  intro hinf
  -- A trivial intersection would make the two subspaces disjoint, contradicting the finrank bound.
  have hdisj : Disjoint W₁ W₂ := by
    rw [disjoint_iff]
    exact hinf
  have hle : finrank K W₁ + finrank K W₂ ≤ finrank K V :=
    Submodule.finrank_add_finrank_le_of_disjoint hdisj
  exact not_le_of_gt hfinrank hle

-- Proof sketch: if `W₁ ⊓ W₂ = ⊥`, then `W₁` and `W₂` are disjoint, so
-- `Submodule.finrank_add_finrank_le_of_disjoint` bounds
-- `Module.finrank K W₁ + Module.finrank K W₂` by `Module.finrank K V`, contradicting the
-- strict inequality.
/-- Exercise 1.4.29 (3): if two subspaces of a finite-dimensional vector space have dimensions
whose sum is larger than the dimension of the ambient space, then they share a nonzero vector. -/
theorem exists_nonzero_mem_inf_of_finrank_add_gt [FiniteDimensional K V]
    (W₁ W₂ : Submodule K V)
    (hfinrank : finrank K V < finrank K W₁ + finrank K W₂) :
    ∃ v : V, v ≠ 0 ∧ v ∈ W₁ ⊓ W₂ := by
  -- First show that the intersection cannot be `⊥`, then extract a nonzero vector from it.
  have hinf : W₁ ⊓ W₂ ≠ ⊥ := inf_ne_bot_of_finrank_add_gt W₁ W₂ hfinrank
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hinf with ⟨v, hv, hv0⟩
  exact ⟨v, hv0, hv⟩

end Submodule

end
