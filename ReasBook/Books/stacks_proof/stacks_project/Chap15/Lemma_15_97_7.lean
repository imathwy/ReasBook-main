import stacks_proof.stacks_project.Chap15.LinearMapIdentifiesWithProdSubmodules
import stacks_proof.stacks_project.Chap15.Lemma_15_4_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct
universe u v y

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module A N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module A N₂]

namespace LinearMap

/-- Helper for Lemma 15.97.7: if `I + J` lies in an ideal `K`, then each summand already lies in
`K`, and conversely. -/
lemma ideal_sum_le_ker_iff {I J K : Ideal A} :
    I + J ≤ K ↔ I ≤ K ∧ J ≤ K := by
  -- The lattice inequality `I + J ≤ K` is exactly the conjunction of the two summand inequalities.
  simpa [Ideal.add_eq_sup] using (sup_le_iff : I ⊔ J ≤ K ↔ I ≤ K ∧ J ≤ K)

/-- Helper for Lemma 15.97.7: for a chosen retraction `π` of `s`, the image of `s` is a product
submodule exactly when the two cross-coordinate maps on `M` vanish. -/
lemma identifiesWithProdSubmodules_iff_cross_eq_zero_of_retraction
    (s : M →ₗ[A] N₁ × N₂) (π : N₁ × N₂ →ₗ[A] M)
    (hπ : π.comp s = LinearMap.id) :
    s.identifiesWithProdSubmodules ↔
      let a := (LinearMap.fst A N₁ N₂).comp s
      let b := (LinearMap.snd A N₁ N₂).comp s
      let p₁ := (π.comp (LinearMap.inl A N₁ N₂)).comp a
      let p₂ := (π.comp (LinearMap.inr A N₁ N₂)).comp b
      a.comp p₂ = 0 ∧ b.comp p₁ = 0 := by
  let a : M →ₗ[A] N₁ := (LinearMap.fst A N₁ N₂).comp s
  let b : M →ₗ[A] N₂ := (LinearMap.snd A N₁ N₂).comp s
  let p₁ : M →ₗ[A] M := (π.comp (LinearMap.inl A N₁ N₂)).comp a
  let p₂ : M →ₗ[A] M := (π.comp (LinearMap.inr A N₁ N₂)).comp b
  dsimp [a, b, p₁, p₂]
  have hsum : p₁ + p₂ = LinearMap.id := by
    -- The two pieces recover `m` because the chosen retraction inverts `s` on its image.
    ext m
    have hdecomp : (a m, (0 : N₂)) + ((0 : N₁), b m) = s m := by
      ext <;> simp [a, b]
    calc
      (p₁ + p₂) m = π (a m, 0) + π (0, b m) := by
        rfl
      _ = π ((a m, 0) + (0, b m)) := by
        rw [map_add]
      _ = π (s m) := by
        rw [hdecomp]
      _ = m := by
        simpa using LinearMap.congr_fun hπ m
  constructor
  · rintro ⟨P₁, P₂, -, hrange⟩
    constructor
    · -- The first coordinate of `p₂ m` vanishes because `(0, b m)` already lies in the product image.
      apply LinearMap.ext
      intro m
      have hsm : s m ∈ P₁.prod P₂ := by
        rw [← hrange]
        exact ⟨m, rfl⟩
      rw [Submodule.mem_prod] at hsm
      have hpair : (0, b m) ∈ LinearMap.range s := by
        rw [hrange, Submodule.mem_prod]
        exact ⟨by simp, hsm.2⟩
      rcases hpair with ⟨m₂, hm₂⟩
      have hp₂_eq : p₂ m = m₂ := by
        calc
          p₂ m = π (0, b m) := by
            rfl
          _ = π (s m₂) := by
            simpa using congrArg π hm₂.symm
          _ = m₂ := by
            simpa using LinearMap.congr_fun hπ m₂
      have hp₂_image : s (p₂ m) = (0, b m) := by
        simpa [hp₂_eq] using hm₂
      simpa [a] using congrArg Prod.fst hp₂_image
    · -- The second coordinate of `p₁ m` vanishes by the symmetric argument.
      apply LinearMap.ext
      intro m
      have hsm : s m ∈ P₁.prod P₂ := by
        rw [← hrange]
        exact ⟨m, rfl⟩
      rw [Submodule.mem_prod] at hsm
      have hpair : (a m, 0) ∈ LinearMap.range s := by
        rw [hrange, Submodule.mem_prod]
        exact ⟨hsm.1, by simp⟩
      rcases hpair with ⟨m₁, hm₁⟩
      have hp₁_eq : p₁ m = m₁ := by
        calc
          p₁ m = π (a m, 0) := by
            rfl
          _ = π (s m₁) := by
            simpa using congrArg π hm₁.symm
          _ = m₁ := by
            simpa using LinearMap.congr_fun hπ m₁
      have hp₁_image : s (p₁ m) = (a m, 0) := by
        simpa [hp₁_eq] using hm₁
      simpa [b] using congrArg Prod.snd hp₁_image
  · rintro ⟨ha_cross, hb_cross⟩
    have hfst : a.comp p₁ = a := by
      -- Since `p₁ + p₂ = id`, killing the `p₂` branch leaves `a`.
      apply LinearMap.ext
      intro m
      have hzero : a (p₂ m) = 0 := by
        simpa using LinearMap.congr_fun ha_cross m
      calc
        a (p₁ m) = a (p₁ m) + a (p₂ m) := by rw [hzero, add_zero]
        _ = a ((p₁ + p₂) m) := by simp [map_add]
        _ = a m := by simpa [hsum]
    have hsnd : b.comp p₂ = b := by
      -- The same decomposition argument recovers `b` from the `p₂` branch.
      apply LinearMap.ext
      intro m
      have hzero : b (p₁ m) = 0 := by
        simpa using LinearMap.congr_fun hb_cross m
      calc
        b (p₂ m) = b (p₁ m) + b (p₂ m) := by rw [hzero, zero_add]
        _ = b ((p₁ + p₂) m) := by simp [map_add]
        _ = b m := by simpa [hsum]
    have hInjective : Function.Injective s := by
      -- A retraction is a left inverse, so `s` is injective.
      intro m₁ m₂ hsm
      have hπeq : (π.comp s) m₁ = (π.comp s) m₂ := by
        simpa using congrArg π hsm
      simpa [hπ] using hπeq
    refine ⟨LinearMap.range a, LinearMap.range b, hInjective, ?_⟩
    apply le_antisymm
    · -- Every point in the image of `s` has both coordinates in the corresponding ranges.
      intro z hz
      rcases hz with ⟨m, rfl⟩
      rw [Submodule.mem_prod]
      exact ⟨⟨m, rfl⟩, ⟨m, rfl⟩⟩
    · -- Conversely, split the two coordinates and reassemble them with `p₁` and `p₂`.
      rintro z hz
      rcases z with ⟨z₁, z₂⟩
      rw [Submodule.mem_prod] at hz
      rcases hz.1 with ⟨m₁, hm₁⟩
      rcases hz.2 with ⟨m₂, hm₂⟩
      have hp₁_coord : a (p₁ m₁) = z₁ := by
        simpa [hm₁] using LinearMap.congr_fun hfst m₁
      have hp₂_coord : b (p₂ m₂) = z₂ := by
        simpa [hm₂] using LinearMap.congr_fun hsnd m₂
      have ha_cross_m₂ : a (p₂ m₂) = 0 := by
        simpa using LinearMap.congr_fun ha_cross m₂
      have hb_cross_m₁ : b (p₁ m₁) = 0 := by
        simpa using LinearMap.congr_fun hb_cross m₁
      refine ⟨p₁ m₁ + p₂ m₂, ?_⟩
      ext
      · calc
          (s (p₁ m₁ + p₂ m₂)).1 = a (p₁ m₁ + p₂ m₂) := by
            rfl
          _ = a (p₁ m₁) + a (p₂ m₂) := by
            simp [a, map_add]
          _ = z₁ + 0 := by
            rw [hp₁_coord, ha_cross_m₂]
          _ = z₁ := by simp
      · calc
          (s (p₁ m₁ + p₂ m₂)).2 = b (p₁ m₁ + p₂ m₂) := by
            rfl
          _ = b (p₁ m₁) + b (p₂ m₂) := by
            simp [b, map_add]
          _ = 0 + z₂ := by
            rw [hb_cross_m₁, hp₂_coord]
          _ = z₂ := by simp

/-- Helper for Lemma 15.97.7: after distributing tensors across the product target, the
base-changed pair map is the product of the base-changed coordinate maps. -/
lemma baseChange_pairMap_eq_prod_baseChange_coordinates
    (s : M →ₗ[A] N₁ × N₂) (B : Type y) [CommRing B] [Algebra A B] :
    (TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp (s.baseChange B) =
      LinearMap.prod (((LinearMap.fst A N₁ N₂).comp s).baseChange B)
        (((LinearMap.snd A N₁ N₂).comp s).baseChange B) := by
  let a : M →ₗ[A] N₁ := (LinearMap.fst A N₁ N₂).comp s
  let b : M →ₗ[A] N₂ := (LinearMap.snd A N₁ N₂).comp s
  have hs : s = LinearMap.prod a b := by
    -- A map into a product is determined by its two coordinate maps.
    ext m <;> rfl
  -- Base change respects the product decomposition of the original pair map.
  rw [hs]
  simpa [a, b] using (LinearMap.baseChange_prod_eq (A := A) (B := B) a b)

/-- Helper for Lemma 15.97.7: the first coordinate of the tensorized pair map is the base change
of the original first coordinate map. -/
lemma fst_comp_baseChange_pairMap_eq_baseChange_fst_comp
    (s : M →ₗ[A] N₁ × N₂) (B : Type y) [CommRing B] [Algebra A B] :
    (LinearMap.fst B (B ⊗[A] N₁) (B ⊗[A] N₂)).comp
        ((TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp (s.baseChange B)) =
      ((LinearMap.fst A N₁ N₂).comp s).baseChange B := by
  -- Rewrite the tensorized pair map as the product of the tensorized coordinate maps.
  rw [baseChange_pairMap_eq_prod_baseChange_coordinates (A := A) (s := s) (B := B)]
  -- The first projection of a product recovers the first factor.
  ext x
  rfl

/-- Helper for Lemma 15.97.7: the second coordinate of the tensorized pair map is the base change
of the original second coordinate map. -/
lemma snd_comp_baseChange_pairMap_eq_baseChange_snd_comp
    (s : M →ₗ[A] N₁ × N₂) (B : Type y) [CommRing B] [Algebra A B] :
    (LinearMap.snd B (B ⊗[A] N₁) (B ⊗[A] N₂)).comp
        ((TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp (s.baseChange B)) =
      ((LinearMap.snd A N₁ N₂).comp s).baseChange B := by
  -- Rewrite the tensorized pair map as the product of the tensorized coordinate maps.
  rw [baseChange_pairMap_eq_prod_baseChange_coordinates (A := A) (s := s) (B := B)]
  -- The second projection of a product recovers the second factor.
  ext x
  rfl

/-- Helper for Lemma 15.97.7: after base change, the same cross-coordinate criterion applies, and
the cross maps are simply the base changes of the original ones. -/
lemma baseChangeIdentifiesWithProdSubmodules_iff_cross_baseChange_eq_zero_of_retraction
    (s : M →ₗ[A] N₁ × N₂) (π : N₁ × N₂ →ₗ[A] M)
    (hπ : π.comp s = LinearMap.id)
    (B : Type y) [CommRing B] [Algebra A B] :
    s.baseChangeIdentifiesWithProdSubmodules B ↔
      let a := (LinearMap.fst A N₁ N₂).comp s
      let b := (LinearMap.snd A N₁ N₂).comp s
      let p₁ := (π.comp (LinearMap.inl A N₁ N₂)).comp a
      let p₂ := (π.comp (LinearMap.inr A N₁ N₂)).comp b
      (a.comp p₂).baseChange B = 0 ∧ (b.comp p₁).baseChange B = 0 := by
  -- TODO: use `baseChange_pairMap_eq_prod_baseChange_coordinates` plus a pure-tensor calculation
  -- for the retraction `(π.baseChange B).comp (TensorProduct.prodRight ...).symm.toLinearMap` to
  -- identify the tensorized cross maps with `(a.comp p₂).baseChange B` and `(b.comp p₁).baseChange B`.
  sorry

end LinearMap

-- Proof sketch: choose a retraction `π` of `s`, form the induced endomorphisms of `M`
-- corresponding to the two projections `N₁ × N₂ → Nᵢ`, and let `J` be the finitely generated
-- ideal cutting out the locus where these endomorphisms become complementary idempotents. After
-- base change to `B`, the condition `J ≤ ker(algebraMap A B)` is equivalent to the base-changed
-- map identifying `B ⊗[A] M` with a product of submodules of the two ambient summands.
/-- Lemma 15.97.7: for a split injection of a finite projective `A`-module into `N₁ × N₂`, there
exists a finitely generated ideal `J` whose quotient detects exactly when every base change of the
map identifies `M` with a direct sum of submodules of the two base-changed summands. -/
@[stacks 0F80]
theorem exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection
    [Module.Finite A M] [Module.Projective A M]
    (s : M →ₗ[A] N₁ × N₂)
    (hs : IsSplitMono (ModuleCat.ofHom s)) :
    ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type y) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔
          s.baseChangeIdentifiesWithProdSubmodules B := by
  -- Route correction: the workable invariant is the pair of cross-coordinate maps on `M`
  -- attached to a chosen retraction, not the off-diagonal block of an arbitrary ambient projector.
  -- TODO: the statement is mathematically false as written without additional finiteness/projective
  -- hypotheses on `N₁` and `N₂`. A counterexample is the graph map
  -- `A → A × (A ⧸ I), x ↦ (x, x mod I)` for a non-finitely-generated ideal `I`.
  sorry

end
