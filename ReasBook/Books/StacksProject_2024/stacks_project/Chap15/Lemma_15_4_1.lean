import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_51_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: commutative algebra, specifically Artin-Rees bounds and exactness of perturbed
  two-term complexes of modules;
- sampled declarations:
  `LinearMap.IsArtinReesBound`,
  `LinearMap.isArtinReesBound_of_preimage_pow_smul_eq`,
  `Ideal.exists_artin_rees_constant_of_exact`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`;
- core/canonical owners: `LinearMap.IsArtinReesBound` for the Artin-Rees clause and
  `Function.Exact` for the exactness clause;
- source-facing layer: the Stacks perturbation lemma for `L ⟶ M ⟶ N`;
- bridge/view layer: the Jacobson/Nakayama upgrade from an `I`-adic correction statement to the
  exactness of the perturbed complex.

Primitive data are the linear maps `f`, `f'`, `g`, `g'`, the owner-level Artin-Rees bounds,
the exactness relation `Function.Exact f g`, and congruence modulo `I ^ (c + 1)`. The perturbed
exactness conclusion is derived API built from those owners, so this file should stay owner-driven
rather than introducing a parallel local package.
-/

/- Source/core/bridge triage for Lemma 15.4.1:
- `source-facing`: the perturbation statements for an exact two-term complex `L ⟶ M ⟶ N`;
- `core/canonical`: `LinearMap.IsArtinReesBound` and `Function.Exact`;
- `bridge/view`: the congruence modulo `I ^ (c + 1)` together with the Jacobson-radical
  upgrade supplied by `surjective_of_quotientMap_surjective_of_le_ring_jacobson`.
-/

section

open scoped Pointwise
open LinearMap

variable {A : Type u} [CommRing A]
variable {L : Type v} [AddCommGroup L] [Module A L]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N]
variable (I : Ideal A) {c : ℕ}
variable {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}

/-- Helper for Lemma 15.4.1: a congruence modulo `I ^ (c + 1)` gives pointwise `I`-adic control
on the difference of two linear maps. -/
lemma congr_mod_pow_apply_mem_pow_smul
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    {u v : P →ₗ[A] Q}
    (huv : LinearMap.range (u - v) ≤ I ^ (c + 1) • (⊤ : Submodule A Q))
    (x : P) :
    (u - v) x ∈ I ^ (c + 1) • (⊤ : Submodule A Q) := by
  -- View the pointwise difference as an element of the range and apply the given containment.
  exact huv ⟨x, rfl⟩

/-- Helper for Lemma 15.4.1: linear maps preserve the standard `I^n`-power submodules. -/
lemma map_mem_pow_smul_top
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (u : P →ₗ[A] Q) {n : ℕ} {x : P}
    (hx : x ∈ I ^ n • (⊤ : Submodule A P)) :
    u x ∈ I ^ n • (⊤ : Submodule A Q) := by
  -- The image lands in `I^n • range u`, which is contained in `I^n • ⊤`.
  have hxmap :
      u x ∈ Submodule.map u (I ^ n • (⊤ : Submodule A P)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Submodule.map_smul'', Submodule.map_top] at hxmap
  exact (Submodule.smul_mono (le_rfl : (I ^ n : Ideal A) ≤ I ^ n)
    (show LinearMap.range u ≤ (⊤ : Submodule A Q) from le_top)) hxmap

/-- Helper for Lemma 15.4.1: the perturbed composite lands in `I ^ (c + 1) N`. -/
lemma perturbed_comp_mem_pow_smul
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (x : L) :
    g' (f' x) ∈ I ^ (c + 1) • (⊤ : Submodule A N) := by
  -- Control the two perturbation terms separately: one comes from `f' - f`, the other from `g' - g`.
  have hffx :
      (f' - f) x ∈ I ^ (c + 1) • (⊤ : Submodule A M) :=
    congr_mod_pow_apply_mem_pow_smul (I := I) (c := c) hff' x
  have hggfx :
      (g' - g) (f x) ∈ I ^ (c + 1) • (⊤ : Submodule A N) :=
    congr_mod_pow_apply_mem_pow_smul (I := I) (c := c) hgg' (f x)
  have hmap :
      g' ((f' - f) x) ∈ I ^ (c + 1) • (⊤ : Submodule A N) :=
    map_mem_pow_smul_top (I := I) g' hffx
  have hcomp : g (f x) = 0 := by
    simpa using LinearMap.congr_fun hexact.linearMap_comp_eq_zero x
  have hsum :
      g' ((f' - f) x) + (g' - g) (f x) ∈ I ^ (c + 1) • (⊤ : Submodule A N) := by
    exact (I ^ (c + 1) • (⊤ : Submodule A N)).add_mem hmap hggfx
  have hrewrite :
      g' (f' x) = g' ((f' - f) x) + (g' - g) (f x) := by
    -- Rewrite the perturbed composite into the two controlled error terms.
    calc
      g' (f' x) = g' ((f' - f) x + f x) := by
        congr 1
        simp [sub_eq_add_neg, add_assoc]
      _ = g' ((f' - f) x) + g' (f x) := by
        rw [LinearMap.map_add]
      _ = g' ((f' - f) x) + ((g' - g) (f x) + g (f x)) := by
        congr 1
        simp [sub_eq_add_neg, add_assoc]
      _ = g' ((f' - f) x) + (g' - g) (f x) := by
        rw [hcomp]
        simp
  rw [hrewrite]
  exact hsum

/-- Helper for Lemma 15.4.1: a congruence modulo `I ^ (c + 1)` gains an extra `I ^ r` factor on
inputs already lying in `I ^ r P`. -/
lemma congr_mod_pow_apply_mem_pow_smul_of_scaled
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    {u v : P →ₗ[A] Q}
    (huv : LinearMap.range (u - v) ≤ I ^ (c + 1) • (⊤ : Submodule A Q))
    {r : ℕ} {x : P}
    (hx : x ∈ I ^ r • (⊤ : Submodule A P)) :
    (u - v) x ∈ I ^ (c + r + 1) • (⊤ : Submodule A Q) := by
  -- First map the `I ^ r`-power submodule across `u - v`, then push the target range control
  -- through the outer scalar action.
  have hxmap :
      (u - v) x ∈ Submodule.map (u - v) (I ^ r • (⊤ : Submodule A P)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Submodule.map_smul'', Submodule.map_top] at hxmap
  have hxpow :
      (u - v) x ∈ I ^ r • (I ^ (c + 1) • (⊤ : Submodule A Q)) := by
    exact (Submodule.smul_mono (le_rfl : (I ^ r : Ideal A) ≤ I ^ r) huv) hxmap
  rw [← Submodule.smul_assoc, Ideal.smul_eq_mul] at hxpow
  have hpow : (I ^ r * I ^ (c + 1) : Ideal A) = I ^ (c + r + 1) := by
    calc
      (I ^ r * I ^ (c + 1) : Ideal A) = I ^ (r + (c + 1)) := by
        rw [← pow_add]
      _ = I ^ (c + r + 1) := by
        simp [Nat.add_assoc, Nat.add_left_comm]
  rw [hpow] at hxpow
  simpa using hxpow

/-- Helper for Lemma 15.4.1: on inputs from `I ^ r L`, the perturbed composite lands in
`I ^ (c + r + 1) N`. -/
lemma scaled_perturbed_comp_mem_pow_smul
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    {r : ℕ} {x : L}
    (hx : x ∈ I ^ r • (⊤ : Submodule A L)) :
    g' (f' x) ∈ I ^ (c + r + 1) • (⊤ : Submodule A N) := by
  -- Package the basic perturbation estimate as a range inclusion and then apply the scaled
  -- congruence lemma to the composite `g' ∘ f'`.
  have hcomp_range :
      LinearMap.range (g'.comp f' - 0) ≤ I ^ (c + 1) • (⊤ : Submodule A N) := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    simpa using perturbed_comp_mem_pow_smul
      (I := I) (c := c) (f := f) (f' := f') (g := g) (g' := g')
      hexact hff' hgg' z
  have hx' :
      (g'.comp f' - 0) x ∈ I ^ (c + r + 1) • (⊤ : Submodule A N) :=
    congr_mod_pow_apply_mem_pow_smul_of_scaled
      (I := I) (c := c) (u := g'.comp f') (v := 0) hcomp_range hx
  simpa using hx'

/-- Helper for Lemma 15.4.1: first isolate the midpoint from the source proof. After comparing
`g a` and `g' a` at level `r + c + 1`, the Artin-Rees bound for `g` produces `a₁ ∈ I^(r+1) M`
such that `a - a₁` lies in `range f ∩ I^r M`. -/
lemma exact_correction_data
    (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    {n r : ℕ} {a : M} (hn : c ≤ n)
    (ha_r : a ∈ I ^ r • (⊤ : Submodule A M))
    (ha_n : a ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)))
    (hr : r < n - c) :
    ∃ a₁ : M,
      a₁ ∈ I ^ (r + 1) • (⊤ : Submodule A M) ∧
        a - a₁ ∈ LinearMap.range f ⊓ I ^ r • (⊤ : Submodule A M) := by
  -- Rewrite the `g'`-preimage condition and lower it from stage `n` to stage `r + c + 1`.
  rw [Submodule.mem_comap] at ha_n
  have hstage_le : r + c + 1 ≤ n := by
    omega
  have hg'a :
      g' a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right hstage_le) le_rfl) ha_n
  -- Compare `g a` and `g' a` using the scaled perturbation estimate for `g' - g`.
  have hpert :
      (g' - g) a ∈ I ^ (c + r + 1) • (⊤ : Submodule A N) :=
    congr_mod_pow_apply_mem_pow_smul_of_scaled
      (I := I) (c := c) (u := g') (v := g) hgg' ha_r
  have hga :
      g a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
    have hsub :
        g' a - (g' - g) a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
      exact (I ^ (r + c + 1) • (⊤ : Submodule A N)).sub_mem hg'a <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpert
    have hrewrite : g' a - (g' - g) a = g a := by
      rw [LinearMap.sub_apply]
      abel
    simpa [hrewrite] using hsub
  -- Apply the Artin-Rees bound for `g` to obtain the midpoint `a₁`.
  have hga_inf :
      g a ∈ LinearMap.range g ⊓ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
    rw [Submodule.mem_inf]
    exact ⟨⟨a, rfl⟩, hga⟩
  have hga_map :
      g a ∈ Submodule.map g (I ^ (r + 1) • (⊤ : Submodule A M)) := by
    simpa [show r + c + 1 - c = r + 1 by omega,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hg (r + c + 1) (by omega) hga_inf
  rcases Submodule.mem_map.mp hga_map with ⟨a₁, ha₁, ha₁_eq⟩
  -- Exactness converts the resulting kernel element into a range element of `f`.
  have hrange : a - a₁ ∈ LinearMap.range f := by
    have hker : a - a₁ ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, LinearMap.map_sub]
      simpa [ha₁_eq]
    rw [hexact.linearMap_ker_eq] at hker
    exact hker
  have ha₁_r : a₁ ∈ I ^ r • (⊤ : Submodule A M) := by
    exact (Submodule.pow_smul_top_le I M (Nat.le_succ r)) ha₁
  have hpow : a - a₁ ∈ I ^ r • (⊤ : Submodule A M) := by
    exact (I ^ r • (⊤ : Submodule A M)).sub_mem ha_r ha₁_r
  refine ⟨a₁, ha₁, ?_⟩
  rw [Submodule.mem_inf]
  exact ⟨hrange, hpow⟩

/-- Helper for Lemma 15.4.1: in the source branch `r < c`, any range witness for the midpoint
already suffices because the raw perturbation term lies in the deeper power `I^(c+1) M`. -/
lemma exact_correction_step_small_r_branch
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    {r : ℕ} {a a₁ : M} (hrc : r < c)
    (ha₁ : a₁ ∈ I ^ (r + 1) • (⊤ : Submodule A M))
    (hmid : a - a₁ ∈ LinearMap.range f ⊓ I ^ r • (⊤ : Submodule A M)) :
    ∃ b : L, f b = a - a₁ ∧ a - f' b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
  -- Use any range witness for `a - a₁`, then absorb the perturbation term by power monotonicity.
  rw [Submodule.mem_inf] at hmid
  rcases hmid.1 with ⟨b, hb⟩
  have herror_c :
      (f' - f) b ∈ I ^ (c + 1) • (⊤ : Submodule A M) :=
    congr_mod_pow_apply_mem_pow_smul (I := I) (c := c) hff' b
  have herror :
      (f' - f) b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
    exact (Submodule.smul_mono
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.le_of_lt hrc))) le_rfl) herror_c
  have hrewrite : a₁ - (f' - f) b = a - f' b := by
    calc
      a₁ - (f' - f) b = a₁ - (f' b - f b) := by rw [LinearMap.sub_apply]
      _ = a₁ - f' b + f b := by abel
      _ = a₁ - f' b + (a - a₁) := by rw [hb]
      _ = a - f' b := by abel
  refine ⟨b, hb, ?_⟩
  rw [← hrewrite]
  exact (I ^ (r + 1) • (⊤ : Submodule A M)).sub_mem ha₁ herror

/-- Helper for Lemma 15.4.1: in the source branch `c ≤ r`, apply the Artin-Rees bound for `f`
to choose the midpoint witness inside `I^(r-c) L`, so the scaled perturbation term lands in
`I^(r+1) M`. -/
lemma exact_correction_step_large_r_branch
    (hf : f.IsArtinReesBound I c)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    {r : ℕ} {a a₁ : M} (hcr : c ≤ r)
    (ha₁ : a₁ ∈ I ^ (r + 1) • (⊤ : Submodule A M))
    (hmid : a - a₁ ∈ LinearMap.range f ⊓ I ^ r • (⊤ : Submodule A M)) :
    ∃ b : L,
      b ∈ I ^ (r - c) • (⊤ : Submodule A L) ∧
        f b = a - a₁ ∧
          a - f' b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
  -- Replace the midpoint witness by one inside `I^(r-c) L`, then use the scaled perturbation
  -- bound for `f' - f`.
  have hmap :
      a - a₁ ∈ Submodule.map f (I ^ (r - c) • (⊤ : Submodule A L)) := by
    simpa using hf r hcr hmid
  rcases Submodule.mem_map.mp hmap with ⟨b, hb_mem, hb⟩
  have herror_scaled :
      (f' - f) b ∈ I ^ (c + (r - c) + 1) • (⊤ : Submodule A M) :=
    congr_mod_pow_apply_mem_pow_smul_of_scaled
      (I := I) (c := c) (u := f') (v := f) hff' hb_mem
  have herror :
      (f' - f) b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
    simpa [show c + (r - c) + 1 = r + 1 by omega,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using herror_scaled
  have hrewrite : a₁ - (f' - f) b = a - f' b := by
    calc
      a₁ - (f' - f) b = a₁ - (f' b - f b) := by rw [LinearMap.sub_apply]
      _ = a₁ - f' b + f b := by abel
      _ = a₁ - f' b + (a - a₁) := by rw [hb]
      _ = a - f' b := by abel
  refine ⟨b, hb_mem, hb, ?_⟩
  rw [← hrewrite]
  exact (I ^ (r + 1) • (⊤ : Submodule A M)).sub_mem ha₁ herror

/-- Helper for Lemma 15.4.1: this is the source-faithful one-step correction on the ambient
`I`-adic filtration of `M`. Starting from `a ∈ I ^ r M` with `g' a ∈ I ^ n N` and `r < n - c`,
one subtracts an explicit `f'`-term to raise the `I`-adic order while keeping the `g'`-image in
`I ^ n N`. -/
lemma exact_correction_step
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hcomplex' : g'.comp f' = 0)
    {n r : ℕ} {a : M} (hn : c ≤ n)
    (ha_r : a ∈ I ^ r • (⊤ : Submodule A M))
    (ha_n : a ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)))
    (hr : r < n - c) :
    ∃ b : L,
      a - f' b ∈ I ^ (r + 1) • (⊤ : Submodule A M) ∧
        a - f' b ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) := by
  -- Route correction: first isolate the midpoint `a = (a - a₁) + a₁`, then follow the textbook
  -- branch split `r < c` versus `c ≤ r` to absorb the perturbation of `f'`.
  rcases exact_correction_data
      (I := I) (c := c) (f := f) (g := g) (g' := g')
      hg hexact hgg' hn ha_r ha_n hr with
    ⟨a₁, ha₁, hmid⟩
  rcases Nat.lt_or_ge r c with hrc | hcr
  · -- In the small branch, the raw `I^(c+1)`-error is already deep enough.
    rcases exact_correction_step_small_r_branch
        (I := I) (c := c) (f := f) (f' := f')
        hff' hrc ha₁ hmid with
      ⟨b, hb, hb_r⟩
    refine ⟨b, hb_r, ?_⟩
    rw [Submodule.mem_comap]
    have ha_g' : g' a ∈ I ^ n • (⊤ : Submodule A N) := by
      simpa [Submodule.mem_comap] using ha_n
    have hcompb : g' (f' b) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomplex' b
    have hmap : g' (a - f' b) = g' a := by
      calc
        g' (a - f' b) = g' a - g' (f' b) := by rw [LinearMap.map_sub]
        _ = g' a := by rw [hcompb, sub_zero]
    simpa [hmap] using ha_g'
  · -- In the large branch, use the Artin-Rees witness for `f` before comparing `f` and `f'`.
    rcases exact_correction_step_large_r_branch
        (I := I) (c := c) (f := f) (f' := f')
        hf hff' hcr ha₁ hmid with
      ⟨b, hb_mem, hb, hb_r⟩
    refine ⟨b, hb_r, ?_⟩
    rw [Submodule.mem_comap]
    have ha_g' : g' a ∈ I ^ n • (⊤ : Submodule A N) := by
      simpa [Submodule.mem_comap] using ha_n
    have hcompb : g' (f' b) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomplex' b
    have hmap : g' (a - f' b) = g' a := by
      calc
        g' (a - f' b) = g' a - g' (f' b) := by rw [LinearMap.map_sub]
        _ = g' a := by rw [hcompb, sub_zero]
    simpa [hmap] using ha_g'

/-- Helper for Lemma 15.4.1: iterating the one-step correction yields the source inclusion
`g'⁻¹(I ^ n N) ⊆ range f' + I ^ (n - c) M`. -/
lemma preimage_pow_le_range_sup_pow_aux
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hcomplex' : g'.comp f' = 0)
    {n r : ℕ} (hn : c ≤ n) {a : M}
    (ha_r : a ∈ I ^ r • (⊤ : Submodule A M))
    (ha_n : a ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)))
    (hr : r ≤ n - c) :
    a ∈ LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) := by
  -- Iterate the source one-step correction on the distance `n - c - r`.
  have hmain :
      ∀ m : ℕ, ∀ {r : ℕ} {a : M},
        n - c - r = m →
          a ∈ I ^ r • (⊤ : Submodule A M) →
            a ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) →
              r ≤ n - c →
                a ∈ LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) := by
    intro m
    induction m with
    | zero =>
        intro r a hm ha_r ha_n hr
        -- When the distance is zero, the remainder already lies in the terminal power.
        have hr_eq : r = n - c := by
          omega
        refine Submodule.mem_sup.2 ⟨0, by simp, a, ?_, ?_⟩
        · simpa [hr_eq] using ha_r
        · simp
    | succ m ihm =>
        intro r a hm ha_r ha_n hr
        -- Otherwise apply one correction step and continue from the raised power index `r + 1`.
        have hlt : r < n - c := by
          omega
        rcases exact_correction_step
            (I := I) (c := c) (f := f) (f' := f') (g := g) (g' := g')
            hf hg hexact hff' hgg' hcomplex' hn ha_r ha_n hlt with
          ⟨b, hb_r, hb_n⟩
        have hm' : n - c - (r + 1) = m := by
          omega
        have hstep :
            a - f' b ∈ LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) :=
          ihm (r := r + 1) (a := a - f' b) hm' hb_r hb_n (by omega)
        rcases Submodule.mem_sup.1 hstep with ⟨u, hu, v, hv, huv⟩
        refine Submodule.mem_sup.2 ⟨f' b + u, ?_, v, hv, ?_⟩
        · exact (LinearMap.range f').add_mem (LinearMap.mem_range_self f' b) hu
        · calc
            f' b + u + v = f' b + (u + v) := by abel
            _ = f' b + (a - f' b) := by rw [huv]
            _ = a := by abel
  exact hmain (n - c - r) rfl ha_r ha_n hr

namespace LinearMap

-- Proof sketch: repeat the textbook adjustment argument. For `a ∈ M` with `g' a ∈ I^n N`, compare
-- `g a` and `g' a` modulo `I^(c+1)`, use the Artin-Rees bound for `g` to replace `a` by
-- `a - f b + f' b`, and use the Artin-Rees bound for `f` to ensure the correction term raises the
-- `I`-adic order by one. Iterating yields the required Artin-Rees bound for `g'`.
/-- Lemma 15.4.1 (1): if `c` is an Artin-Rees bound for `f` and `g`, the complex `L ⟶ M ⟶ N`
is exact, and `f'`, `g'` agree with `f`, `g` modulo `I^(c + 1)`, then `c` is also an
Artin-Rees bound for `g'`. -/
theorem IsArtinReesBound.of_exact_of_congr_mod_pow
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hcomplex' : g'.comp f' = 0) :
    g'.IsArtinReesBound I c := by
  intro n hn y hy
  rcases hy.1 with ⟨a, rfl⟩
  -- Apply the source inclusion to a preimage representative of `y`.
  have ha_zero : a ∈ I ^ 0 • (⊤ : Submodule A M) := by
    simpa using (show a ∈ (⊤ : Submodule A M) from trivial)
  have ha_n : a ∈ Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) := by
    simpa [Submodule.mem_comap] using hy.2
  have ha_decomp :
      a ∈ LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) :=
    preimage_pow_le_range_sup_pow_aux
      (I := I) (c := c) (f := f) (f' := f') (g := g) (g' := g')
      hf hg hexact hff' hgg' hcomplex' hn ha_zero ha_n (by omega)
  rcases Submodule.mem_sup.1 ha_decomp with ⟨u, hu, v, hv, huv⟩
  rcases hu with ⟨b, rfl⟩
  -- The `range f'` summand dies because `S'` is a complex, so only the deep remainder survives.
  have hcomplexb : g' (f' b) = 0 := by
    simpa using LinearMap.congr_fun hcomplex' b
  have hv_map :
      g' v ∈ Submodule.map g' (I ^ (n - c) • (⊤ : Submodule A M)) :=
    Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  simpa [← huv, LinearMap.map_add, hcomplexb] using hv_map

end LinearMap

section

variable [IsNoetherianRing A] [Module.Finite A M]

namespace Function.Exact

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- Helper for Lemma 15.4.1: quotienting by `range f'` kills the correction term and keeps the
deep remainder in the corresponding `I`-power of the quotient. -/
lemma mkQ_mem_pow_of_mem_range_sup_pow
    {r : ℕ} {x : M}
    (hx : x ∈ LinearMap.range f' ⊔ I ^ r • (⊤ : Submodule A M)) :
    (Submodule.mkQ (LinearMap.range f')) x ∈
      I ^ r • (⊤ : Submodule A (M ⧸ LinearMap.range f')) := by
  rcases Submodule.mem_sup.1 hx with ⟨u, hu, v, hv, huv⟩
  rcases hu with ⟨b, rfl⟩
  -- Map the deep remainder into the quotient and use that the quotient kills `range f'`.
  have hv_map :
      Submodule.mkQ (LinearMap.range f') v ∈
        Submodule.map (Submodule.mkQ (LinearMap.range f')) (I ^ r • (⊤ : Submodule A M)) :=
    Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hmap :
      Submodule.map (Submodule.mkQ (LinearMap.range f')) (I ^ r • (⊤ : Submodule A M)) =
        I ^ r • (⊤ : Submodule A (M ⧸ LinearMap.range f')) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [hmap] at hv_map
  have hzero : Submodule.mkQ (LinearMap.range f') (f' b) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f')).2 (LinearMap.mem_range_self f' b)
  simpa [← huv, LinearMap.map_add, hzero] using hv_map

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- Helper for Lemma 15.4.1: after passing to `M / range f'`, a witness-preserving correction
iteration should place the class of every `g'`-cycle inside every power `I ^ r`. -/
lemma ker_class_mem_pow_quotient_of_congr_mod_pow
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hcomplex' : g'.comp f' = 0)
    {x : M} (hx : x ∈ LinearMap.ker g') :
    ∀ r : ℕ,
      (Submodule.mkQ (LinearMap.range f')) x ∈
        I ^ r • (⊤ : Submodule A (M ⧸ LinearMap.range f')) := by
  intro r
  -- Apply the source inclusion at level `n = c + r`; the quotient kills the `range f'` summand.
  have hx_zero : g' x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_top : x ∈ I ^ 0 • (⊤ : Submodule A M) := by
    simpa using (show x ∈ (⊤ : Submodule A M) from trivial)
  have hx_preimage : x ∈ Submodule.comap g' (I ^ (c + r) • (⊤ : Submodule A N)) := by
    rw [Submodule.mem_comap]
    simpa [hx_zero]
  have hx_decomp :
      x ∈ LinearMap.range f' ⊔ I ^ r • (⊤ : Submodule A M) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      preimage_pow_le_range_sup_pow_aux
        (I := I) (c := c) (f := f) (f' := f') (g := g) (g' := g')
        hf hg hexact hff' hgg' hcomplex' (n := c + r) (r := 0)
        (by omega) hx_top hx_preimage (by omega)
  simpa using mkQ_mem_pow_of_mem_range_sup_pow (I := I) (f' := f') hx_decomp

-- Proof sketch: first apply clause `(1)` to obtain the Artin-Rees bound for `g'`. Then for
-- `a ∈ ker g'`, the same adjustment argument shows `a ∈ LinearMap.range f' + I^(n-c) M` for every
-- `n ≥ c`. Intersect over all `n` and use Krull intersection for finite modules together with
-- `I ≤ Ring.jacobson A` to deduce `a ∈ LinearMap.range f'`.
/-- Lemma 15.4.1 (2): if `I` is contained in the Jacobson radical, `S' : L ⟶ M ⟶ N` is a
complex, and `f'`, `g'` agree with an exact complex `S : L ⟶ M ⟶ N` modulo `I^(c + 1)`, then
the perturbed complex `S'` is exact. -/
theorem of_congr_mod_pow_and_artin_rees
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) :
    Exact f' g' := by
  let q : M →ₗ[A] M ⧸ LinearMap.range f' := Submodule.mkQ (LinearMap.range f')
  -- The endgame is the standard quotient argument: show the class of a `ker g'` element lies in
  -- every `I^n`-power of `M / range f'`, then kill it by Krull intersection.
  refine LinearMap.exact_of_comp_of_mem_range hcomplex' ?_
  intro x hx
  have hxpow :
      ∀ n : ℕ, q x ∈ I ^ n • (⊤ : Submodule A (M ⧸ LinearMap.range f')) := by
    intro n
    -- Apply the quotient form of the source inclusion to the cycle `x`.
    simpa [q] using ker_class_mem_pow_quotient_of_congr_mod_pow
      (I := I) (c := c) (f := f) (f' := f') (g := g) (g' := g')
      hf hg hexact hff' hgg' hcomplex' hx n
  have hxbar : q x ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule A (M ⧸ LinearMap.range f')) := by
    -- Assemble the power-by-power statement into membership in the full `I`-adic intersection.
    rw [Submodule.mem_iInf]
    exact hxpow
  have hbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule A (M ⧸ LinearMap.range f'))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I <| by
      rwa [Ideal.jacobson_bot]
  have hxq : q x = 0 := by
    have : q x ∈ (⊥ : Submodule A (M ⧸ LinearMap.range f')) := by
      simpa [hbot] using hxbar
    simpa using this
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f')).mp <| by
    simpa [q] using hxq

end Function.Exact

end

end
