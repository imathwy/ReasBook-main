import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.81.1: transport the kernel-factorization criterion from
`Fin n → R` to `Fin n →₀ R` along `Finsupp.linearEquivFunOnFinite`. -/
lemma finsupp_kernel_factorization_of_pi_kernel_factorization
    (h :
      ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
        f x = 0 →
          ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
            f = g ∘ₗ h' ∧ h' x = 0) :
    ∀ ⦃n : ℕ⦄ (f : (Fin n →₀ R) →ₗ[R] M) (x : Fin n →₀ R),
      f x = 0 →
        ∃ (m : ℕ) (h' : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ h' x = 0 := by
  intro n f x hx
  let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R := Finsupp.linearEquivFunOnFinite R R (Fin n)
  -- Move the problem to the function model `Fin n → R`, where the hypothesis applies directly.
  obtain ⟨m, h', g, hfactor, hx'⟩ :=
    h (f ∘ₗ e.symm.toLinearMap) (e x) (by simpa [e] using hx)
  use m
  use h' ∘ₗ e.toLinearMap
  use g
  constructor
  · -- Postcompose the transported factorization with `e` to return to the `Finsupp` domain.
    simpa [LinearMap.comp_assoc] using congrArg (fun φ => φ ∘ₗ e.toLinearMap) hfactor
  · simpa [e] using hx'

/-- Helper for Lemma 10.81.1: the `Fin n → R` factorization criterion implies flatness by
transporting it to mathlib's `Finsupp`-based equational criterion. -/
lemma flat_of_pi_kernel_factorization
    (h :
      ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
        f x = 0 →
          ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
            f = g ∘ₗ h' ∧ h' x = 0) :
    Module.Flat R M := by
  have hFinsupp :=
    finsupp_kernel_factorization_of_pi_kernel_factorization (R := R) (M := M) h
  -- After transport, the owner flatness criterion closes the argument.
  exact Module.Flat.of_forall_exists_factorization fun {l} {f} {x} hx ↦ hFinsupp x f hx

/-- Helper for Lemma 10.81.1: clause (3) lets one kill the span of any finite family of kernel
elements by adjoining those generators one at a time. -/
lemma exists_factorization_killing_span_finset
    (h :
      ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R))
        (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
        N ≤ ker f →
          N ≤ ker h' →
          (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h') →
          ∀ x : Fin n → R,
            f x = 0 →
              ∃ (m' : ℕ) (h'' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h'' ∧
                  ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h'') :
    ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (s : Finset (Fin n → R)),
      (∀ x ∈ s, f x = 0) →
        ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ Submodule.span R (s : Set (Fin n → R)) ≤ ker h' := by
  classical
  intro n f s hs
  induction s using Finset.induction with
  | empty =>
      let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R := Finsupp.linearEquivFunOnFinite R R (Fin n)
      -- The empty generating set is handled by the canonical equivalence with the free `Finsupp`.
      use n
      use e.symm.toLinearMap
      use f ∘ₗ e.toLinearMap
      constructor
      · ext x
        simp [e]
      · simpa
  | insert x s hx_not_mem ih =>
      have hs_tail : ∀ y ∈ s, f y = 0 := by
        intro y hy
        exact hs y (Finset.mem_insert_of_mem hy)
      obtain ⟨m, h', g, hfactor, hkill⟩ := ih hs_tail
      have hspan_ker_f : Submodule.span R (s : Set (Fin n → R)) ≤ ker f := by
        rw [hfactor]
        exact hkill.trans (LinearMap.ker_le_ker_comp h' g)
      have hx_zero : f x = 0 := hs x (Finset.mem_insert_self x s)
      -- Refine the current factorization so that it also kills the new generator `x`.
      obtain ⟨m', h'', hsup, g', hfactor'⟩ :=
        h f (Submodule.span R (s : Set (Fin n → R))) h' hspan_ker_f hkill ⟨g, hfactor⟩ x hx_zero
      use m'
      use h''
      use g'
      constructor
      · exact hfactor'
      · -- Rewriting `span (insert x s)` as `span s + Rx` matches the output of clause (3).
        rw [Finset.coe_insert, Submodule.span_insert]
        simpa [Submodule.add_eq_sup, sup_comm] using hsup

-- Proof sketch: clause (1) is the equational criterion `Module.Flat.iff_forall_isTrivialRelation`
-- rewritten for maps out of finite free modules. Clause (2) implies clause (3) by factoring the
-- intermediate map `g` further to kill `h x`. Clause (3) implies clause (4) by induction on a
-- finite set of generators of `N`, adjoining one generator at a time. Clause (4) implies clause
-- (2) by taking `N = ⊥`.
/-- Lemma 10.81.1: for an `R`-module `M`, the following are equivalent: `M` is flat; every kernel
element of a map `R^n → M` can be killed after factoring through some finite free module; a
factorization that kills a submodule `N` can be refined to kill `N + Rx` for any additional kernel
element `x`; and every finitely generated submodule of such a kernel can be killed by a
factorization through a finite free module. -/
theorem flat_tfae_kernel_factorization_criterion :
    List.TFAE
      [ Module.Flat R M,
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
          f x = 0 →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ h x = 0,
        ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R))
          (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
          N ≤ ker f →
            N ≤ ker h →
            (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h) →
            ∀ x : Fin n → R,
              f x = 0 →
                ∃ (m' : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                  N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h' ∧
                    ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h',
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R)),
          N ≤ ker f →
            N.FG →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ N ≤ ker h ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hflat n f x hx
      letI : Module.Flat R M := hflat
      -- The forward direction is the owner equational criterion for finite free modules.
      simpa using
        (Module.Flat.exists_factorization_of_apply_eq_zero_of_free
          (R := R) (M := M) (N := Fin n → R) (f := x) (x := f) hx)
    · intro h
      -- Transport clause (2) to mathlib's `Finsupp` formulation of flatness.
      exact flat_of_pi_kernel_factorization (R := R) (M := M) h
  tfae_have 2 → 3 := by
    intro h n m f N h' hNkerf hNkerh hfactor x hx
    have hFinsupp :=
      finsupp_kernel_factorization_of_pi_kernel_factorization (R := R) (M := M) h
    obtain ⟨g, hg⟩ := hfactor
    -- Factor the intermediate map `g` further so that the image of `x` is also killed.
    obtain ⟨m', h'', g', hg', hhx⟩ :=
      hFinsupp g (h' x) (by simpa [hg, LinearMap.comp_apply] using hx)
    use m'
    use h'' ∘ₗ h'
    constructor
    · -- The new map kills both the old submodule `N` and the extra generator `x`.
      rw [Submodule.add_eq_sup]
      refine sup_le ?_ ?_
      · exact hNkerh.trans (LinearMap.ker_le_ker_comp h' h'')
      · have hxker : x ∈ ker (h'' ∘ₗ h') := by
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hhx
        refine Submodule.span_le.2 ?_
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hxker
    · use g'
      calc
        f = g ∘ₗ h' := hg
        _ = (g' ∘ₗ h'') ∘ₗ h' := by rw [hg']
        _ = g' ∘ₗ (h'' ∘ₗ h') := by rw [LinearMap.comp_assoc]
  tfae_have 3 → 4 := by
    intro h n f N hNkerf hNfg
    classical
    obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hNfg
    let s : Finset (Fin n → R) := hSfinite.toFinset
    have hs_span : Submodule.span R (s : Set (Fin n → R)) = N := by
      simpa [s] using hSspan
    have hs_zero : ∀ x ∈ s, f x = 0 := by
      intro x hx
      have hxN : x ∈ N := by
        rw [← hs_span]
        exact Submodule.subset_span hx
      simpa [LinearMap.mem_ker] using hNkerf hxN
    -- Inductively adjoining generators yields a factorization killing the whole finitely generated
    -- submodule.
    obtain ⟨m, h', g, hfactor, hkill⟩ :=
      exists_factorization_killing_span_finset (R := R) (M := M) h f s hs_zero
    use m
    use h'
    use g
    constructor
    · exact hfactor
    · rw [← hs_span]
      exact hkill
  tfae_have 4 → 2 := by
    intro h n f x hx
    have hxspan : Submodule.span R ({x} : Set (Fin n → R)) ≤ ker f := by
      refine Submodule.span_le.2 ?_
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [LinearMap.mem_ker] using hx
    have hfg : (Submodule.span R ({x} : Set (Fin n → R))).FG := by
      simpa using (Submodule.fg_span_singleton (R := R) x)
    -- Killing the cyclic submodule generated by `x` recovers the one-element criterion.
    obtain ⟨m, h', g, hfactor, hkill⟩ := h f (Submodule.span R ({x} : Set (Fin n → R))) hxspan hfg
    use m
    use h'
    use g
    constructor
    · exact hfactor
    · have hxker : x ∈ ker h' := hkill (Submodule.subset_span (by simp))
      simpa [LinearMap.mem_ker] using hxker
  tfae_finish

end
