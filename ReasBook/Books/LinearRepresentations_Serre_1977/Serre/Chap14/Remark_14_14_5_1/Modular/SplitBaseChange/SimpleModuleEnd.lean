import Mathlib

/-!
# Endomorphism algebras of simple modules transfer along surjective maps with nilpotent kernel

Let `Φ : A →ₐ[k] R` be a surjective `k`-algebra map with nilpotent kernel `N = ker Φ`.
If every simple `R`-module has `1`-dimensional `k`-endomorphism algebra, then so does every
simple `A`-module.  The proof: the nilpotent ideal `N` annihilates the simple module `S` (else
`N • ⊤ = ⊤` would propagate to `N^m • ⊤ = ⊤`, contradicting `N^m = ⊥`), so the `A`-action
on `S` factors through `A ⧸ N ≃ R`, identifying `S` with a simple `R`-module having the same
`k`-endomorphisms.
-/

noncomputable section
universe u

namespace Serre.SplitBaseChange

/-- Transfer of "every simple module has 1-dimensional endomorphism algebra" along a surjective
`k`-algebra map with nilpotent kernel. If `Φ : A → R` is a surjective `k`-algebra map with
nilpotent kernel and every simple `R`-module has 1-dimensional `k`-endomorphisms (`hR`), then
every simple `A`-module also has 1-dimensional `k`-endomorphisms. -/
theorem finrank_end_eq_one_of_surjective_nilpotent
    {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
    (hR : ∀ (T : Type u) [AddCommGroup T] [Module R T] [Module k T] [IsScalarTower k R T]
            [Module.Finite k T], IsSimpleModule R T → Module.finrank k (Module.End R T) = 1)
    (Φ : A →ₐ[k] R) (hsurj : Function.Surjective Φ)
    (hnil : IsNilpotent (RingHom.ker (Φ : A →+* R)))
    (S : Type u) [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]
    [Module.Finite k S] (hS : IsSimpleModule A S) :
    Module.finrank k (Module.End A S) = 1 := by
  haveI : IsSimpleModule A S := hS
  set N : Ideal A := RingHom.ker (Φ : A →+* R) with hNdef
  -- Step 1: `N` annihilates `S`.
  have hbot_smul : (⊥ : Ideal A) • (⊤ : Submodule A S) = ⊥ := by
    rw [eq_bot_iff]
    refine Submodule.smul_le.mpr (fun r hr n _ => ?_)
    rw [Submodule.mem_bot] at hr
    rw [hr, zero_smul]; exact Submodule.zero_mem _
  have hNtop : N • (⊤ : Submodule A S) = ⊥ := by
    rcases eq_bot_or_eq_top (N • (⊤ : Submodule A S)) with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm⟩ := hnil
      have key : ∀ j : ℕ, N ^ j • (⊤ : Submodule A S) = ⊤ := by
        intro j
        induction j with
        | zero => rw [Submodule.pow_zero, Submodule.one_smul]
        | succ i ih => rw [Submodule.pow_succ, Submodule.mul_smul, h, ih]
      have hmtop := key m
      rw [hm, Ideal.zero_eq_bot, hbot_smul] at hmtop
      exact bot_ne_top hmtop
  have hann : ∀ n ∈ N, ∀ s : S, n • s = 0 := by
    intro n hn s
    have hmem : n • s ∈ N • (⊤ : Submodule A S) :=
      Submodule.smul_mem_smul hn Submodule.mem_top
    rw [hNtop, Submodule.mem_bot] at hmem
    exact hmem
  have htor : Module.IsTorsionBySet A S (N : Set A) := fun s a => hann a.1 a.2 s
  -- Step 2: build the `R`-module structure on `S`.
  letI mq : Module (A ⧸ N) S := htor.module
  let e : (A ⧸ N) ≃ₐ[k] R := Ideal.quotientKerAlgEquivOfSurjective hsurj
  letI mR : Module R S := Module.compHom S (e.symm.toRingEquiv : R →+* (A ⧸ N))
  -- Compatibility of the two actions: `Φ a • s = a • s`.
  have hcompat : ∀ (a : A) (s : S), (Φ a) • s = a • s := by
    intro a s
    have h2 : (e.symm.toRingEquiv : R →+* (A ⧸ N)) (Φ a) = Ideal.Quotient.mk N a := by
      have h3 : e (Ideal.Quotient.mk N a) = Φ a := rfl
      have h4 : (e.symm.toRingEquiv : R →+* (A ⧸ N)) (Φ a) = e.symm (Φ a) := rfl
      rw [h4, ← h3, e.symm_apply_apply]
    have h1 : (Φ a) • s = (e.symm.toRingEquiv : R →+* (A ⧸ N)) (Φ a) • s := rfl
    rw [h1, h2]
    exact Module.IsTorsionBySet.mk_smul htor a s
  -- Step 3: scalar tower, simplicity, and endomorphism comparison.
  have halg : ∀ (c : k) (s : S), (algebraMap k R c) • s = c • s := by
    intro c s
    rw [← Φ.commutes c, hcompat (algebraMap k A c) s, algebraMap_smul]
  letI tower : IsScalarTower k R S :=
    ⟨fun c r s => by rw [Algebra.smul_def, mul_smul, halg]⟩
  haveI hrs : RingHomSurjective (Φ : A →+* R) := ⟨hsurj⟩
  have hSimpleR : IsSimpleModule R S := by
    let l : S →ₛₗ[(Φ : A →+* R)] S :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun a s => (hcompat a s).symm }
    exact (LinearMap.isSimpleModule_iff_of_bijective l Function.bijective_id).mp hS
  have hendeq : Module.finrank k (Module.End A S) = Module.finrank k (Module.End R S) := by
    let toR : Module.End A S → Module.End R S := fun f =>
      { toFun := f
        map_add' := f.map_add'
        map_smul' := fun r s => by
          obtain ⟨a, rfl⟩ := hsurj r
          simp only [RingHom.id_apply]
          rw [hcompat a s, LinearMap.map_smul, hcompat a (f s)] }
    let toA : Module.End R S → Module.End A S := fun g =>
      { toFun := g
        map_add' := g.map_add'
        map_smul' := fun a s => by
          simp only [RingHom.id_apply]
          rw [← hcompat a s, LinearMap.map_smul, hcompat a (g s)] }
    let eEnd : Module.End A S ≃ₗ[k] Module.End R S :=
      { toFun := toR
        map_add' := fun f g => by ext s; rfl
        map_smul' := fun c f => by ext s; rfl
        invFun := toA
        left_inv := fun f => by ext s; rfl
        right_inv := fun g => by ext s; rfl }
    exact eEnd.finrank_eq
  rw [hendeq]
  exact hR S hSimpleR

end Serre.SplitBaseChange
