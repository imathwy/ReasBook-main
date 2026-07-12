import Mathlib

/-!
# A semisimple representation with one-dimensional self-intertwiners is irreducible

This file proves a field-general form of (one half of) Schur's lemma: a finite-dimensional
representation that is *semisimple* and whose space of self-intertwiners is *one-dimensional*
over the base field is *irreducible*.  No algebraic closedness of the base field is required.

The argument is the classical idempotent argument.  Over the group ring `k[G]` the self-
intertwiners of `ρ` form the endomorphism algebra `End_{k[G]} ρ.asModule`, which here is
one-dimensional over `k`, hence every endomorphism is a `k`-scalar multiple of the identity.
If the module were not simple, semisimplicity would produce a complement of a proper non-trivial
submodule, and the associated projection would be an idempotent endomorphism distinct from `0`
and `1` — impossible, since the only idempotent scalars are `0` and `1`.
-/

noncomputable section

universe u

open Module Submodule
open scoped MonoidAlgebra

namespace Representation

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A semisimple module over a ring `R` whose endomorphism algebra is one-dimensional over a
field `k` is simple.

This is the module-theoretic heart of the Schur-type statement below: a one-dimensional
endomorphism algebra forces every endomorphism to be a `k`-scalar multiple of the identity, so
the projection associated to any complement of a submodule is a scalar idempotent, hence `0` or
`1`, hence the submodule is `⊥` or `⊤`. -/
theorem _root_.isSimpleModule_of_isSemisimpleModule_of_finrank_End_eq_one
    {k R M : Type*} [Field k] [Ring R] [AddCommGroup M] [Module R M]
    [Algebra k (Module.End R M)]
    [IsSemisimpleModule R M] [Module.Free k (Module.End R M)]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  -- A one-dimensional algebra is nontrivial, so `1 ≠ 0`.
  haveI hnt : Nontrivial (Module.End R M) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [h]; norm_num)
  have hid : (1 : Module.End R M) ≠ 0 := one_ne_zero
  -- Every endomorphism is a `k`-scalar multiple of the identity.
  have hscalar : ∀ f : Module.End R M, ∃ c : k, f = c • (1 : Module.End R M) := by
    obtain ⟨g₀, hg₀, hspan⟩ := (finrank_eq_one_iff' (K := k) (V := Module.End R M)).mp h
    obtain ⟨a, ha⟩ := hspan 1
    have hane : a ≠ 0 := by
      rintro rfl; rw [zero_smul] at ha; exact hid ha.symm
    intro f
    obtain ⟨c, hc⟩ := hspan f
    refine ⟨c * a⁻¹, ?_⟩
    rw [← hc, ← ha, smul_smul]
    congr 1
    field_simp
  -- The module is nontrivial since the identity is nonzero.
  haveI hntM : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hid (Subsingleton.elim _ _)
  rw [isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  -- Take a complement of `N` and form the associated projection idempotent.
  obtain ⟨N', hc⟩ := exists_isCompl N
  set p : Module.End R M := hc.projection with hp
  obtain ⟨c, hceq⟩ := hscalar p
  have hidem : p * p = p := hc.projection_isIdempotentElem
  rw [hceq] at hidem
  -- The scalar `c` satisfies `c² = c`.
  have hcc : (c * c) • (1 : Module.End R M) = c • (1 : Module.End R M) := by
    rw [← hidem, smul_mul_smul_comm, mul_one]
  have hccz : (c * c - c) • (1 : Module.End R M) = 0 := by
    rw [sub_smul, hcc, sub_self]
  have hsub : c * c - c = 0 := by
    rcases smul_eq_zero.mp hccz with h1 | h2
    · exact h1
    · exact absurd h2 hid
  have hc01 : c = 0 ∨ c = 1 := by
    have hfac : c * (c - 1) = 0 := by ring_nf; linear_combination hsub
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (sub_eq_zero.mp h2)
  rcases hc01 with rfl | rfl
  · -- `c = 0`: the projection is `0`, so `N = range p = ⊥`.
    left
    rw [zero_smul] at hceq
    have hrange : LinearMap.range p = N := hc.projection_range
    rw [hceq] at hrange
    simpa using hrange.symm
  · -- `c = 1`: the projection is the identity, so `N' = ker p = ⊥`, whence `N = ⊤`.
    right
    rw [one_smul] at hceq
    have hker : LinearMap.ker p = N' := hc.projection_ker
    rw [hceq, Module.End.one_eq_id, LinearMap.ker_id] at hker
    have hN' : N' = ⊥ := hker.symm
    subst hN'
    exact eq_top_of_isCompl_bot hc

set_option backward.isDefEq.respectTransparency false in
/-- **Schur-type criterion (field-general).**  A finite-dimensional semisimple representation whose
space of self-intertwiners is one-dimensional over the base field is irreducible.  No algebraic
closedness of `k` is required. -/
theorem isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one
    (ρ : Representation k G V) [FiniteDimensional k V] [IsSemisimpleRepresentation ρ]
    (h : Module.finrank k (Representation.IntertwiningMap ρ ρ) = 1) :
    Representation.IsIrreducible ρ := by
  -- Self-intertwiners are linearly equivalent to `k[G]`-endomorphisms of `ρ.asModule`.
  let e : IntertwiningMap ρ ρ ≃ₗ[k] Module.End k[G] ρ.asModule :=
    (IntertwiningMap.equivAlgEnd ρ).toLinearEquiv
  haveI : Module.Free k (Module.End k[G] ρ.asModule) := Module.Free.of_equiv e
  have hfin : Module.finrank k (Module.End k[G] ρ.asModule) = 1 := by
    rw [← LinearEquiv.finrank_eq e]; exact h
  haveI : IsSemisimpleModule k[G] ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  have hsimple : IsSimpleModule k[G] ρ.asModule :=
    isSimpleModule_of_isSemisimpleModule_of_finrank_End_eq_one
      (k := k) (R := k[G]) (M := ρ.asModule) hfin
  exact (irreducible_iff_isSimpleModule_asModule ρ).mpr hsimple

end Representation
