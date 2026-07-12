import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain triage:
- primary domain: simple modules over Artinian rings and finite-dimensional algebras, together
  with Schur's lemma for endomorphism rings of simple modules;
- sampled owner API: `IsSimpleModule`, `IsSimpleModule.toSpanSingleton_surjective`,
  `isArtinian_of_fg_of_artinian`, `IsArtinianRing.of_finite`, and `Module.End.instDivisionRing`;
- best owner abstraction: `IsSimpleModule A M` is the core owner notion, while the Artinian-ring
  and finite-dimensional-algebra statements in this file are bridge theorems producing or using
  simple modules;
- primitive data: the ring/module structures plus the Artinian or finite-dimensional hypotheses;
- derived API: existence of simple submodules, finite-dimensionality of simple modules over a
  finite-dimensional algebra, and the division-ring structure on `Module.End A M`.
- source/core/bridge split:
  `source-facing`: the Stacks-project existence and finiteness statements;
  `core/canonical`: `IsSimpleModule A M` and `Module.End.instDivisionRing`;
  `bridge/view`: `IsArtinianRing.of_finite` and the Artinian-ring existence theorem below.
-/

section

variable {A : Type v} [Ring A] [IsArtinianRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]

-- Proof sketch: for a nonzero `m`, the cyclic submodule `A ∙ m` is finitely generated and hence
-- Artinian; a nonzero Artinian module has a minimal nonzero submodule, which is simple.
/-- Owner theorem: every nonzero module over an Artinian ring contains a simple submodule. -/
theorem artinian_ring_exists_simple_submodule [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let N : Submodule A M := A ∙ m
  have hN_ne : N ≠ ⊥ := by
    intro hN
    exact hm <| by
      simpa [N, hN] using (Submodule.mem_span_singleton_self m : m ∈ A ∙ m)
  letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN_ne
  letI : IsArtinian A N := isArtinian_of_fg_of_artinian N (Submodule.fg_span_singleton m)
  let s : Set (Submodule A N) := {S | S ≠ ⊥}
  have hs : s.Nonempty := ⟨⊤, by simp [s]⟩
  obtain ⟨S, hS, hmin⟩ := IsArtinian.set_has_minimal s hs
  have hsimple : IsSimpleModule A S := by
    rw [isSimpleModule_iff_isAtom]
    refine (isAtom_iff_le_of_ge).2 ⟨hS, ?_⟩
    intro P hP hPS
    by_contra hSP
    have hPS_ne : P ≠ S := by
      intro hEq
      subst hEq
      exact hSP le_rfl
    exact (hmin P (by simpa [s] using hP) (lt_of_le_of_ne hPS hPS_ne)).elim
  refine ⟨S.map N.subtype, ?_⟩
  letI : IsSimpleModule A S := hsimple
  exact IsSimpleModule.congr (S.equivMapOfInjective _ N.subtype_injective).symm

end

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
variable {M : Type w} [AddCommGroup M] [Module A M]

-- Proof sketch: `FiniteDimensional k A` makes `A` an Artinian ring, so this is the Artinian-ring
-- owner theorem above.
/-- Lemma 11.3.2 (2): every nonzero `A`-module contains a simple `A`-submodule when `A` is finite
over `k`. -/
@[stacks 0746]
theorem finite_algebra_exists_simple_submodule
    (k : Type u) [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {M : Type w} [AddCommGroup M] [Module A M] [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact artinian_ring_exists_simple_submodule

-- Proof sketch: specialize the previous finite-algebra theorem to the regular module `A`.
/-- Lemma 11.3.2 (1): if the finite `k`-algebra `A` is nonzero, then the regular left
`A`-module contains a simple submodule. This is the regular-module specialization of the
Artinian-ring owner theorem. -/
@[stacks 0746]
theorem finite_algebra_exists_simple_submodule_regular
    (k : Type u) [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Nontrivial A] :
    ∃ N : Submodule A A, IsSimpleModule A N := by
  have h : ∃ N : Submodule A A, IsSimpleModule A N := finite_algebra_exists_simple_submodule k
  exact h

-- Proof sketch: A simple `A`-module is finitely generated over `A`, and restriction of scalars
-- along the finite `k`-algebra `A` preserves finite generation, yielding finite-dimensionality
-- over `k`.
/-- Lemma 11.3.2 (3): a simple module over a finite `k`-algebra is finite dimensional over `k`. -/
@[stacks 0746]
theorem finite_algebra_simple_module_finite_dimensional [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] : FiniteDimensional k M := by
  letI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  letI : Module.Finite A M :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton A M m)
      (IsSimpleModule.toSpanSingleton_surjective A hm)
  exact Module.Finite.trans A M

end

section

variable {A : Type v} [Ring A]
variable {M : Type w} [AddCommGroup M] [Module A M] [IsSimpleModule A M]

/- Lemma 11.3.2 (4): Schur's lemma gives the endomorphism ring `Module.End A M` of a simple
`A`-module the canonical mathlib `DivisionRing` structure, i.e. it is a skew field. -/
recall Module.End.instDivisionRing

end
