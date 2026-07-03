import Mathlib
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_11_3_1 (from Chap11) -/
universe u

section

open Module (End toModuleEnd)

variable {A : Type u} [Ring A] [IsSimpleRing A]

/-- Lemma 11.3.1: if `A` is a simple ring and `M` is a nonzero right ideal of `A`, then the
canonical right-multiplication map from `Aᵐᵒᵖ` to the bicommutant
`End (End Aᵐᵒᵖ M) M` is bijective. In owner-abstraction form this is the canonical
map `toModuleEnd`, while the textbook `Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M` is the
same action viewed as an algebra homomorphism. -/
-- Proof sketch: injectivity comes from simplicity of `A`, since a nonzero right ideal makes the
-- bicommutant nontrivial. For surjectivity, show that the image is a nonzero right ideal in the
-- bicommutant and then use the simplicity argument from the textbook to force it to be all of the
-- bicommutant.
theorem rightIdeal_bicommutant_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _) := sorry

/-- Companion bridge: the textbook `ℤ`-algebra form of Lemma 11.3.1 is the same canonical map. -/
theorem rightIdeal_bicommutant_lsmul_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →ₐ[ℤ] _) := by
  simpa using rightIdeal_bicommutant_bijective M hM

/-- Owner abstraction underlying Lemma 11.3.1: the bicommutant of a nonzero right ideal of a
simple ring recovers the original opposite ring. -/
noncomputable def rightIdeal_double_centralizer (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Aᵐᵒᵖ ≃+* End (End Aᵐᵒᵖ M) M :=
  RingEquiv.ofBijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _)
    (rightIdeal_bicommutant_bijective M hM)

end

/-! ### Lemma_11_3_2 (from Chap11) -/
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

/-! ### Theorem_11_3_3 (from Chap11) -/
/- Domain-style sampling for Theorem 11.3.3:
- primary domain: Artin--Wedderburn theory for simple finite-dimensional algebras;
- sampled owner declarations:
  `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`;
- best owner abstraction: this numbered item is a recall-only `core/canonical` entry, owned by
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`; there is no source-defined extra data
  to package into a local wrapper or bridge;
- primitive data: the ambient assumptions `[Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsSimpleRing A]`;
- derived API: the canonical matrix-over-division-algebra presentation, with the finiteness of the
  division algebra over `k` supplied directly by the owner theorem.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a simple finite-dimensional `k`-algebra is a matrix
  algebra over a finite-dimensional division `k`-algebra;
- `core/canonical`: `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`;
- `bridge/view`: none is needed here, because the source statement is exactly the canonical owner
  theorem in the finite-dimensional algebra setting. -/

section

variable {k A : Type*}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

/- Theorem 11.3.3: a simple finite-dimensional `k`-algebra is `k`-algebra isomorphic to a matrix
algebra `Matrix (Fin n) (Fin n) K` for some positive integer `n` and some skew field `K` over `k`
that is finite over `k`. This is exactly the canonical finite Wedderburn--Artin theorem
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`; in the present context,
`FiniteDimensional k A` supplies the `Module.Finite k A` and `IsArtinianRing A` instances needed
to apply that owner theorem. -/
recall IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite

end
