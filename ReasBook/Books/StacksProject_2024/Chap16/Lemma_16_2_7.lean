import StacksProject_2024.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-
Domain-style sampling for `Lemma 16.2.7`:
- primary domain: base change for finite-presentation Jacobian witnesses of elementary and strict
  standardness;
- sampled owner API:
  `Algebra.Presentation.baseChange`,
  `Algebra.Presentation.IsElementaryStandardElement`,
  `Algebra.Presentation.IsStrictlyStandardElement`,
  `Algebra.IsStandardSmooth.baseChange`;
- best owner abstraction: the primitive base-change statements live at the presentation level,
  while `Algebra.IsElementaryStandard` and `Algebra.IsStrictlyStandard` are the derived
  existential owner predicates;
- primitive data: a finite presentation `P` and a presentation-level witness
  `P.IsElementaryStandardElement a` or `P.IsStrictlyStandardElement a`;
- derived API: the algebra-level base-change theorems obtained by existentially choosing `P`.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that elementary or strictly standard elements remain so
  after base change;
- `core/canonical`: `Algebra.Presentation.baseChange` together with the owner predicates
  `P.IsElementaryStandardElement a` and `P.IsStrictlyStandardElement a`;
- `bridge/view`: the tensor element `1 ⊗ₜ[R] a` in the base-changed algebra `R' ⊗[R] A`.
-/

namespace Algebra.Presentation

variable {n m : ℕ}

-- Proof sketch: unfold the presentation-level witness from Definition `16.2.3`, apply the
-- canonical base-changed presentation `P.baseChange R'`, and transport the same size `c`, the
-- Jacobian determinant or minor expression, and the tail ideal-membership condition along the ring
-- map `MvPolynomial.map (algebraMap R R')`.
/-- Presentation-level base change of the elementary standard condition. -/
theorem isElementaryStandardElement_baseChange
    (P : Algebra.Presentation R A (Fin n) (Fin m)) {a : A}
    (ha : P.IsElementaryStandardElement a) :
    (baseChange R' P).IsElementaryStandardElement ((1 : R') ⊗ₜ[R] a) :=
  sorry

-- Proof sketch: base change the witnessing presentation `P` and transport the Jacobian-minor
-- expansion termwise through the canonical tensor-product algebra map.
/-- Presentation-level base change of the strictly standard condition. -/
theorem isStrictlyStandardElement_baseChange
    (P : Algebra.Presentation R A (Fin n) (Fin m)) {a : A}
    (ha : P.IsStrictlyStandardElement a) :
    (baseChange R' P).IsStrictlyStandardElement ((1 : R') ⊗ₜ[R] a) := sorry

end Algebra.Presentation

namespace Algebra

-- Proof sketch: choose a witnessing finite presentation from `IsElementaryStandard R a`, apply the
-- presentation-level base-change theorem, and package the resulting witness back into the
-- canonical existential owner predicate.
/-- Lemma 16.2.7: an elementary standard element remains elementary standard after base change. -/
theorem isElementaryStandard_baseChange
    (a : A) (ha : IsElementaryStandard R a) :
    IsElementaryStandard R' ((1 : R') ⊗ₜ[R] a) := by
  rcases ha with ⟨n, m, P, hP⟩
  exact ⟨n, m, Presentation.baseChange R' P,
    Presentation.isElementaryStandardElement_baseChange P hP⟩

-- Proof sketch: the algebra-level strict statement is the derived existential package of the
-- presentation-level base-change theorem for strict standardness.
/-- Lemma 16.2.7: a strictly standard element remains strictly standard after base change. -/
theorem isStrictlyStandard_baseChange
    (a : A) (ha : IsStrictlyStandard R a) :
    IsStrictlyStandard R' ((1 : R') ⊗ₜ[R] a) := by
  rcases ha with ⟨n, m, P, hP⟩
  exact ⟨n, m, Presentation.baseChange R' P,
    Presentation.isStrictlyStandardElement_baseChange P hP⟩

end Algebra

end
