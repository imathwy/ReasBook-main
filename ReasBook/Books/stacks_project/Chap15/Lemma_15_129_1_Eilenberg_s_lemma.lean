import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommMonoid Q] [Module R Q]
variable {F : Type x} [AddCommMonoid F] [Module R F] [Module.Free R F]

/- Domain sampling:
- primary domain: infinitely generated free modules and absorption of direct summands;
- owner abstractions inspected upstream: `Module.Projective.iff_split`, `Module.Projective.of_split`,
  `LinearMap.inl`/`LinearMap.fst`, and `LinearEquiv.prodCongr`;
- source-facing layer: the complement-based hypothesis `(P × Q) ≃ₗ[R] F`;
- core/canonical layer: the retract data `i : P →ₗ[R] F`, `s : F →ₗ[R] P` with `s.comp i = id`;
- bridge/view below: recover that retract canonically from the given product equivalence. -/

/-- Canonical split-data form of Eilenberg absorption: a direct summand of a non-finitely generated
free module is absorbed by that free module. -/
theorem nonfinitely_generated_free_absorption_of_split
    (hF : ¬ Module.Finite R F) (i : P →ₗ[R] F) (s : F →ₗ[R] P)
    (hs : s.comp i = LinearMap.id) :
    Nonempty ((P × F) ≃ₗ[R] F) := sorry

-- Proof sketch: extract the canonical retract `P ↪ F ↠ P` from the chosen equivalence
-- `(P × Q) ≃ₗ[R] F`, then apply the split-data form above.
/-- Lemma 15.129.1 (Eilenberg's lemma): if `F` is a free `R`-module that is not finitely
generated and `P ⊕ Q ≅ F`, then `P ⊕ F ≅ F`; in Lean, the binary direct sums are modeled by the
product modules `P × Q` and `P × F`. -/
theorem prod_nonfinitely_generated_free_absorption
    (hF : ¬ Module.Finite R F) (e : (P × Q) ≃ₗ[R] F) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  let i : P →ₗ[R] F := e.toLinearMap ∘ₗ LinearMap.inl R P Q
  let s : F →ₗ[R] P := LinearMap.fst R P Q ∘ₗ e.symm.toLinearMap
  have hs : s.comp i = LinearMap.id := by
    ext p
    simp [i, s]
  simpa [i, s] using nonfinitely_generated_free_absorption_of_split hF i s hs

end
