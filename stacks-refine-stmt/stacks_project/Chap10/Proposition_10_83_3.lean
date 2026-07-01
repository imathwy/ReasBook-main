import Mathlib
import stacks_project.Chap10.Theorem_10_95_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: faithfully flat descent for finite projective modules over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
  `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`,
  `module_finite_projective_iff_finitePresentation_and_flat`;
- best owner abstraction: the owner predicates `Module.Finite R M` and `Module.Projective R M`;
- primitive data: the ring map `R → S`, the `R`-module `M`, and the faithfully flat base change;
- derived API: the finite-projective descent proposition below.

Layering:
- this numbered item is `bridge/view`: it packages the two owner descent theorems for finiteness
  and projectivity into the source-facing textbook phrase "finite projective".
-/

-- Proof sketch: finite generation descends by the canonical theorem
-- `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`. For projectivity, finite projective
-- over `S` implies finitely presented and flat after base change; descend finite presentation and
-- flatness separately, then apply the characterization of finite projective modules as finitely
-- presented flat modules.
/-- Proposition 10.83.3: if the faithfully flat base change `S ⊗[R] M` is a finite projective
`S`-module, then `M` is a finite projective `R`-module. This is the canonical Lean form of the
textbook statement for `M ⊗_R S`. -/
theorem finite_projective_of_finite_projective_tensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (hfinite : Module.Finite S (S ⊗[R] M)) (hprojective : Module.Projective S (S ⊗[R] M)) :
    Module.Finite R M ∧ Module.Projective R M := by
  letI : Module.Finite S (S ⊗[R] M) := hfinite
  letI : Module.Projective S (S ⊗[R] M) := hprojective
  let hfinite : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  let hprojective : Module.Projective R M :=
    Module.Projective.of_projective_tensorProduct_of_faithfullyFlat S
  exact ⟨hfinite, hprojective⟩

end
