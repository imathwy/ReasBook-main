import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Domain-style sampling:
- primary domain: faithfully flat descent for finiteness conditions on modules;
- sampled owner declarations of the same kind:
  `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
  `Module.Flat.of_flat_tensorProduct`,
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`;
- best owner abstraction: the predicate `Module.FinitePresentation R M`;
- primitive data: the rings `R`, `S`, the `R`-module `M`, and the faithfully flat base change
  `R → S`;
- derived API: descent lemmas for finiteness predicates after tensor base change.

Layering:
- this numbered item is `core/canonical`: unlike the finite and flat clauses, there is no
  upstream owner theorem for module finite-presentation descent, so the theorem below is the owner
  declaration rather than a bridge or compatibility wrapper.
-/

/- Companion recall: if the base-changed `S`-module `S ⊗[R] M` is finite, then `M` is finite.
This is exactly the canonical faithfully flat descent theorem
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`. -/
recall Module.Finite.of_finite_tensorProduct_of_faithfullyFlat

-- Proof sketch: first descend finite generation of `M` from part (1). Choose a finite free
-- presentation of `M`, identify the kernel after tensoring with `S` using flatness of the faithful
-- base change, use finite presentation of `S ⊗[R] M` to show the base-changed kernel is finite,
-- and then descend that finite generation again via faithfully flat descent.
/-- Lemma 10.83.2: if the base-changed `S`-module `S ⊗[R] M` is finitely presented over `S`,
then `M` is finitely presented over `R`. -/
@[stacks 03C4]
theorem Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  -- First descend finite generation of `M`; this is the textbook part (1).
  letI : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  -- Base change the chosen finite free cover and use finite presentation upstairs to control its
  -- kernel.
  have hπ_base : Function.Surjective (π.baseChange S) := by
    simpa [LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective S hπ
  have hker_base_fg : Submodule.FG (LinearMap.ker (π.baseChange S)) :=
    Module.FinitePresentation.fg_ker (π.baseChange S) hπ_base
  -- Identify the upstairs kernel with the tensor product of the downstairs kernel.
  have hker_tensor_finite : Module.Finite S (S ⊗[R] LinearMap.ker π) := by
    have hker_ltensor_fg :
        Submodule.FG (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S π)) := by
      simpa [LinearMap.baseChange_eq_ltensor] using hker_base_fg
    letI : Module.Finite S (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S π)) :=
      Module.Finite.of_fg hker_ltensor_fg
    let e :
        S ⊗[R] LinearMap.ker π ≃ₗ[S]
          LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S π) :=
      LinearMap.tensorKerEquiv S S π
    exact Module.Finite.equiv e.symm
  -- Descend finite generation of the kernel and conclude from the finite free presentation.
  letI : Module.Finite R (LinearMap.ker π) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.finitePresentation_of_surjective π hπ Submodule.FG.of_finite

/- Companion recall: if the base-changed `S`-module `S ⊗[R] M` is flat over `S`, then `M` is
flat over `R`. This is exactly the canonical faithfully flat descent theorem
`Module.Flat.of_flat_tensorProduct`. -/
recall Module.Flat.of_flat_tensorProduct

end
