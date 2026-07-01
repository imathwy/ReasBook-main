import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

open scoped TensorProduct

/- Domain-style sampling for Lemma 10.89.4:
- primary domain: finitely presented modules, filtered-colimit presentations in `ModuleCat`, and
  tensoring a factored map with a fixed module;
- sampled owner declarations:
  `module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented`,
  `module_finitePresentation_iff_isFinitelyPresentable`,
  `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`,
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`;
- best owner abstraction: this lemma is a source-facing factorization statement, but its proof
  should run through the canonical owners `ObjectProperty.ind`, `IsFinitelyPresentable`, and the
  tensor functor `tensorRight` on `ModuleCat`;
- primitive data: the map `f : P →ₗ[R] M`, the finitely presented source `P`, the module `Q`, and
  the tensor element `x` lying in `ker (f.rTensor Q)`;
- derived API: the finitely presented stage `P' : ModuleCat.{w} R` in a filtered presentation of
  `M`, together with the induced factorization through that stage and the eventual vanishing of `x`
  after tensoring.

Source/core/bridge triage:
- `source-facing`: the theorem below, which extracts one finitely presented factorization killing a
  chosen tensor-kernel element;
- `core/canonical`: filtered colimit presentations of `ModuleCat` and finite presentability via
  `IsFinitelyPresentable`;
- `bridge/view`: the mapped colimit presentation under `tensorRight (ModuleCat.of R Q)`.
-/

-- Proof sketch: write `M` as a filtered colimit of finitely presented modules. Since `P` is
-- finitely presented, the map `f` factors through one stage `M_j`. The element `x` then maps to an
-- element of `M_j ⊗[R] Q` that dies in the colimit `M ⊗[R] Q`, so after passing to a later stage
-- `M_{j'}` it already dies there. Take `P' = M_{j'}` and let `f'` be the induced composite.
/-- Lemma 10.89.4: if `x` lies in the kernel of the tensor map induced by `f : P → M`, then `f`
factors through a finitely presented module `P'` in such a way that `x` already lies in the kernel
of the induced map `P ⊗[R] Q → P' ⊗[R] Q`. -/
theorem exists_finitePresentation_factorization_of_mem_ker_rTensor
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    (f : P →ₗ[R] M)
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    {x : P ⊗[R] Q} (hx : x ∈ LinearMap.ker (f.rTensor Q)) :
    ∃ (P' : ModuleCat.{w} R) (_ : Module.FinitePresentation R P')
      (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
        f = g.comp f' ∧ x ∈ LinearMap.ker (f'.rTensor Q) := sorry
