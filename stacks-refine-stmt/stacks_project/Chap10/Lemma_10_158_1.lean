import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

/- Domain-style sampling for Lemma 10.158.1:
- primary domain: finitely generated field extensions and the owner predicates
  `FormallyUnramified`, `Unramified`, `FormallyEtale`, and `Etale`;
- sampled owner declarations:
  `Algebra.formallyUnramified_iff`,
  `Algebra.FormallyUnramified.iff_isSeparable`,
  `Algebra.Unramified`,
  `Algebra.Etale.of_formallyUnramified_of_flat`;
- best owner abstraction: `Algebra.FormallyUnramified k K`, since over an essentially finite type
  field extension it canonically recovers separability, finite-dimensionality, and the finite-type
  or finitely presented hypotheses needed for the unramified and étale owners;
- primitive data: only the field extension `K / k` with `[Algebra.EssFiniteType k K]`;
- derived API: the six source-facing clauses of the `List.TFAE`.

Source/core/bridge triage:
- `source-facing`: the six-way TFAE matching the textbook lemma;
- `core/canonical`: the owner predicates above, especially `Algebra.FormallyUnramified k K`;
- `bridge/view`: the Kähler-differential reformulation
  `Algebra.formallyUnramified_iff` and the finite-generation upgrades from the field case.
-/

private theorem finiteDimensional_and_isSeparable_of_formallyUnramified
    [Algebra.FormallyUnramified k K] :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  let _ : FiniteDimensional k K :=
    (Module.Free.chooseBasis k K).finiteDimensional_of_finite
  exact
    ⟨inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).mp inferInstance⟩

/-- Lemma 10.158.1: for a finitely generated field extension `K / k`, the following are
equivalent: `K / k` is a finite separable field extension, `Ω[K⁄k] = 0`, `K` is formally
unramified over `k`, `K` is unramified over `k`, `K` is formally étale over `k`, and `K` is étale
over `k`. In Lean, `Ω[K⁄k] = 0` is expressed as `Subsingleton Ω[K⁄k]`, and finite separability as
`FiniteDimensional k K ∧ Algebra.IsSeparable k K`. -/
theorem finite_separable_field_extension_tfae_subsingleton_kaehler_formallyUnramified_unramified_formallyEtale_etale :
    List.TFAE [
      FiniteDimensional k K ∧ Algebra.IsSeparable k K,
      Subsingleton Ω[K⁄k],
      Algebra.FormallyUnramified k K,
      Algebra.Unramified k K,
      Algebra.FormallyEtale k K,
      Algebra.Etale k K
    ] := by
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨_, _⟩
      exact Algebra.FormallyUnramified.of_isSeparable k K
    · intro _
      exact finiteDimensional_and_isSeparable_of_formallyUnramified
  tfae_have 2 ↔ 3 := (Algebra.formallyUnramified_iff k K).symm
  tfae_have 3 → 4 := by
    intro _
    let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
    let _ : Algebra.FiniteType k K := inferInstance
    exact Algebra.Unramified.mk
  tfae_have 4 → 3 := by
    intro _
    infer_instance
  tfae_have 3 → 6 := by
    intro _
    let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
    let _ : Module.FinitePresentation k K := Module.finitePresentation_of_finite k K
    let _ : Algebra.FinitePresentation k K := Algebra.FinitePresentation.of_finitePresentation k K
    exact Algebra.Etale.of_formallyUnramified_of_flat
  tfae_have 6 → 5 := by
    intro _
    infer_instance
  tfae_have 5 → 3 := by
    intro _
    infer_instance
  tfae_finish

end

end Algebra
