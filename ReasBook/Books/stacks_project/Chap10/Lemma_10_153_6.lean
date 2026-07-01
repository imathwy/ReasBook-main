import Mathlib
import stacks_project.Chap10.Definition_10_153_1
import stacks_project.Chap10.Lemma_10_153_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-
Domain-style sampling:
- primary domain: strictly henselian local rings, finite-type algebra decompositions, and
  residue-field extensions of finite local factors;
- sampled owner declarations in the chapter/domain:
  `finite_type_algebra_decomposition_henselian_local`,
  `algebraMap_isLocalHom_of_finite_local`,
  `StrictHenselianLocalRing`,
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`;
- best owner abstraction:
  the source-facing decomposition owner is already
  `finite_type_algebra_decomposition_henselian_local`; strict henselianity only adds derived
  residue-field consequences on its finite local factors;
- primitive data:
  the `Fintype`-indexed local finite factor decomposition and the remainder `B`;
- derived API:
  the canonical local-hom instance on each factor, finite-dimensionality of the induced
  residue-field extension, and its purely inseparable refinement over the separably closed residue
  field.

Source/core/bridge triage:
- `source-facing`: the strengthened decomposition theorem below;
- `core/canonical`: `finite_type_algebra_decomposition_henselian_local`,
  `algebraMap_isLocalHom_of_finite_local`, and the canonical residue-field finiteness and
  algebraicity instances;
- `bridge/view`: specializing strict henselianity of `R` to residue-field statements on each finite
  local factor produced by the henselian decomposition.
-/

-- Proof sketch: start from the canonical henselian decomposition of Lemma `10.153.5`. For each
-- finite local factor `A i`, Lemma `10.153.4 (3)` gives that `R → A i` is local, so the induced
-- residue-field extension is finite-dimensional by the canonical residue-field instance. Since
-- `ResidueField R` is separably closed, algebraicity of that extension upgrades it to a purely
-- inseparable extension. The local-hom fact is used only as internal instance scaffolding for the
-- residue-field statements, not as a separate public output. The non-quasi-finite remainder term
-- is exactly the one from the owner decomposition.
/-- Lemma 10.153.6: over a strictly henselian local ring `R`, any finite type `R`-algebra `S`
decomposes as a finite product of local finite `R`-algebras whose residue fields are finite purely
inseparable extensions of `ResidueField R`, together with a remainder on which `R → B` is not
quasi-finite at any prime lying over the maximal ideal of `R`. -/
lemma finite_type_algebra_decomposition_strictly_henselian_local :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      letI : ∀ i, IsLocalHom (algebraMap R (A i)) := fun i ↦
        show IsLocalHom (algebraMap R (A i)) from algebraMap_isLocalHom_of_finite_local
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, FiniteDimensional (ResidueField R) (ResidueField (A i))) ∧
        (∀ i, IsPurelyInseparable (ResidueField R) (ResidueField (A i))) ∧
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal := by
  let decompProp : Prop :=
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal
  have hdecomp : decompProp := finite_type_algebra_decomposition_henselian_local
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, hB⟩ := hdecomp
  letI : Fintype ι := instFintype
  letI : ∀ i, CommRing (A i) := instAComm
  letI : ∀ i, Algebra R (A i) := instAAlg
  letI : ∀ i, IsLocalRing (A i) := instALocal
  letI : ∀ i, Module.Finite R (A i) := instAFinite
  letI : ∀ i, IsLocalHom (algebraMap R (A i)) := fun i ↦
    show IsLocalHom (algebraMap R (A i)) from algebraMap_isLocalHom_of_finite_local
  refine ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, ?_, ?_, hB⟩
  · intro i
    infer_instance
  · intro i
    letI : Algebra.IsAlgebraic (ResidueField R) (ResidueField (A i)) := inferInstance
    infer_instance

end
