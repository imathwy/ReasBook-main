import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [HenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-
Domain-style sampling:
- primary domain: henselian local rings, quasi-finite loci, and finite-type product decompositions;
- sampled owner declarations in the chapter/domain:
  `has_finite_local_ring_product_decomposition`,
  `finite_type_algebra_split_finite_nonQuasiFinite_property`,
  `henselian_local_ring_tfae`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction:
  the canonical owner for the first splitting step is
  `finite_type_algebra_split_finite_nonQuasiFinite_property R`,
  while the actual decomposition object is owned by `AlgEquiv`;
- primitive data:
  a finite type `R`-algebra `S`;
- derived API:
  the finite factor, the non-quasi-finite remainder, and the further finite-product decomposition
  of the finite factor into local finite `R`-algebras; the remainder clause is stated by the
  canonical owner `Algebra.QuasiFiniteAt`.

Source/core/bridge triage:
- `source-facing`: the theorem `finite_type_algebra_decomposition_henselian_local`, which keeps the
  textbook decomposition into explicit local finite factors indexed by a finite type;
- `core/canonical`: `finite_type_algebra_split_finite_nonQuasiFinite_property R`;
- `bridge/view`: the passage from that owner clause to the explicit `Fintype`-indexed product using
  `exists_pi_algEquiv_henselianLocalRing_of_finite`.
-/

-- Proof sketch: first use the canonical owner theorem
-- `henselian_local_ring_tfae` at clause `10` to split `S` as a finite `R`-algebra factor times a
-- remainder with no quasi-finite point over `maximalIdeal R`. Then apply
-- `exists_pi_algEquiv_henselianLocalRing_of_finite` to the finite factor and compose the two
-- `AlgEquiv`s at the same `Fintype`-indexed product level.
/-- Lemma 10.153.5: any finite type algebra over a henselian local ring decomposes as a finite
product of local finite `R`-algebras together with a remainder on which `R → B` is not
quasi-finite at any prime lying over the maximal ideal of `R`. -/
lemma finite_type_algebra_decomposition_henselian_local :
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
            ¬ Algebra.QuasiFiniteAt R q.asIdeal := by
  have hsplit : finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R :=
    ((henselian_local_ring_tfae.{u, v, v, v, v, v, v, v} R).out 0 10 rfl rfl).mp
      (show HenselianLocalRing R from inferInstance)
  obtain ⟨A, _, _, _, B, _, _, ⟨eAB⟩, hB⟩ :=
    hsplit S
  have hAprod :
      ∃ (ι : Type v) (_ : Fintype ι) (A' : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A' i))
        (instAAlg : ∀ i, Algebra R (A' i))
        (instAHenselian : ∀ i, HenselianLocalRing (A' i))
        (instAFinite : ∀ i, Module.Finite R (A' i)),
        letI : ∀ i, CommRing (A' i) := instAComm
        letI : ∀ i, Algebra R (A' i) := instAAlg
        letI : ∀ i, HenselianLocalRing (A' i) := instAHenselian
        letI : ∀ i, Module.Finite R (A' i) := instAFinite
        Nonempty (A ≃ₐ[R] ∀ i, A' i) :=
    exists_pi_algEquiv_henselianLocalRing_of_finite
  obtain ⟨ι, instFintype, A', instAComm, instAAlg, instAHenselian, instAFinite, ⟨eA⟩⟩ :=
    hAprod
  letI : Fintype ι := instFintype
  letI : ∀ i, HenselianLocalRing (A' i) := instAHenselian
  refine ⟨ι, instFintype, A', instAComm, instAAlg, ?_, instAFinite, B,
    inferInstance, inferInstance, ?_⟩
  · intro i
    infer_instance
  · let instAComm' : ∀ i, CommRing (A' i) := instAComm
    let instAAlg' : ∀ i, Algebra R (A' i) := instAAlg
    let instALocal' : ∀ i, IsLocalRing (A' i) := fun i ↦ inferInstance
    let instAFinite' : ∀ i, Module.Finite R (A' i) := instAFinite
    letI : ∀ i, CommRing (A' i) := instAComm'
    letI : ∀ i, Algebra R (A' i) := instAAlg'
    letI : ∀ i, IsLocalRing (A' i) := instALocal'
    letI : ∀ i, Module.Finite R (A' i) := instAFinite'
    refine ⟨eAB.trans <| AlgEquiv.prodCongr eA (AlgEquiv.refl : B ≃ₐ[R] B), ?_⟩
    intro q hq
    exact hB q hq.symm

end
