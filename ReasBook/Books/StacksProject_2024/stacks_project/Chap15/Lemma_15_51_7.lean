import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_11_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_8
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_10

-- Declarations for this item will be appended below by the statement pipeline.

open RingPairCat
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- Pair henselization exists as the right adjoint supplied by Lemma `15.12.1`. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [P.HasPropertyC] [P.HasPropertyD] [P.HasPropertyE]

/-- Helper for Lemma 15.51.7: if the target algebra is Noetherian, then every fixed fiber over a
prime of the source is Noetherian as well. -/
lemma fiber_isNoetherianRing_of_isNoetherianTarget
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : PrimeSpectrum R) :
    IsNoetherianRing (p.asIdeal.Fiber S) := by
  -- Proof comment: commute the tensor presentation of the fiber so the Noetherian target ring
  -- becomes the base of an essentially finite type algebra.
  let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
  -- Proof comment: the standard tensor commutation equivalence identifies this model with the
  -- canonical fiber ring.
  exact
    isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm

/-- Helper for Lemma 15.51.7: localizing along a pulled-back prime is compatible with a ring
equivalence. -/
noncomputable lemma localizationAtPrime_ringEquiv_of_comap
    {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : PrimeSpectrum S) :
    Localization.AtPrime (Ideal.comap e.toRingHom q.asIdeal) ≃+*
      Localization.AtPrime q.asIdeal := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom (Ideal.comap e.toRingHom q.asIdeal).primeCompl =
        q.asIdeal.primeCompl := by
    -- Proof comment: a ring equivalence transports the complement of a prime ideal exactly.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx hy
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (by simpa using hx)
  -- Proof comment: once the multiplicative sets agree, the universal property of localization
  -- packages the pulled-back and target localizations into a ring equivalence.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (Ideal.comap e.toRingHom q.asIdeal))
      (Localization.AtPrime q.asIdeal) e hPrimeCompl

/-- Helper for Lemma 15.51.7: localizing a finite product at the prime coming from one coordinate
recovers the localization of that chosen coordinate factor. -/
noncomputable lemma localizationAtPrime_comap_eval_ringEquiv
    {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, CommRing (S i)]
    (i : ι) (Q : PrimeSpectrum (S i)) :
    Localization.AtPrime (Ideal.comap (Pi.evalRingHom S i) Q.asIdeal) ≃+*
      Localization.AtPrime Q.asIdeal := by
  -- Proof comment: the evaluation map on a finite product induces a bijection on the relevant
  -- localizations, so the two local rings are canonically isomorphic.
  simpa [PrimeSpectrum.comap_asIdeal] using
    (RingEquiv.ofBijective
      (Localization.AtPrime.mapPiEvalRingHom Q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective Q.asIdeal) :
        Localization.AtPrime (Ideal.comap (Pi.evalRingHom S i) Q.asIdeal) ≃+*
          Localization.AtPrime Q.asIdeal)

/-- Helper for Lemma 15.51.7: after contracting a prime of the pair henselization back to `A`,
the corresponding localization of `A` is still a `P`-ring. -/
lemma contracted_pair_henselization_localization_isPRing
    (hA : IsPRing P A)
    (qh : PrimeSpectrum (henselizationRing (pairOfIdeal I))) :
    IsPRing P
      (Localization.AtPrime
        (PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) qh).asIdeal) := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) qh
  -- Proof comment: reuse the prime-pair criterion for `A` on the contracted prime `p`.
  refine (isPRing_localizationAtPrime_iff (P := P) p).2 ?_
  intro q hqp
  exact hA.satisfiesPPrimePairCondition p q hqp

/-- Helper for Lemma 15.51.7: the maximal ideal `mh` of the pair henselization contracts to the
corresponding prime `p` of `A`. -/
lemma contracted_pair_henselization_comap_eq
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    Ideal.comap (toHenselization (pairOfIdeal I)) mh.asIdeal = p.asIdeal := by
  -- Proof comment: `p` was defined as the prime-theoretic contraction of `mh`.
  rfl

/-- Helper for Lemma 15.51.7: every maximal ideal of the pair henselization contains the
distinguished henselization ideal. -/
lemma pair_henselization_ideal_le_maximal
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    henselizationIdeal (pairOfIdeal I) ≤ mh.asIdeal := by
  have hJac :
      henselizationIdeal (pairOfIdeal I) ≤
        Ring.jacobson (henselizationRing (pairOfIdeal I)) := by
    -- Proof comment: the pair henselization is henselian at its distinguished ideal, so that
    -- ideal lies in the Jacobson radical of the henselization ring.
    exact
      Ideal.le_ring_jacobson_of_henselianRing
        (A := henselizationRing (pairOfIdeal I))
        (I := henselizationIdeal (pairOfIdeal I))
  -- Proof comment: every maximal ideal contains the Jacobson radical.
  exact hJac.trans (Ring.jacobson_le_of_isMaximal mh.asIdeal)

/-- Helper for Lemma 15.51.7: after contracting a maximal ideal `m^h` of the pair henselization
back to `A`, the contracted prime contains the original ideal `I`. -/
lemma ideal_le_contracted_pair_henselization_prime
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    I ≤ p.asIdeal := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  -- Proof comment: first pull back the distinguished henselization ideal along `A → A^h`, then
  -- use that every maximal branch contains that ideal.
  calc
    I ≤ Ideal.comap (toHenselization (pairOfIdeal I))
        (henselizationIdeal (pairOfIdeal I)) := by
          exact henselizationIdeal_le_comap_toHenselization (I := I)
    _ ≤ Ideal.comap (toHenselization (pairOfIdeal I)) mh.asIdeal := by
          exact Ideal.comap_mono (pair_henselization_ideal_le_maximal (I := I) mh)
    _ = p.asIdeal := by
          simpa [p] using contracted_pair_henselization_comap_eq (I := I) mh

/-- Helper for Lemma 15.51.7: localizing the structural map `A → A^h` at the contracted prime of
`mh` gives the canonical local map into `(A^h)_(mh)`. -/
noncomputable abbrev contracted_pair_henselization_localRingHom
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime mh.asIdeal :=
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  Localization.localRingHom
    p.asIdeal
    mh.asIdeal
    (toHenselization (pairOfIdeal I))
    (contracted_pair_henselization_comap_eq (I := I) mh)

/-- Helper for Lemma 15.51.7: on source elements, the localized structural map is exactly the
localized target algebra map. -/
lemma contracted_pair_henselization_localRingHom_toHenselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I)))
    (a : A) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    contracted_pair_henselization_localRingHom (I := I) mh
        (algebraMap A (Localization.AtPrime p.asIdeal) a) =
      algebraMap (henselizationRing (pairOfIdeal I)) (Localization.AtPrime mh.asIdeal)
        ((toHenselization (pairOfIdeal I)) a) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  -- Proof comment: `Localization.localRingHom` is characterized by sending a base element to its
  -- image in the localized target.
  simpa [contracted_pair_henselization_localRingHom, p] using
    (Localization.localRingHom_to_map
      p.asIdeal
      mh.asIdeal
      (toHenselization (pairOfIdeal I))
      (contracted_pair_henselization_comap_eq (I := I) mh)
      a)

/-- Helper for Lemma 15.51.7: after localizing at the contracted branch, the structural map
commutes with the original map `A → A^h`. -/
lemma contracted_pair_henselization_localRingHom_comp_toHenselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    (contracted_pair_henselization_localRingHom (I := I) mh).comp
        (algebraMap A (Localization.AtPrime p.asIdeal)) =
      (algebraMap (henselizationRing (pairOfIdeal I)) (Localization.AtPrime mh.asIdeal)).comp
        (toHenselization (pairOfIdeal I)) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  -- Proof comment: the previous pointwise formula upgrades immediately to equality of ring maps.
  ext a
  simpa [RingHom.comp_apply, p] using
    contracted_pair_henselization_localRingHom_toHenselization
      (I := I) mh a

/-- Helper for Lemma 15.51.7: the localized structural map is a local homomorphism. -/
lemma contracted_pair_henselization_localRingHom_isLocalHom
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    IsLocalHom (contracted_pair_henselization_localRingHom (I := I) mh) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  -- Proof comment: this is the canonical locality statement for `Localization.localRingHom`.
  simpa [contracted_pair_henselization_localRingHom, p] using
    (Localization.isLocalHom_localRingHom
      p.asIdeal
      mh.asIdeal
      (toHenselization (pairOfIdeal I))
      (contracted_pair_henselization_comap_eq (I := I) mh))

/-- Helper for Lemma 15.51.7: the contracted local ring `A_p` attached to a maximal branch `m^h`
has the canonical local henselization used in the source proof. -/
noncomputable abbrev contracted_localRing_henselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    Type u :=
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  henselizationRing (pairOfIdeal (maximalIdeal (Localization.AtPrime p.asIdeal)))

/-- Helper for Lemma 15.51.7: the canonical local henselization of the contracted localization is a
henselization of that local ring. -/
lemma contracted_localRing_henselization_isHenselizationOf
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    IsHenselizationOf R (contracted_localRing_henselization (I := I) mh) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  -- Proof comment: this is exactly the owner theorem identifying the pair henselization at the
  -- maximal ideal of a local ring with its local henselization.
  simpa [contracted_localRing_henselization, p, R] using
    (localRing_henselization_isHenselizationOf R)

/-- Helper for Lemma 15.51.7: the source ideal `I` maps into the maximal ideal of the canonical
local henselization of the contracted localization `A_p`. -/
lemma sourceIdeal_le_comap_contracted_localRing_henselization_maximal
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
    let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
    I ≤ Ideal.comap (algebraMap A Rh) (maximalIdeal Rh) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
  let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsHenselizationOf R Rh :=
    contracted_localRing_henselization_isHenselizationOf (I := I) mh
  -- Proof comment: first `I` lands in the contracted prime `p`, hence in the maximal ideal of
  -- `A_p`; the canonical henselization map of `A_p` is local, so its maximal-ideal pullback is
  -- still `maximalIdeal A_p`.
  calc
    I ≤ Ideal.comap (algebraMap A R) (maximalIdeal R) := by
          simpa [R, p] using ideal_le_contracted_pair_henselization_prime (I := I) mh
    _ = Ideal.comap (algebraMap A Rh) (Ideal.comap (algebraMap R Rh) (maximalIdeal Rh)) := by
          rw [Ideal.comap_comap]
          simp [R, Rh, IsScalarTower.algebraMap_eq A R Rh]
    _ = Ideal.comap (algebraMap A Rh) (maximalIdeal Rh) := by
          congr 1
          simpa using (IsLocalHom.comap_maximalIdeal (f := algebraMap R Rh))

/-- Helper for Lemma 15.51.7: the universal property of pair henselization gives a comparison map
from `A^h` to the canonical local henselization of the contracted localization `A_p`. -/
noncomputable abbrev pair_henselization_to_contracted_localRing_henselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
    let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
    henselizationRing (pairOfIdeal I) →+* Rh :=
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
  let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := I) (B := Rh) (K := maximalIdeal Rh)
        (by infer_instance)
        (sourceIdeal_le_comap_contracted_localRing_henselization_maximal (I := I) mh)

/-- Helper for Lemma 15.51.7: the comparison map from `A^h` to the canonical local henselization
restricts to the canonical composite `A → A_p → (A_p)^h` on the source ring `A`. -/
lemma pair_henselization_to_contracted_localRing_henselization_comp
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
    let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
    (pair_henselization_to_contracted_localRing_henselization (I := I) mh).comp
        (toHenselization (pairOfIdeal I)) =
      algebraMap A Rh := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra A Rh := RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
  let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: this is the defining compatibility clause of the chosen map from the pair
  -- henselization universal property.
  exact Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := I) (B := Rh) (K := maximalIdeal Rh)
        (by infer_instance)
        (sourceIdeal_le_comap_contracted_localRing_henselization_maximal (I := I) mh)

/-- Helper for Lemma 15.51.7: the chosen maximal branch `mh` yields a residue-field map from the
canonical local henselization `Rh = (A_p)^h` to the residue field of the localized branch
`(A^h)_(mh)`. -/
noncomputable abbrev contracted_localRing_henselization_to_branch_residueField
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime mh.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
    let g₀ : R →+* ResidueField B :=
      (algebraMap B (ResidueField B)).comp
        (contracted_pair_henselization_localRingHom (I := I) mh)
    let _ : Algebra R (ResidueField B) := g₀.toAlgebra
    Rh →+* ResidueField B :=
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
  let g₀ : R →+* ResidueField B :=
    (algebraMap B (ResidueField B)).comp
      (contracted_pair_henselization_localRingHom (I := I) mh)
  let _ : Algebra R (ResidueField B) := g₀.toAlgebra
  have hres :
      Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B)) =
        maximalIdeal B := by
    -- Proof comment: the residue map of a local ring kills exactly its maximal ideal.
    simpa [RingHom.ker_eq_comap_bot, ResidueField.algebraMap_eq] using
      (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)
  have hIK :
      maximalIdeal R ≤ Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
    -- Proof comment: the chosen branch residue map factors through the residue map of the local
    -- branch `(A^h)_(mh)`, so it kills the maximal ideal of `R`.
    calc
      maximalIdeal R =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh) (maximalIdeal B) := by
            simpa [R, B, p] using
              (IsLocalRing.maximalIdeal_comap
                (contracted_pair_henselization_localRingHom (I := I) mh))
      _ =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh)
            (Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B))) := by
            rw [hres]
      _ = Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
            rw [Ideal.comap_comap]
  -- Proof comment: apply the local henselization universal property with target ideal `0`.
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal R) (B := ResidueField B) (K := (⊥ : Ideal (ResidueField B)))
        (by infer_instance)
        hIK

/-- Helper for Lemma 15.51.7: the branch residue-field map from `Rh` extends the canonical local
map `R → (A^h)_(mh) → κ((A^h)_(mh))`. -/
lemma contracted_localRing_henselization_to_branch_residueField_comp
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime mh.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
    let g₀ : R →+* ResidueField B :=
      (algebraMap B (ResidueField B)).comp
        (contracted_pair_henselization_localRingHom (I := I) mh)
    let _ : Algebra R (ResidueField B) := g₀.toAlgebra
    (contracted_localRing_henselization_to_branch_residueField (I := I) mh).comp
        (algebraMap R Rh) =
      g₀ := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
  let g₀ : R →+* ResidueField B :=
    (algebraMap B (ResidueField B)).comp
      (contracted_pair_henselization_localRingHom (I := I) mh)
  let _ : Algebra R (ResidueField B) := g₀.toAlgebra
  have hres :
      Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B)) =
        maximalIdeal B := by
    -- Proof comment: reuse the residue-field kernel calculation from the definition above.
    simpa [RingHom.ker_eq_comap_bot, ResidueField.algebraMap_eq] using
      (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)
  have hIK :
      maximalIdeal R ≤ Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
    -- Proof comment: the same kernel computation shows that the local branch map kills
    -- `maximalIdeal R` after passage to the residue field of `B`.
    calc
      maximalIdeal R =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh) (maximalIdeal B) := by
            simpa [R, B, p] using
              (IsLocalRing.maximalIdeal_comap
                (contracted_pair_henselization_localRingHom (I := I) mh))
      _ =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh)
            (Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B))) := by
            rw [hres]
      _ = Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
            rw [Ideal.comap_comap]
  -- Proof comment: this is exactly the defining compatibility clause of the chosen henselization
  -- map into the branch residue field.
  exact Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal R) (B := ResidueField B) (K := (⊥ : Ideal (ResidueField B)))
        (by infer_instance)
        hIK

/-- Helper for Lemma 15.51.7: the universal map from the pair henselization to the local
henselization of the contracted localization lands in the chosen maximal branch `mh`. -/
lemma pair_henselization_to_contracted_localRing_henselization_comap_maximalIdeal
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let Rh := contracted_localRing_henselization (I := I) mh
    Ideal.comap
        (pair_henselization_to_contracted_localRing_henselization (I := I) mh)
        (maximalIdeal Rh) =
      mh.asIdeal := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let g₀ : R →+* ResidueField B :=
    (algebraMap B (ResidueField B)).comp
      (contracted_pair_henselization_localRingHom (I := I) mh)
  let g : Rh →+* ResidueField B :=
    contracted_localRing_henselization_to_branch_residueField (I := I) mh
  let _ : Algebra A (ResidueField B) := RingHom.toAlgebra (g₀.comp (algebraMap A R))
  have hg₀_kills_maximal :
      maximalIdeal R ≤ Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
    have hres :
        Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B)) =
          maximalIdeal B := by
      -- Proof comment: the residue map of a local ring kills exactly its maximal ideal.
      simpa [RingHom.ker_eq_comap_bot, ResidueField.algebraMap_eq] using
        (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)
    -- Proof comment: the chosen branch residue map factors through the residue map of
    -- `(A^h)_(mh)`, so it kills the maximal ideal of `R`.
    calc
      maximalIdeal R =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh) (maximalIdeal B) := by
            simpa [R, B, p] using
              (IsLocalRing.maximalIdeal_comap
                (contracted_pair_henselization_localRingHom (I := I) mh))
      _ =
          Ideal.comap (contracted_pair_henselization_localRingHom (I := I) mh)
            (Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B))) := by
            rw [hres]
      _ = Ideal.comap g₀ (⊥ : Ideal (ResidueField B)) := by
            rw [Ideal.comap_comap]
  have hg_comp :
      g.comp (algebraMap R Rh) = g₀ :=
    contracted_localRing_henselization_to_branch_residueField_comp (I := I) mh
  have hg_maximal :
      Ideal.comap g (⊥ : Ideal (ResidueField B)) = maximalIdeal Rh := by
    apply le_antisymm
    · -- Proof comment: kernels into a field are proper, hence lie in the maximal ideal of the
      -- local source ring.
      exact IsLocalRing.le_maximalIdeal (by
        simpa [RingHom.ker_eq_comap_bot] using (RingHom.ker_ne_top g))
    · -- Proof comment: `g` extends a map killing `maximalIdeal R`, so it kills the image
      -- `maximalIdeal Rh = maximalIdeal R • Rh`.
      rw [← IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)]
      apply Ideal.map_le_iff_le_comap.mpr
      simpa [hg_comp, Ideal.comap_comap] using hg₀_kills_maximal
  let ψ : henselizationRing (pairOfIdeal I) →+* ResidueField B :=
    (algebraMap B (ResidueField B)).comp
      (algebraMap (henselizationRing (pairOfIdeal I)) B)
  have hg_pair_comp :
      (g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh)).comp
          (toHenselization (pairOfIdeal I)) =
        g₀.comp (algebraMap A R) := by
    -- Proof comment: both comparison maps restrict to `A → A_p → κ(B)` on the source ring.
    ext a
    simp [RingHom.comp_apply, hg_comp,
      pair_henselization_to_contracted_localRing_henselization_comp (I := I) mh]
  have hψ_comp :
      ψ.comp (toHenselization (pairOfIdeal I)) =
        g₀.comp (algebraMap A R) := by
    -- Proof comment: the canonical localization-residue map on `A^h` has the same restriction.
    ext a
    simp [ψ, g₀, RingHom.comp_apply,
      contracted_pair_henselization_localRingHom_toHenselization (I := I) mh a]
  have hI_residue :
      I ≤ Ideal.comap (algebraMap A (ResidueField B)) (⊥ : Ideal (ResidueField B)) := by
    -- Proof comment: `I` lies in the contracted prime `p`, and `g₀` kills the maximal ideal of
    -- `A_p`, so the induced `A`-map to the residue field of `B` kills `I`.
    calc
      I ≤ Ideal.comap (algebraMap A R) (maximalIdeal R) := by
            simpa [R, p] using ideal_le_contracted_pair_henselization_prime (I := I) mh
      _ ≤ Ideal.comap (algebraMap A R) (Ideal.comap g₀ (⊥ : Ideal (ResidueField B))) := by
            exact Ideal.comap_mono hg₀_kills_maximal
      _ = Ideal.comap (algebraMap A (ResidueField B)) (⊥ : Ideal (ResidueField B)) := by
            rfl
  have hcompare :
      g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh) = ψ := by
    -- Proof comment: maps from the pair henselization to the henselian target field are uniquely
    -- determined by their restriction to `A`.
    rcases
        existsUnique_henselizationRingHom_of_henselian_target
          (I := I) (B := ResidueField B) (K := (⊥ : Ideal (ResidueField B)))
          (by infer_instance)
          hI_residue with
      ⟨φ, hφ_comp, hφ_unique⟩
    calc
      g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh) = φ :=
        hφ_unique _ hg_pair_comp
      _ = ψ := (hφ_unique _ hψ_comp).symm
  have hres :
      Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B)) =
        maximalIdeal B := by
    -- Proof comment: the residue map of the localized branch again kills exactly the maximal
    -- ideal.
    simpa [RingHom.ker_eq_comap_bot, ResidueField.algebraMap_eq] using
      (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)
  -- Proof comment: pull the maximal ideal of `Rh` back through the residue-field comparison and
  -- then identify the canonical localization kernel with `mh`.
  calc
    Ideal.comap
        (pair_henselization_to_contracted_localRing_henselization (I := I) mh)
        (maximalIdeal Rh) =
      Ideal.comap
        (pair_henselization_to_contracted_localRing_henselization (I := I) mh)
        (Ideal.comap g (⊥ : Ideal (ResidueField B))) := by
          rw [hg_maximal.symm]
    _ = Ideal.comap
        (g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh))
        (⊥ : Ideal (ResidueField B)) := by
          rw [Ideal.comap_comap]
    _ = Ideal.comap ψ (⊥ : Ideal (ResidueField B)) := by
          rw [hcompare]
    _ =
      Ideal.comap (algebraMap (henselizationRing (pairOfIdeal I)) B)
        (Ideal.comap (algebraMap B (ResidueField B)) (⊥ : Ideal (ResidueField B))) := by
          rw [Ideal.comap_comap]
    _ = Ideal.comap (algebraMap (henselizationRing (pairOfIdeal I)) B) (maximalIdeal B) := by
          rw [hres]
    _ = mh.asIdeal := by
          simpa [B] using
            (Localization.AtPrime.comap_maximalIdeal
              (R := henselizationRing (pairOfIdeal I)) (I := mh.asIdeal))

/-- Helper for Lemma 15.51.7: once the branch-selection equality is known, the universal map
`A^h → (A_p)^h` factors through the localization `(A^h)_(mh)`. -/
noncomputable abbrev localized_pair_henselization_factor_to_contracted_localRing_henselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let Rh := contracted_localRing_henselization (I := I) mh
    Localization.AtPrime mh.asIdeal →+* Rh :=
  let Rh := contracted_localRing_henselization (I := I) mh
  Localization.localRingHom
    mh.asIdeal
    (maximalIdeal Rh)
    (pair_henselization_to_contracted_localRing_henselization (I := I) mh)
    (by
      simpa [Rh] using
        pair_henselization_to_contracted_localRing_henselization_comap_maximalIdeal
          (I := I) mh)

/-- Helper for Lemma 15.51.7: a bijective ring map is already an ind-étale map, so it can be
used as a harmless transport factor inside henselization comparisons. -/
lemma isFilteredColimitOfEtale_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hbij : Function.Bijective f) :
    f.IsFilteredColimitOfEtale := by
  have hEtale : CommRingCat.etale (CommRingCat.ofHom f) := by
    -- Proof comment: a bijective ring map is étale, hence belongs to the ind-étale closure.
    dsimp [CommRingCat.etale]
    exact RingHom.Etale.of_bijective hbij
  -- Proof comment: the ind-étale closure contains every étale morphism.
  dsimp [RingHom.IsFilteredColimitOfEtale]
  exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale

/-- Helper for Lemma 15.51.7: ring equivalences preserve henselian local rings. -/
lemma henselianLocalRing_of_equiv
    {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) [HenselianLocalRing R] :
    HenselianLocalRing S := by
  letI : IsLocalRing S := e.isLocalRing
  have hR := ((HenselianLocalRing.TFAE R).out 0 2).mp
    (show HenselianLocalRing R from inferInstance)
  -- Proof comment: transport clause `(3)` of the henselian local TFAE across the ring
  -- equivalence, exactly as in the canonical owner argument.
  refine ((HenselianLocalRing.TFAE S).out 2 0).mp ?_
  intro K _ φ hφ f hf a₀ hroot hderiv
  let g : Polynomial R := f.map (e.symm : S →+* R)
  have hcomp : ((φ.comp (e : R →+* S)).comp (e.symm : S →+* R)) = φ := by
    -- Proof comment: `e` and `e.symm` cancel inside the coefficient map.
    ext x
    simp
  have hφe : Function.Surjective (φ.comp (e : R →+* S)) := by
    -- Proof comment: precomposing a surjective coefficient map with an equivalence stays
    -- surjective.
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨e.symm x, by simp⟩
  have hg_monic : g.Monic := hf.map (e.symm : S →+* R)
  have hg_root : g.eval₂ (φ.comp (e : R →+* S)) a₀ = 0 := by
    -- Proof comment: evaluating the transported polynomial in `R` reproduces the original root
    -- equation in `S`.
    rw [show g = f.map (e.symm : S →+* R) by rfl, Polynomial.eval₂_map, hcomp]
    exact hroot
  have hg_deriv :
      g.derivative.eval₂ (φ.comp (e : R →+* S)) a₀ =
        f.derivative.eval₂ φ a₀ := by
    -- Proof comment: the derivative transforms compatibly under the same coefficient transport.
    rw [show g = f.map (e.symm : S →+* R) by rfl, Polynomial.derivative_map,
      Polynomial.eval₂_map, hcomp]
  have hg_simple : g.derivative.eval₂ (φ.comp (e : R →+* S)) a₀ ≠ 0 := by
    -- Proof comment: the nonvanishing derivative condition is preserved by the derivative rewrite.
    simpa [hg_deriv] using hderiv
  obtain ⟨a, ha_root, ha_map⟩ := hR (φ.comp (e : R →+* S)) hφe g hg_monic a₀ hg_root hg_simple
  refine ⟨e a, ?_, ?_⟩
  · -- Proof comment: apply `e.symm` to reduce the lifted root equation back to the root already
    -- constructed in `R`.
    have ha_eval₂ : Polynomial.eval₂ (e.symm : S →+* R) a f = 0 := by
      simpa [g, Polynomial.IsRoot, Polynomial.eval_map] using ha_root
    exact
      Polynomial.isRoot_of_eval₂_map_eq_zero
        (p := f) (f := (e.symm : S →+* R)) e.symm.injective
        (by simpa using ha_eval₂)
  · -- Proof comment: the congruence modulo the kernel is exactly the pushed-forward one from the
    -- source henselian lift.
    simpa using ha_map

/-- Helper for Lemma 15.51.7: the localized pair henselization is canonically the local
henselization of the contracted branch `A_p`. -/
lemma localized_pair_henselization_equiv_contracted_localRing_henselization
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime mh.asIdeal
    let Rh := contracted_localRing_henselization (I := I) mh
    let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
    B ≃ₐ[R] Rh := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra R B := (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
  let _ : IsLocalHom (algebraMap R B) :=
    contracted_pair_henselization_localRingHom_isLocalHom (I := I) mh
  let _ : Algebra A Rh :=
    RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
  let _ : IsScalarTower A R Rh := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsHenselizationOf R Rh :=
    contracted_localRing_henselization_isHenselizationOf (I := I) mh
  let f : B →+* Rh :=
    localized_pair_henselization_factor_to_contracted_localRing_henselization (I := I) mh
  have hRh_comap :
      Ideal.comap (algebraMap A Rh) (maximalIdeal Rh) = p.asIdeal := by
    -- Proof comment: the canonical local henselization of `A_p` still lies over the contracted
    -- branch prime `p`.
    calc
      Ideal.comap (algebraMap A Rh) (maximalIdeal Rh) =
          Ideal.comap (algebraMap A R)
            (Ideal.comap (algebraMap R Rh) (maximalIdeal Rh)) := by
              rw [Ideal.comap_comap]
              simp [R, Rh, IsScalarTower.algebraMap_eq A R Rh]
      _ = Ideal.comap (algebraMap A R) (maximalIdeal R) := by
            congr 1
            simpa using (IsLocalHom.comap_maximalIdeal (f := algebraMap R Rh))
      _ = p.asIdeal := by
            simpa [R, p] using
              (Localization.AtPrime.comap_maximalIdeal (R := A) (I := p.asIdeal))
  have hf_comp :
      f.comp (algebraMap R B) = algebraMap R Rh := by
    -- Proof comment: both maps `R → Rh` are the localizations of the same composite
    -- `A → A^h → Rh`.
    refine Localization.localRingHom_unique
      p.asIdeal
      (maximalIdeal Rh)
      (algebraMap A Rh)
      hRh_comap
      (fun a ↦ ?_)
    simp only [f, R, B, Rh, RingHom.comp_apply, Localization.localRingHom_to_map]
    simpa [pair_henselization_to_contracted_localRing_henselization_comp (I := I) mh]
      using
        (contracted_pair_henselization_localRingHom_toHenselization
          (I := I) mh a)
  let fAlg : B →ₐ[R] Rh :=
    { toRingHom := f
      commutes' := by
        intro x
        exact DFunLike.congr_fun hf_comp x }
  have hRK :
      maximalIdeal R ≤ Ideal.comap (algebraMap R B) (maximalIdeal B) := by
    -- Proof comment: the localized branch map `R → B` is local, so it kills the maximal ideal of
    -- `R` in the residue field of `B`.
    simpa [R, B, p] using
      (show maximalIdeal R ≤ Ideal.comap (algebraMap R B) (maximalIdeal B) from
        le_of_eq (IsLocalHom.comap_maximalIdeal (f := algebraMap R B)).symm)
  let g : Rh →+* B :=
    Classical.choose <|
      ExistsUnique.exists <|
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal R) (B := B) (K := maximalIdeal B)
          (by infer_instance)
          hRK
  have hg_comp :
      g.comp (algebraMap R Rh) = algebraMap R B := by
    -- Proof comment: this is the defining compatibility of the chosen reverse comparison map.
    exact Classical.choose_spec <|
      ExistsUnique.exists <|
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal R) (B := B) (K := maximalIdeal B)
          (by infer_instance)
          hRK
  have hI_B :
      I ≤ Ideal.comap (algebraMap A B) (maximalIdeal B) := by
    -- Proof comment: the original ideal lands in the contracted prime `p`, hence in the maximal
    -- ideal of the localized branch `B`.
    calc
      I ≤ Ideal.comap (algebraMap A R) (maximalIdeal R) := by
            simpa [R, p] using ideal_le_contracted_pair_henselization_prime (I := I) mh
      _ = Ideal.comap (algebraMap A B) (Ideal.comap (algebraMap R B) (maximalIdeal B)) := by
            rw [Ideal.comap_comap]
            simp [R, B, IsScalarTower.algebraMap_eq A R B]
      _ = Ideal.comap (algebraMap A B) (maximalIdeal B) := by
            congr 1
            simpa using (IsLocalHom.comap_maximalIdeal (f := algebraMap R B))
  have hgf_pair :
      g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh) =
        algebraMap (henselizationRing (pairOfIdeal I)) B := by
    -- Proof comment: both maps from `A^h` to `B` extend the same source map `A → A_p → B`, so
    -- the pair henselization universal property identifies them.
    rcases
        existsUnique_henselizationRingHom_of_henselian_target
          (I := I) (B := B) (K := maximalIdeal B)
          (by infer_instance)
          hI_B with
      ⟨φ, hφ_comp, hφ_unique⟩
    have hleft :
        (g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh)).comp
            (toHenselization (pairOfIdeal I)) =
          algebraMap A B := by
      ext a
      simp [RingHom.comp_apply, hg_comp,
        pair_henselization_to_contracted_localRing_henselization_comp (I := I) mh]
    have hright :
        (algebraMap (henselizationRing (pairOfIdeal I)) B).comp
            (toHenselization (pairOfIdeal I)) =
          algebraMap A B := by
      rfl
    calc
      g.comp (pair_henselization_to_contracted_localRing_henselization (I := I) mh) = φ :=
        hφ_unique _ hleft
      _ = algebraMap (henselizationRing (pairOfIdeal I)) B :=
        (hφ_unique _ hright).symm
  have hgf :
      g.comp f = RingHom.id B := by
    -- Proof comment: once both endomorphisms of the localization agree on `A^h`, localization
    -- uniqueness forces them to be equal.
    refine Localization.localRingHom_unique
      mh.asIdeal
      (maximalIdeal B)
      (algebraMap (henselizationRing (pairOfIdeal I)) B)
      (by simpa [B] using
        (Localization.AtPrime.comap_maximalIdeal
          (R := henselizationRing (pairOfIdeal I)) (I := mh.asIdeal)))
      (fun x ↦ ?_)
    simp only [f, RingHom.comp_apply, Localization.localRingHom_to_map]
    exact DFunLike.congr_fun hgf_pair x
  have hfg :
      f.comp g = RingHom.id Rh := by
    -- Proof comment: both endomorphisms of the canonical local henselization extend the identity
    -- map of the contracted local ring `R`, so local henselization uniqueness makes them equal.
    rcases
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal R) (B := Rh) (K := maximalIdeal Rh)
          (by infer_instance)
          (show maximalIdeal R ≤ Ideal.comap (algebraMap R Rh) (maximalIdeal Rh) from
            by
              simpa using
                (show maximalIdeal R ≤
                    Ideal.comap (algebraMap R Rh) (maximalIdeal Rh) from
                  le_of_eq (IsLocalHom.comap_maximalIdeal (f := algebraMap R Rh)).symm))
      with
      ⟨φ, hφ_comp, hφ_unique⟩
    have hleft :
        (f.comp g).comp (algebraMap R Rh) = algebraMap R Rh := by
      calc
        (f.comp g).comp (algebraMap R Rh) =
            f.comp (g.comp (algebraMap R Rh)) := by
              rw [RingHom.comp_assoc]
        _ = f.comp (algebraMap R B) := by rw [hg_comp]
        _ = algebraMap R Rh := hf_comp
    have hright :
        (RingHom.id Rh).comp (algebraMap R Rh) = algebraMap R Rh := by
      rfl
    calc
      f.comp g = φ := hφ_unique _ hleft
      _ = RingHom.id Rh := (hφ_unique _ hright).symm
  have hf_injective : Function.Injective f := by
    -- Proof comment: the explicit left inverse `g` makes `f` injective.
    intro x y hxy
    calc
      x = g (f x) := by
        symm
        exact DFunLike.congr_fun hgf x
      _ = g (f y) := by rw [hxy]
      _ = y := DFunLike.congr_fun hgf y
  have hf_surjective : Function.Surjective f := by
    -- Proof comment: the explicit right inverse `g` makes `f` surjective.
    intro y
    refine ⟨g y, ?_⟩
    exact DFunLike.congr_fun hfg y
  -- Proof comment: package the two inverse local comparison maps into the canonical
  -- `R`-algebra equivalence between the localized pair henselization and the canonical local
  -- henselization of the contracted branch.
  exact AlgEquiv.ofBijective fAlg ⟨hf_injective, hf_surjective⟩

/-- Helper for Lemma 15.51.7: the localized pair henselization should be viewed as a henselization
of the contracted local ring. -/
lemma localized_pair_henselization_isHenselizationOf
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
      (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
    IsHenselizationOf (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let _ : IsLocalHom (contracted_pair_henselization_localRingHom (I := I) mh) :=
    contracted_pair_henselization_localRingHom_isLocalHom (I := I) mh
  let Rh := contracted_localRing_henselization (I := I) mh
  let _ : Algebra A Rh :=
    RingHom.toAlgebra ((algebraMap R Rh).comp (algebraMap A R))
  let _ : IsScalarTower A (Localization.AtPrime p.asIdeal) Rh :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hRh :
      IsHenselizationOf R Rh :=
    contracted_localRing_henselization_isHenselizationOf (I := I) mh
  let e : B ≃ₐ[R] Rh :=
    localized_pair_henselization_equiv_contracted_localRing_henselization (I := I) mh
  have hlocal_B : IsLocalHom (algebraMap R B) :=
    contracted_pair_henselization_localRingHom_isLocalHom (I := I) mh
  have hcomp :
      algebraMap R B = e.symm.toRingHom.comp (algebraMap R Rh) := by
    -- Proof comment: the inverse algebra equivalence identifies the structural map of `B` with
    -- the structural map of the canonical henselization `Rh`.
    ext x
    exact (e.symm.commutes x).symm
  letI : HenselianLocalRing B := henselianLocalRing_of_equiv e.symm.toRingEquiv
  letI : IsLocalHom e.symm.toRingHom := Function.Surjective.isLocalHom _ e.symm.surjective
  refine
    { toHenselianLocalRing := inferInstance
      toIsLocalHom := hlocal_B
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · -- Proof comment: compose the ind-étale presentation of `Rh` with the bijective transport
    -- map `Rh ≃ B`.
    have he :
        e.symm.toRingHom.IsFilteredColimitOfEtale :=
      isFilteredColimitOfEtale_of_bijective e.symm.toRingHom e.symm.bijective
    exact hcomp ▸
      RingHom.isFilteredColimitOfEtale_comp
        (algebraMap R Rh)
        e.symm.toRingHom
        IsHenselizationOf.isFilteredColimitOfEtale
        he
  · -- Proof comment: the maximal ideal of `B` is the image of the maximal ideal of `R` because
    -- the same statement holds for `Rh` and `e.symm` is a surjective local map.
    calc
      Ideal.map (algebraMap R B) (maximalIdeal R) =
          Ideal.map e.symm.toRingHom (Ideal.map (algebraMap R Rh) (maximalIdeal R)) := by
            rw [hcomp, Ideal.map_map]
      _ = Ideal.map e.symm.toRingHom (maximalIdeal Rh) := by
            rw [IsHenselizationOf.map_maximalIdeal]
      _ = maximalIdeal B := by
            simpa using IsLocalRing.map_maximalIdeal_of_surjective
              e.symm.toRingHom e.symm.surjective
  · -- Proof comment: the residue-field map for `R → B` is the composite of the residue-field
    -- bijection for `R → Rh` with the one induced by the surjective local map `Rh → B`.
    have he_res :
        Function.Bijective (ResidueField.map e.symm.toRingHom) :=
      residueField_bijective_of_surjective_localHom
        (f := e.symm.toRingHom) e.symm.surjective
    have hcomp_res :
        (ResidueField.map e.symm.toRingHom).comp
            (ResidueField.map (algebraMap R Rh)) =
          ResidueField.map (algebraMap R B) := by
      ext x
      simp [hcomp]
    exact hcomp_res.symm ▸ he_res.comp IsHenselizationOf.residueField_bijective

/-- Helper for Lemma 15.51.7: once the localized target is packaged as a henselization of the
contracted local ring, the completion comparison is exactly Lemma `15.43.9`. -/
lemma localized_pair_henselization_completion_bijective
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
      (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
    let _ : IsHenselizationOf (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
      localized_pair_henselization_isHenselizationOf (I := I) mh
    Function.Bijective
      (maximalIdealCompletionMap
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal))) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
    (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
  let _ : IsHenselizationOf (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
    localized_pair_henselization_isHenselizationOf (I := I) mh
  let _ : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime mh.asIdeal) :=
    henselizationMap_faithfullyFlat.flat
  let _ : IsNoetherianRing (Localization.AtPrime mh.asIdeal) :=
    isNoetherianRing_henselization
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime mh.asIdeal)
  -- Proof comment: the henselization owner gives both the maximal-ideal equality and the residue
  -- field bijection needed by the completion comparison theorem.
  simpa [p] using
    (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
      (A := Localization.AtPrime p.asIdeal)
      (B := Localization.AtPrime mh.asIdeal)
      IsHenselizationOf.map_maximalIdeal
      IsHenselizationOf.residueField_bijective)

/-- Helper for Lemma 15.51.7: once property `P` holds on the completed `κ(q)`-fiber, the source
proof still needs the henselization fiber product decomposition to isolate the chosen branch
`qh`. -/
lemma localized_pair_henselization_branch_formalFiber_hasProperty
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I)))
    (qh : PrimeSpectrum (Localization.AtPrime mh.asIdeal)) :
    let p : PrimeSpectrum A :=
      PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
    let R := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime mh.asIdeal
    let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) qh
    let Bhat := AdicCompletion (maximalIdeal B) B
    P q.asIdeal.ResidueField (q.asIdeal.Fiber Bhat) →
      P q.asIdeal.ResidueField (qh.asIdeal.Fiber Bhat) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) qh
  let Bhat := AdicCompletion (maximalIdeal B) B
  -- Proof comment: this is exactly the source proof's branch-isolation step. One tensors the
  -- bijective map `q.asIdeal.Fiber B → ∏_{q_i|q} κ(q_i)` with `Bhat`, rewrites the completed
  -- `κ(q)`-fiber as the product of the completed branch fibers, and then applies axiom `(B)` to
  -- pass from the whole product to the chosen `qh`-factor.
  -- TODO: package the tensor-product/product comparison for the completed `q`-fiber of `B`, then
  -- pull back the chosen product-coordinate prime through that comparison, and finally use the
  -- coordinate localization equivalence above to isolate the `qh`-branch.
  intro hbase
  let _ : IsNoetherianRing (q.asIdeal.Fiber Bhat) :=
    fiber_isNoetherianRing_of_isNoetherianTarget (R := R) (S := Bhat) q
  have hlocal :
      ∀ Q : PrimeSpectrum (q.asIdeal.Fiber Bhat),
        P q.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) := by
    -- Proof comment: axiom `(B)` reduces the branch extraction to identifying the correct prime
    -- localization of the completed `κ(q)`-fiber.
    exact
      (FieldAlgebraProperty.HasPropertyB.localizationCriterion
        (P := P) q.asIdeal.ResidueField (q.asIdeal.Fiber Bhat)).1 hbase
  let qOver : q.asIdeal.primesOver B := Ideal.primesOver.mk q.asIdeal qh.asIdeal
  -- Route correction: the remaining gap is no longer the localization criterion itself. The
  -- unresolved step is to construct the pulled-back prime of `q.asIdeal.Fiber Bhat` corresponding
  -- to the `qOver` coordinate in the completed fiber/product decomposition and rewrite its
  -- localization to the target branch fiber `qh.asIdeal.Fiber Bhat`.
  let _ := hlocal
  let _ := qOver
  sorry

/-- Helper for Lemma 15.51.7: the formal fibers of the localized pair henselization should be
transferred from the contracted local ring using the henselization fiber decomposition. -/
lemma localized_pair_henselization_localFormalFibersHaveProperty
    (hA : IsPRing P A)
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    LocalFormalFibersHaveProperty P (Localization.AtPrime mh.asIdeal) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  let R := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime mh.asIdeal
  have hsource :
      IsPRing P R := by
    -- Proof comment: the ambient `P`-ring hypothesis descends immediately to the contracted
    -- localization.
    simpa [p] using
      contracted_pair_henselization_localization_isPRing
        (I := I) (P := P) hA mh.toPrimeSpectrum
  let _ : Algebra R B :=
    (contracted_pair_henselization_localRingHom (I := I) mh).toAlgebra
  let _ : IsHenselizationOf R B :=
    localized_pair_henselization_isHenselizationOf (I := I) mh
  have hcompletion :
      Function.Bijective
        (maximalIdealCompletionMap
          (algebraMap R B)) :=
    localized_pair_henselization_completion_bijective (I := I) mh
  let _ : IsPRing P R := hsource
  intro qh
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) qh
  let qOver : q.asIdeal.primesOver B := Ideal.primesOver.mk q.asIdeal qh.asIdeal
  let Rhat := AdicCompletion (maximalIdeal R) R
  let Bhat := AdicCompletion (maximalIdeal B) B
  have hsource_fibers :
      ∀ q' : PrimeSpectrum R,
        P q'.asIdeal.ResidueField (q'.asIdeal.Fiber Rhat) := by
    intro q'
    -- Proof comment: the base `P`-ring hypothesis controls every completed fiber of the
    -- contracted localization `R = A_p`.
    simpa [Rhat] using
      completion_fibers_have_property_of_pRing
        (P := P) (A := R) (I := maximalIdeal R) hsource q'
  let eCompletion : Rhat ≃ₐ[R] Bhat :=
    AlgEquiv.ofRingEquiv
      (completion_comparison_equiv_of_bijective (A := R) (B := B) hcompletion)
      (fun x ↦ by
        -- Proof comment: the completion comparison extends the original local map `R → B`.
        simpa [Rhat, Bhat] using
          DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R B)) x)
  let _ : Algebra Rhat Bhat := eCompletion.toRingHom.toAlgebra
  let _ : IsScalarTower R Rhat Bhat := by
    exact IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun x ↦ by
      change eCompletion ((algebraMap R Rhat) x) = (algebraMap R Bhat) x
      exact eCompletion.commutes x
  let _ : Module.Flat R Rhat := maximalIdeal_completion_flat_of_isNoetherian (S := R)
  let _ : (algebraMap Rhat Bhat).IsRegularRingMap := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (ringEquiv_isRegularRingMap eCompletion.toRingEquiv :
        eCompletion.toRingHom.IsRegularRingMap)
  have hbase :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber Bhat) := by
    -- Proof comment: axiom `(C)` transports the completed `κ(q)`-fiber from `R^∧` to `B^∧`.
    simpa [Rhat, Bhat, q] using
      (FieldAlgebraProperty.HasPropertyC.regularAscent
        (P := P) R Rhat Bhat hsource_fibers q)
  have hbranch :
      P q.asIdeal.ResidueField (qh.asIdeal.Fiber Bhat) := by
    -- Proof comment: the remaining source-faithful gap is to isolate the chosen henselization
    -- branch from the product decomposition of the completed `κ(q)`-fiber.
    exact
      localized_pair_henselization_branch_formalFiber_hasProperty
        (I := I) (P := P) mh qh hbase
  have hsep :
      Algebra.IsSeparable q.asIdeal.ResidueField qh.asIdeal.ResidueField := by
    -- Proof comment: residue fields of henselization branches are separable algebraic over the
    -- contracted residue field.
    simpa [q, qOver] using
      (henselization_residueField_isAlgebraic_and_separable
        (R := R) (Rh := B) q qOver).2
  let _ : Algebra.IsSeparable q.asIdeal.ResidueField qh.asIdeal.ResidueField := hsep
  -- Proof comment: axiom `(E)` upgrades the ground field from `κ(q)` to the actual branch
  -- residue field `κ(qh)`.
  simpa [q, Bhat] using
    (FieldAlgebraProperty.HasPropertyE.separableBaseChange
      (P := P) q.asIdeal.ResidueField qh.asIdeal.ResidueField
      (qh.asIdeal.Fiber Bhat) hbranch)

/-- Helper for Lemma 15.51.7: it remains to prove that the localization of the pair henselization
at a maximal ideal is a `P`-ring by identifying it with a henselization of the contracted local
ring and transferring the formal-fiber condition along the source proof. -/
lemma localized_pair_henselization_isPRing_at_maximal
    (hA : IsPRing P A)
    (mh : MaximalSpectrum (henselizationRing (pairOfIdeal I))) :
    IsPRing P (Localization.AtPrime mh.asIdeal) := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (toHenselization (pairOfIdeal I)) mh.toPrimeSpectrum
  have hsource :
      IsPRing P (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: the ambient `P`-ring hypothesis descends immediately to the contracted
    -- localization.
    simpa [p] using
      contracted_pair_henselization_localization_isPRing
        (I := I) (P := P) hA mh.toPrimeSpectrum
  let _ : IsPRing P (Localization.AtPrime p.asIdeal) := hsource
  -- Proof comment: after the local formal fibers are transferred along the localized
  -- henselization, Lemma `15.51.4` turns that back into the desired local `P`-ring statement.
  exact
    (isPRing_localizationAtMaximal_iff_localFormalFibersHaveProperty
      (P := P) (m := mh)).2 <|
      localized_pair_henselization_localFormalFibersHaveProperty
        (I := I) (P := P) hA mh

-- Proof sketch: by Lemma `15.51.4`, it is enough to check the local formal fibres of the
-- henselization ring at maximal ideals. For a maximal ideal `m^h` of `A^h`, compare the completed
-- local ring of `(A^h)_(m^h)` with the completion of `A_m`, where `m` is the inverse image of
-- `m^h`. The completion comparison from Lemma `15.12.4`, the finite product description of the
-- fibre from Lemma `15.45.12`, property `(B)` for localization, and property `(E)` for separable
-- algebraic residue-field extensions transfer `P` from the formal fibres of `A` to those of
-- `A^h`.
/-- Lemma 15.51.7: if `A` is a `P`-ring and the field-algebra property `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then the canonical pair-henselization ring `A^h` of `(A, I)` is again a
`P`-ring. -/
theorem isPRing_henselizationRing
    (hA : IsPRing P A) :
    IsPRing P (henselizationRing (pairOfIdeal I)) := by
  let _ : IsPRing P A := hA
  let _ : IsNoetherianRing (henselizationRing (pairOfIdeal I)) :=
    henselizationRing_isNoetherian (pairOfIdeal I)
  -- Proof comment: reduce to the maximal-local formal-fiber criterion from Lemma `15.51.4`.
  rw [isPRing_iff_localFormalFibersHaveProperty_atMaximal]
  intro mh
  -- Proof comment: once the maximal localization is known to be a `P`-ring, the same criterion
  -- identifies that with the desired local formal-fiber property.
  exact
    (isPRing_localizationAtMaximal_iff_localFormalFibersHaveProperty
      (P := P) (m := mh)).1 <|
      localized_pair_henselization_isPRing_at_maximal
        (I := I) (P := P) hA mh

end
