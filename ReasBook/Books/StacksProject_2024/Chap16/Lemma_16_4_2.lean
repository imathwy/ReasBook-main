import Mathlib
import StacksProject_2024.Chap10.Lemma_10_70_3
import StacksProject_2024.Chap16.Situation_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped TensorProduct

universe u v w x

section

/-
Domain-style sampling pass for Lemma 16.4.2.

Primary domain: commutative algebra of affine blowup charts under localization and surjective base
change.

Sampled owner declarations:
* `affineBlowupChart` from `Chap10/Definition_10_70_1`;
* `mappedIdealElement` from `Chap10/Lemma_10_70_3`;
* `tensorToAffineBlowupAlgebra` from `Chap10/Lemma_10_70_3`;
* `Localization.tensorRightAlgEquiv` from mathlib's localization base-change API;
* `RamificationOneDvrFactorizationSituation.p` from `Situation_16_4_1`.

Owner abstraction: the blowup algebra is owned by `affineBlowupChart`, while the induced
distinguished element after base change is owned by `mappedIdealElement` and the comparison morphism
is owned by `tensorToAffineBlowupAlgebra`; the localization/tensor-source identification is owned by
`Localization.tensorRightAlgEquiv`.
Primitive data: the center ideals `S.p` and the corresponding source center ideal in a surjective
scalar tower `B → A → Λ`, together with the chosen uniformizer images inside them.
Derived API: the localized and surjective base-change comparison maps, and their kernel
descriptions from Lemma `10.70.3`.

Source/core/bridge triage:
* `source-facing`: the localization and surjective base-change statements for the Néron blowup;
* `core/canonical`: `affineBlowupChart`, `mappedIdealElement`, `tensorToAffineBlowupAlgebra`,
  `Localization.tensorRightAlgEquiv`;
* `bridge/view`: `localizedPhi`, `localizedAffineBlowupComparison`.
-/

variable (S : RamificationOneDvrFactorizationSituation)

variable {S}

-- Proof sketch: a uniformizer `π` generates the maximal ideal of the DVR `R`, hence its image in
-- `Λ` lies in `maximalIdeal S.L` because the ramification index is `1`. By the definition of
-- `S.p`, the image of `π` in `A` therefore belongs to `S.p`.
/-- A chosen uniformizer of `R` maps into the ideal `𝔭 ⊆ A`. -/
theorem algebraMap_uniformizer_mem_p {π : S.R} (hπ : Irreducible π) :
    algebraMap S.R S.A π ∈ S.p := sorry

/-- The image of a chosen uniformizer `π` viewed as an element of the ideal `𝔭 ⊆ A`. -/
noncomputable def neronBlowupParameter (π : S.R) (hπ : Irreducible π) : S.p :=
  ⟨algebraMap S.R S.A π, algebraMap_uniformizer_mem_p hπ⟩

-- Proof sketch: membership in `S.p` is equivalent to membership of `φ(a)` in the maximal ideal of
-- `Λ`; in a local ring, an element outside the maximal ideal is a unit.
/-- If `a ∉ 𝔭`, then its image in `Λ` is a unit. -/
theorem phi_a_isUnit_of_not_mem_p (a : S.A) (ha : a ∉ S.p) :
    IsUnit (S.phi a) := sorry

-- Proof sketch: every element of `Submonoid.powers a` is a power `a^n`, and powers of a unit are
-- units. Apply `phi_a_isUnit_of_not_mem_p` to `a` and raise the resulting unit to the relevant
-- power.
/-- Every power of an element outside `𝔭` maps to a unit in `Λ`. -/
theorem phi_powers_isUnit_of_not_mem_p (a : S.A) (ha : a ∉ S.p) (y : Submonoid.powers a) :
    IsUnit (S.phi y) := sorry

/-- The induced `A`-algebra factorization map `A_a → Λ` when `a ∉ 𝔭`. -/
noncomputable def localizedPhi (a : S.A) (ha : a ∉ S.p) :
    Localization.Away a →ₐ[S.A] S.L :=
  let φ : S.A →ₐ[S.A] S.L := Algebra.ofId S.A S.L
  have hφ : ∀ y : Submonoid.powers a, IsUnit (φ y) := by
    simpa using phi_powers_isUnit_of_not_mem_p a ha
  IsLocalization.liftAlgHom hφ

-- Proof sketch: compare membership in the comap ideal defining the localized factorization with
-- membership in `S.p` via `mem_p_iff`, then use the explicit formula for the lifted map
-- `localizedPhi`.
/-- The ideal defining the localized Néron blowup is the extension of `𝔭` to `A_a`. -/
theorem localizedNeronBlowupIdeal_eq_map (a : S.A) (ha : a ∉ S.p) :
    Ideal.comap (localizedPhi a ha).toRingHom (maximalIdeal S.L) =
      Ideal.map (algebraMap S.A (Localization.Away a)) S.p := sorry

/-- The image of a chosen uniformizer `π` viewed as an element of the localized center ideal
`localizedPhi⁻¹(\mathfrak m_Λ) ⊆ A_a`. -/
noncomputable def localizedNeronBlowupParameter
    (π : S.R) (hπ : Irreducible π) (a : S.A) (ha : a ∉ S.p) :
    Ideal.comap (localizedPhi a ha).toRingHom (maximalIdeal S.L) := by
  rw [localizedNeronBlowupIdeal_eq_map a ha]
  exact mappedIdealElement S.p (neronBlowupParameter π hπ)

private theorem localizedNeronBlowupSourceSubmonoid_eq
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Algebra.algebraMapSubmonoid
        (affineBlowupChart S.p (neronBlowupParameter π hπ)) (Submonoid.powers a) =
      Submonoid.powers
        ((algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) a) :=
  @Algebra.algebraMapSubmonoid_powers S.A _ (affineBlowupChart S.p (neronBlowupParameter π hπ))
    _ _ a

private noncomputable abbrev localizedNeronBlowupSourceAwayAlgebra
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Algebra (Localization.Away a)
      (Localization.Away
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a)) :=
  (Localization.awayMapₐ
    (Algebra.ofId S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) a).toAlgebra

attribute [instance] localizedNeronBlowupSourceAwayAlgebra

/-- The underlying ring equivalence identifying the tensor-product source in Lemma `10.70.3` with
the localization `A'_a` of the Néron blowup `A'`. -/
private noncomputable def localizedNeronBlowupSourceRingEquiv
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ) ≃+*
      Localization.Away
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a) := by
  delta Localization.Away
  exact Eq.mp
    (by rw [localizedNeronBlowupSourceSubmonoid_eq π hπ a])
    (Localization.tensorRightAlgEquiv (Submonoid.powers a)
      (affineBlowupChart S.p (neronBlowupParameter π hπ))).toRingEquiv

/-- The underlying ring equivalence `localizedNeronBlowupSourceRingEquiv` is compatible with the
`A_a`-algebra structures. -/
private theorem localizedNeronBlowupSourceRingEquiv_commutes
    (π : S.R) (hπ : Irreducible π) (a : S.A) (x : Localization.Away a) :
    localizedNeronBlowupSourceRingEquiv π hπ a
        (algebraMap (Localization.Away a)
          (Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ)) x) =
      algebraMap (Localization.Away a)
        (Localization.Away
          (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a)) x := by
  sorry

/-- The canonical identification of the tensor-product source in Lemma `10.70.3` with the
localization `A'_a` of the Néron blowup `A'`. -/
private noncomputable def localizedNeronBlowupSourceEquiv
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ) ≃ₐ[Localization.Away a]
      Localization.Away
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a) :=
  @AlgEquiv.ofRingEquiv
    (Localization.Away a)
    (Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ))
    (Localization.Away
      (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a))
    inferInstance inferInstance inferInstance
    Algebra.TensorProduct.leftAlgebra (localizedNeronBlowupSourceAwayAlgebra π hπ a)
    (localizedNeronBlowupSourceRingEquiv π hπ a)
    (localizedNeronBlowupSourceRingEquiv_commutes π hπ a)

/-- The canonical affine-blowup comparison map from the localization `A'_a` of the blowup chart of
`A` to the blowup chart of the extended ideal on `A_a`. -/
noncomputable def localizedAffineBlowupComparison
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Localization.Away
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a) →ₐ[Localization.Away a]
      affineBlowupChart
        (Ideal.map (algebraMap S.A (Localization.Away a)) S.p)
        (mappedIdealElement S.p (neronBlowupParameter π hπ)) :=
  (tensorToAffineBlowupAlgebra
      (Localization.Away a) S.p (neronBlowupParameter π hπ)).comp
    (localizedNeronBlowupSourceEquiv π hπ a).symm.toAlgHom

/-- Under the canonical source equivalence, the image of the Néron blowup parameter `π` in the
tensor-product source identifies with its image in the localized source `A'_a`. -/
private theorem localizedNeronBlowupSourceEquiv_algebraMap_uniformizer
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    localizedNeronBlowupSourceEquiv π hπ a
        (algebraMap S.R
          (Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ)) π) =
      algebraMap S.R
        (Localization.Away
          (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a)) π := by
  sorry

/-- Bridge to Lemma `10.70.3`: the canonical affine-blowup comparison map is surjective and its
kernel is the `π`-power torsion on the localized source `A'_a`. -/
theorem localizedAffineBlowupComparison_surjective_and_ker_eq_pi_power_torsion
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Function.Surjective (localizedAffineBlowupComparison π hπ a) ∧
      ∀ x :
          Localization.Away
            (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a),
        x ∈ RingHom.ker (localizedAffineBlowupComparison π hπ a).toRingHom ↔
          ∃ n : ℕ,
            (algebraMap S.R
              (Localization.Away
                (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a)) π) ^ n *
              x = 0 := by
  sorry

/-- The canonical affine-blowup comparison map is bijective. -/
theorem localizedAffineBlowupComparison_bijective
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Function.Bijective (localizedAffineBlowupComparison π hπ a) := by
  sorry

/-- Lemma 16.4.2 (1): if `a ∉ 𝔭`, then the affine Néron blowup of the localized factorization
`A_a → Λ` has center ideal `Ideal.map (algebraMap S.A (Localization.Away a)) S.p`, and the
corresponding affine blowup chart is canonically the localization `A'_a` of the Néron blowup
`A'`. -/
noncomputable def neronBlowup_localization_baseChange
    (π : S.R) (hπ : Irreducible π) (a : S.A) (ha : a ∉ S.p) :
    affineBlowupChart
        (Ideal.map (algebraMap S.A (Localization.Away a)) S.p)
        (mappedIdealElement S.p (neronBlowupParameter π hπ)) ≃ₐ[Localization.Away a]
      Localization.Away
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a) := by
  let _ := localizedNeronBlowupIdeal_eq_map a ha
  exact
    (AlgEquiv.ofBijective
        (localizedAffineBlowupComparison π hπ a)
        (localizedAffineBlowupComparison_bijective π hπ a)).symm

section Surjection

section SurjectiveBaseChange

variable (S)
variable (B : Type x) [CommRing B] [Algebra S.R B] [Algebra B S.A] [IsScalarTower S.R B S.A]

/-- The canonical source map `B → Λ` induced by the scalar tower `R → B → A` and the factorization
map `φ : A → Λ`. -/
abbrev sourcePhi : B →ₐ[S.R] S.L :=
  S.phi.comp (IsScalarTower.toAlgHom S.R B S.A)

/-- The ideal `𝔭_B ⊆ B` attached to the canonical source factorization `B → A → Λ`. -/
def sourceP : Ideal B :=
  Ideal.comap (sourcePhi S B).toRingHom (maximalIdeal S.L)

-- Proof sketch: the same ramification-index-one argument as for `A` shows that the image of a
-- uniformizer `π` of `R` lands in the inverse image of `maximalIdeal Λ` under the canonical map
-- `B → A → Λ`.
/-- A chosen uniformizer of `R` maps into the ideal `𝔭_B ⊆ B`. -/
theorem source_uniformizer_mem_p {π : S.R} (hπ : Irreducible π) :
    algebraMap S.R B π ∈ sourceP S B := sorry

/-- The image of a chosen uniformizer `π` viewed as an element of the ideal `𝔭_B ⊆ B`. -/
noncomputable def sourceNeronBlowupParameter (π : S.R) (hπ : Irreducible π) :
    sourceP S B :=
  ⟨algebraMap S.R B π, source_uniformizer_mem_p S B hπ⟩

-- Proof sketch: compare the defining comap ideals of `𝔭_B` and `S.p` using the canonical
-- composite `B → A → Λ`; after pushing forward along `algebraMap B S.A`, the two descriptions
-- agree.
/-- The ideal defining the Néron blowup of `A` is the image of the corresponding ideal of `B`. -/
theorem mapped_sourceP_eq_targetP
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    Ideal.map (algebraMap B S.A) (sourceP S B) = S.p := sorry

-- Proof sketch: specialize Lemma `10.70.3` to the surjective scalar-tower map `B → A`. The
-- canonical base-change morphism is exactly `tensorToAffineBlowupAlgebra`, and the distinguished
-- source element is the ambient `algebraMap` image of `π`.
/- Lemma 16.4.2 (2): if the canonical map `B → A` in the scalar tower is surjective, then the
center ideal of `A` is the image of the center ideal of `B`, and the canonical comparison map from
`A ⊗[B] B'` to `A'` is surjective with kernel equal to the `π`-power torsion; equivalently, `A'`
is the quotient of `A ⊗[B] B'` by its `π`-power torsion. -/
theorem neronBlowup_surjection_baseChange_surjective_with_ker_awayTorsion
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A))
    (π : S.R) (hπ : Irreducible π) :
    Ideal.map (algebraMap B S.A) (sourceP S B) = S.p ∧
      let A' :=
        S.A ⊗[B] affineBlowupChart
          (sourceP S B)
          (sourceNeronBlowupParameter S B π hπ)
      let φ := tensorToAffineBlowupAlgebra S.A (sourceP S B) (sourceNeronBlowupParameter S B π hπ)
      let πA : A' := algebraMap B A' (algebraMap S.R B π)
      Function.Surjective φ ∧
        ∀ x : A', x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, πA ^ n * x = 0 := by
  refine ⟨mapped_sourceP_eq_targetP S B hf, ?_⟩
  let A' :=
    S.A ⊗[B] affineBlowupChart
      (sourceP S B)
      (sourceNeronBlowupParameter S B π hπ)
  let φ := tensorToAffineBlowupAlgebra S.A (sourceP S B) (sourceNeronBlowupParameter S B π hπ)
  let πA : A' := algebraMap B A' (algebraMap S.R B π)
  change Function.Surjective φ ∧
    ∀ x : A', x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, πA ^ n * x = 0
  simpa [A', φ, πA, sourceNeronBlowupParameter] using
    affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
      S.A
      (sourceP S B)
      (sourceNeronBlowupParameter S B π hπ)

end SurjectiveBaseChange

end Surjection

end
