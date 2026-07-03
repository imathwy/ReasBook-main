import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_4_2 (from Chap16) -/
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

/-! ### Lemma_16_4_3 (from Chap16) -/
open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped TensorProduct

universe u v w

section

variable (S : RamificationOneDvrFactorizationSituation)

/-- The transform of the center prime `𝔭` inside the Néron blowup `A'`. This is the principal-open
library-facing stand-in for the local prime `𝔭'` appearing in the textbook statement. -/
noncomputable def neronBlowupCenterIdeal (π : S.R) (hπ : Irreducible π) :
    Ideal (affineBlowupChart S.p (neronBlowupParameter π hπ)) :=
  Ideal.map (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) S.p

/-- The local special fiber `(A / π A)_𝔭`, written in the canonical quotient-after-localization
form. -/
abbrev specialFiberLocalRing (π : S.R) :=
  Localization.AtPrime S.p ⧸
    Ideal.span
      ({algebraMap S.A (Localization.AtPrime S.p) (algebraMap S.R S.A π)} :
        Set (Localization.AtPrime S.p))

/-- The dimension `c = dim ((A / π A)_𝔭)` from Lemma `16.4.3`, expressed via Krull dimension. -/
noncomputable abbrev specialFiberLocalDimension (π : S.R) : WithBot ℕ∞ :=
  ringKrullDim (specialFiberLocalRing S π)

/-- The principal-open form of the short exact sequence of Kähler differentials in
Lemma `16.4.3`. In this statement-stage skeleton, this predicate records the rank parameter
`c = dim ((A / π A)_𝔭)` attached to the cokernel of the eventual short exact sequence on a
principal open of the Néron blowup. -/
def HasNeronBlowupPrincipalOpenDifferentialSequence
    (π : S.R) (hπ : Irreducible π)
    (_ : affineBlowupChart S.p (neronBlowupParameter π hπ)) : Prop :=
  ∃ c : ℕ,
    (c : WithBot ℕ∞) = specialFiberLocalDimension S π

/-- A principal open of the Néron blowup carrying both the smoothness conclusion and the
auxiliary differential-sequence clause from Lemma `16.4.3`. -/
private abbrev NeronBlowupPrincipalOpenWitness
    (π : S.R) (hπ : Irreducible π)
    (g : affineBlowupChart S.p (neronBlowupParameter π hπ)) : Prop :=
  Algebra.Smooth S.R (Localization.Away g) ∧
    HasNeronBlowupPrincipalOpenDifferentialSequence S π hπ g

variable {S}

-- Proof sketch: use Lemma `16.4.2` to replace `A` by a localization away from `𝔭`, choose a
-- regular system of parameters in the special fiber `(A / π A)_𝔭`, and present the Néron blowup
-- as the quotient `A[y₁, …, y_c] / (π y_i - g_i)`. The Jacobi-Zariski sequence on a suitable
-- principal open of `A'` gives the displayed exact sequence, and the linear independence of the
-- differentials `dg_i` over the separable residue extension forces injectivity on the left and
-- smoothness on that principal open.
/-- Lemma 16.4.3: in Situation `16.4.1`, if `R → A` is smooth at `𝔭` and the special-fiber field
extension `R / πR ⊆ Λ / πΛ` is separable, then the Néron blowup `A'` is smooth at the center
lying over `𝔭`. In the canonical principal-open formulation, there exists `g ∉ 𝔭 A'` such that
`A'_g` is smooth over `R`; the differential-sequence clause is recorded in this statement-stage
skeleton by the auxiliary proposition
`HasNeronBlowupPrincipalOpenDifferentialSequence S π g`, whose rank parameter is constrained to be
`c = dim ((A / π A)_𝔭)`. -/
theorem smoothAway_center_of_separable_specialFiber_and_hasDifferentialSequence
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth : Algebra.IsSmoothAt S.R S.p) :
    ∃ g : affineBlowupChart S.p (neronBlowupParameter π hπ),
      g ∉ neronBlowupCenterIdeal S π hπ ∧
        NeronBlowupPrincipalOpenWitness S π hπ g := sorry

end

/-! ### Lemma_16_4_4 (from Chap16) -/
open scoped TensorProduct
open Algebra IsLocalRing
open RamificationOneDvrFactorizationSituation

universe u x

noncomputable section

section

/-
Domain-style sampling pass for Lemma 16.4.4.

Primary domain: source-facing smoothness at prime-spectrum points in a DVR factorization
situation, together with the cotangent module `Ω[A⁄R]` after base change to `Λ`.

Sampled owner declarations:
* `Algebra.SmoothAtPrime`;
* `Algebra.smoothAtPrime_iff_isSmoothAt`;
* `RamificationOneDvrFactorizationSituation.q`;
* `RamificationOneDvrFactorizationSituation.p`;
* `PrimeSpectrum.comap`.

Best owner abstraction: the chapter’s source-facing smoothness owner is
`Algebra.SmoothAtPrime` on prime-spectrum points. The factorization data are already owned by
`RamificationOneDvrFactorizationSituation`; the ideals `S.q` and `S.p` are derived from that
owner, the points of `Spec(S.A)` are canonically `⟨S.q, inferInstance⟩` and `⟨S.p, inferInstance⟩`,
and the pullback point of `Spec(B)` is canonically
`PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`. The local predicate `IsSmoothAt` is only a
proof bridge via `smoothAtPrime_iff_isSmoothAt`.

Primitive-vs-derived split:
* primitive data: `S : RamificationOneDvrFactorizationSituation` and the explicit surjection
  `ψ : B →ₐ[S.R] S.A`;
* derived API: the induced `S.A`-algebra structure on `S.L`, the scalar tower `S.R → S.A → S.L`,
  the ideals `S.q` and `S.p`, the corresponding points `⟨S.q, inferInstance⟩` and
  `⟨S.p, inferInstance⟩`, and the pullback point
  `PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`.

Source/core/bridge triage:
* `source-facing`: the smoothness statement at the points `⟨S.q, inferInstance⟩`,
  `⟨S.p, inferInstance⟩`, and `PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩`;
* `core/canonical`: `RamificationOneDvrFactorizationSituation`, `S.q`, `S.p`,
  `Algebra.SmoothAtPrime`, and `PrimeSpectrum.comap`;
* `bridge/view`: the local formal-smoothness criterion `smoothAtPrime_iff_isSmoothAt`.
-/

variable (S : RamificationOneDvrFactorizationSituation)

-- Proof sketch: use the exact conormal sequence for the surjection `B ↠ A` to identify the source
-- cokernel hypothesis with freeness of `S.L ⊗[S.A] Ω[S.A⁄S.R]`. Smoothness at `S.q` gives
-- freeness of the differential module at the generic point with rank equal to the relative
-- dimension there; flatness of `S.A` over `S.R` compares the fiber dimensions at `S.q` and at
-- `S.p`. Then rewrite through `smoothAtPrime_iff_isSmoothAt` and apply the local cotangent-space
-- criterion for smoothness at `S.p`.
/-- Lemma 16.4.4: let `S : RamificationOneDvrFactorizationSituation`, so `φ : A → Λ` is the
factorization map with `𝔮 = ker(φ)` and `𝔭 = φ⁻¹(\mathfrak m_Λ)`. Let `ψ : B →ₐ[S.R] S.A` be a
surjective `R`-algebra map, formalized as `Function.Surjective ψ`. Assume `R → A` is smooth at
`𝔮`, formalized as `Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩`; assume `R → B` is smooth
at the pullback of `𝔭`, formalized as
`Algebra.SmoothAtPrime S.R B (PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩)`; and assume
the canonical cokernel hypothesis is expressed in the library-facing form that
`S.L ⊗[S.A] Ω[S.A⁄S.R]` is a free `S.L`-module. Then `R → A` is smooth at `𝔭`, formalized as
`Algebra.SmoothAtPrime S.R S.A ⟨S.p, inferInstance⟩`. -/
theorem smoothAtPrime_p_of_smoothAtPrime_q_of_source_smoothAtPrime_of_free_kaehler_baseChange
    (S : RamificationOneDvrFactorizationSituation)
    {B : Type x} [CommRing B] [Algebra S.R B]
    (ψ : B →ₐ[S.R] S.A)
    (hψ : Function.Surjective ψ)
    (hAq : Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩)
    (hB : Algebra.SmoothAtPrime S.R B (PrimeSpectrum.comap ψ.toRingHom ⟨S.p, inferInstance⟩))
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Algebra.SmoothAtPrime S.R S.A ⟨S.p, inferInstance⟩ := sorry

end

/-! ### Lemma_16_4_5 (from Chap16) -/
open RamificationOneDvrFactorizationSituation

universe u v w

section

/-- A coarse statement-stage witness identifying `T` with one affine Néron blowup step of the
factorization situation `S`: the base and target DVRs are unchanged up to ring equivalence, and
the intermediate algebra of `T` is identified with the affine Néron blowup algebra attached to
`S`. -/
structure AffineNeronBlowupStepWitness
    (S T : RamificationOneDvrFactorizationSituation) where
  /-- The chosen parameter along which the affine Néron blowup is formed. -/
  parameter : S.R
  /-- The chosen parameter is a uniformizer candidate. -/
  parameter_irreducible : Irreducible parameter
  /-- The next stage has the same base DVR as the previous one, up to ring equivalence. -/
  baseRingEquiv : T.R ≃+* S.R
  /-- The next stage has the same target DVR as the previous one, up to ring equivalence. -/
  targetRingEquiv : T.L ≃+* S.L
  /-- The intermediate algebra of the next stage is the affine Néron blowup algebra of the
  previous stage. -/
  blowupAlgebraEquiv : T.A ≃+*
    affineBlowupChart S.p (neronBlowupParameter parameter parameter_irreducible)

/-- A finite tower of affine Néron blowups starting from `S` and ending at a stage smooth at its
center prime. -/
structure FiniteAffineNeronBlowupTower (S : RamificationOneDvrFactorizationSituation) where
  /-- The number of affine Néron blowup steps in the tower. -/
  length : ℕ
  /-- The factorization situations occurring in the tower. -/
  stages : Fin (length + 1) → RamificationOneDvrFactorizationSituation
  /-- The initial stage of the tower is the given situation `S`. -/
  start_eq : stages 0 = S
  /-- Each consecutive pair of stages is related by one affine Néron blowup step. -/
  step :
    ∀ i : Fin length, AffineNeronBlowupStepWitness (stages i.castSucc) (stages i.succ)
  /-- The terminal stage of the tower is smooth at its center prime. -/
  final_smooth :
    Algebra.SmoothAtPrime
      (stages (Fin.last length)).R
      (stages (Fin.last length)).A
      ⟨(stages (Fin.last length)).p, inferInstance⟩

variable (S : RamificationOneDvrFactorizationSituation)

-- Proof sketch: iterate the defect-reduction argument of Lemma `16.4.5`. Lemma `16.4.4` handles
-- the zero-defect case, while the Néron blowup comparison from Lemmas `16.4.2` and `16.4.3`
-- preserves the setup and decreases the torsion defect by at least `1` whenever the center is not
-- yet smooth. Since the defect is a natural number, the process terminates after finitely many
-- affine Néron blowups.
/-- Lemma 16.4.5: in Situation `16.4.1`, assume `R → A` is smooth at `𝔮 = ker(φ)`, formalized as
`Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩`, and that the special-fiber extension
`R / πR ⊆ Λ / πΛ` is separable. Then after finitely many affine Néron blowups one reaches a
factorization situation whose intermediate algebra is smooth over `R` at the center prime over
`𝔭`. In this statement-stage formalization, the finite sequence of blowups is recorded by
`FiniteAffineNeronBlowupTower S`. -/
theorem exists_finite_affine_neron_blowup_tower_with_smooth_center
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth_q : Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩) :
    Nonempty (FiniteAffineNeronBlowupTower S) := sorry

end

/-! ### Lemma_16_4_6 (from Chap16) -/
open IsLocalRing

universe u

namespace Algebra

section

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
variable [Algebra R Λ] [_root_.IsExtensionOfDiscreteValuationRings R Λ]

-- Proof sketch: by Lemma `10.127.4`, it is enough to factor every finite-presentation
-- `R`-algebra map `A → Λ` through a smooth `R`-algebra. Replace `A` by its image in `Λ` so that
-- `A` is a domain inside `FractionRing Λ`; the assumed separability of `FractionRing Λ` over
-- `FractionRing R` and Lemma `10.140.9` make `R → A` smooth at the generic point. Lemma `16.4.5`
-- then yields, after finitely many Néron blowups, a stage smooth at the center over the closed
-- point, and localizing away from that center gives the required smooth factorization through
-- `Λ`.
/-- Lemma 16.4.6: let `R ⊂ Λ` be an extension of discrete valuation rings with ramification index
`1`. If the induced extension of residue fields is separable and the induced extension of
fraction fields is separable in the Stacks Project sense, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_ramificationIndexOne_dvrExtension
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    [Algebra.IsSeparable (ResidueField R) (ResidueField Λ)]
    [IsSeparableOver (FractionRing R) (FractionRing Λ)] :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
