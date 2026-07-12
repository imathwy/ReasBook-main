import Mathlib
import StacksProject_2024.Chap10.Lemma_10_70_2
import StacksProject_2024.Chap10.Lemma_10_70_3
import StacksProject_2024.Chap16.Situation_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped AffineBlowupChart TensorProduct

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
* `bridge/view`: the localized factorization and comparison maps used to identify the localized
  Néron blowup with the canonical base-change chart.
-/

variable (S : RamificationOneDvrFactorizationSituation)

variable {S}

-- Proof sketch: a uniformizer `π` generates the maximal ideal of the DVR `R`, hence its image in
-- `Λ` lies in `maximalIdeal S.L` because the ramification index is `1`. By the definition of
-- `S.p`, the image of `π` in `A` therefore belongs to `S.p`.
private theorem algebraMap_uniformizer_mem_p {π : S.R} (hπ : Irreducible π) :
    algebraMap S.R S.A π ∈ S.p := by
  -- An irreducible element of the DVR is a nonunit, hence it lies in the maximal ideal.
  have hπmax : π ∈ maximalIdeal S.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (irreducible_iff.mp hπ).1
  -- The image of `maximalIdeal R` is contained in the center ideal `𝔭`.
  exact S.map_maximalIdeal_le_p <| Ideal.mem_map_of_mem _ hπmax

/-- The image of a chosen uniformizer `π` viewed as an element of the ideal `𝔭 ⊆ A`. -/
noncomputable def neronBlowupParameter (π : S.R) (hπ : Irreducible π) : S.p :=
  ⟨algebraMap S.R S.A π, algebraMap_uniformizer_mem_p hπ⟩

-- Proof sketch: membership in `S.p` is equivalent to membership of `φ(a)` in the maximal ideal of
-- `Λ`; in a local ring, an element outside the maximal ideal is a unit.
private theorem phi_a_isUnit_of_not_mem_p (a : S.A) (ha : a ∉ S.p) :
    IsUnit (S.phi a) := by
  classical
  -- Route correction: prove unitality by contradiction from the local-ring characterization of
  -- the maximal ideal, rather than trying to extract a unit directly from `ha`.
  by_contra hunit
  apply ha
  rw [S.mem_p_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hunit

-- Proof sketch: every element of `Submonoid.powers a` is a power `a^n`, and powers of a unit are
-- units. Apply `phi_a_isUnit_of_not_mem_p` to `a` and raise the resulting unit to the relevant
-- power.
private theorem phi_powers_isUnit_of_not_mem_p (a : S.A) (ha : a ∉ S.p)
    (y : Submonoid.powers a) :
    IsUnit (S.phi y) := by
  -- Every element of `Submonoid.powers a` is some `a^n`, and powers of a unit remain units.
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨n, rfl⟩
  simpa [map_pow] using (phi_a_isUnit_of_not_mem_p a ha).pow n

/-- The induced `A`-algebra factorization map `A_a → Λ` when `a ∉ 𝔭`. -/
noncomputable def neronBlowupLocalizationFactorization (a : S.A) (ha : a ∉ S.p) :
    Localization.Away a →ₐ[S.A] S.L :=
  let φ : S.A →ₐ[S.A] S.L := Algebra.ofId S.A S.L
  have hφ : ∀ y : Submonoid.powers a, IsUnit (φ y) := by
    simpa using phi_powers_isUnit_of_not_mem_p a ha
  IsLocalization.liftAlgHom hφ

/-- The center ideal of the localized factorization `A_a → Λ`. -/
noncomputable def neronBlowupLocalizationCenterIdeal (a : S.A) (ha : a ∉ S.p) :
    Ideal (Localization.Away a) :=
  Ideal.comap (neronBlowupLocalizationFactorization a ha).toRingHom (maximalIdeal S.L)

-- Proof sketch: compare membership in the comap ideal defining the localized factorization with
-- membership in `S.p` via `mem_p_iff`, then use the explicit formula for the lifted map
-- `localizedFactorizationMap`.
/-- The center ideal of the localized factorization is the extension of `𝔭` to `A_a`. -/
theorem neronBlowup_localization_centerIdeal_eq_map (a : S.A) (ha : a ∉ S.p) :
    neronBlowupLocalizationCenterIdeal a ha =
      Ideal.map (algebraMap S.A (Localization.Away a)) S.p := by
  ext z
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers a) z
  have hp : S.p.IsPrime := inferInstance
  have hxy :
      S.phi x =
        S.phi y *
          neronBlowupLocalizationFactorization a ha
            (IsLocalization.mk' (Localization.Away a) x y) := by
    -- Compute the localized factorization on the fraction `x / y`.
    rw [neronBlowupLocalizationFactorization, IsLocalization.liftAlgHom_apply]
    simpa [RingHom.algebraMap_toAlgebra] using
      (IsLocalization.lift_mk'_spec
        (M := Submonoid.powers a)
        (S := Localization.Away a)
        (g := Algebra.ofId S.A S.L)
        (hg := by
          simpa [RingHom.algebraMap_toAlgebra] using phi_powers_isUnit_of_not_mem_p a ha)
        x
        (neronBlowupLocalizationFactorization a ha
          (IsLocalization.mk' (Localization.Away a) x y))
        y).mp rfl
  constructor
  · intro hz
    rw [neronBlowupLocalizationCenterIdeal, Ideal.mem_comap] at hz
    have hxmax : S.phi x ∈ maximalIdeal S.L := by
      rw [hxy]
      exact Ideal.mul_mem_left _ _ hz
    have hxp : x ∈ S.p := by
      exact (S.mem_p_iff).mpr hxmax
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨1, by simp, ?_⟩
    simpa using hxp
  · intro hz
    rw [IsLocalization.mk'_mem_map_algebraMap_iff] at hz
    rcases hz with ⟨s, hs, hsx⟩
    have hsnot : (s : S.A) ∉ S.p := by
      rcases hs with ⟨n, rfl⟩
      intro hs'
      exact ha (hp.mem_of_pow_mem _ hs')
    have hxp : x ∈ S.p := by
      exact (hp.mem_or_mem hsx).resolve_left hsnot
    have hxmax : S.phi x ∈ maximalIdeal S.L := by
      exact (S.mem_p_iff).mp hxp
    rw [neronBlowupLocalizationCenterIdeal, Ideal.mem_comap]
    rw [hxy] at hxmax
    exact (Ideal.unit_mul_mem_iff_mem (maximalIdeal S.L)
      (phi_powers_isUnit_of_not_mem_p a ha y)).mp hxmax

/-- Helper for Lemma 16.4.2: the localized image of `π` belongs to the localized center ideal. -/
private theorem neronBlowupLocalizationCenterParameter_mem
    (π : S.R) (hπ : Irreducible π) (a : S.A) (ha : a ∉ S.p) :
    algebraMap S.R (Localization.Away a) π ∈ neronBlowupLocalizationCenterIdeal a ha := by
  rw [neronBlowup_localization_centerIdeal_eq_map (S := S) a ha]
  exact Ideal.mem_map_of_mem (algebraMap S.A (Localization.Away a))
    (algebraMap_uniformizer_mem_p hπ)

/-- The image of a chosen uniformizer `π` viewed as an element of the localized center ideal
`(neronBlowupLocalizationFactorization a ha)⁻¹(\mathfrak m_Λ) ⊆ A_a`. -/
noncomputable def neronBlowupLocalizationCenterParameter
    (π : S.R) (hπ : Irreducible π) (a : S.A) (ha : a ∉ S.p) :
    neronBlowupLocalizationCenterIdeal a ha :=
  ⟨algebraMap S.R (Localization.Away a) π,
    neronBlowupLocalizationCenterParameter_mem (S := S) π hπ a ha⟩

/-- Helper for Lemma 16.4.2: the tensor-product source ring appearing before localizing the Néron
blowup chart away from `a`. -/
private abbrev localizedNeronBlowupSource
    (π : S.R) (hπ : Irreducible π) (a : S.A) :=
  Localization.Away a ⊗[S.A] affineBlowupChart S.p (neronBlowupParameter π hπ)

/-- Helper for Lemma 16.4.2: the localization of the Néron blowup chart away from the image of
`a`. -/
private abbrev localizedNeronBlowupTarget
    (π : S.R) (hπ : Irreducible π) (a : S.A) :=
  Localization.Away
    (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a)

private theorem localizedNeronBlowupSourceSubmonoid_eq
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Algebra.algebraMapSubmonoid
        (affineBlowupChart S.p (neronBlowupParameter π hπ)) (Submonoid.powers a) =
      Submonoid.powers
        (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ)) a) :=
  @Algebra.algebraMapSubmonoid_powers S.A _ (affineBlowupChart S.p (neronBlowupParameter π hπ))
    _ _ a

private noncomputable abbrev localizedNeronBlowupSourceAwayAlgebra
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a) :=
  (Localization.awayMapₐ
    (Algebra.ofId S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) a).toAlgebra

/-- Helper for Lemma 16.4.2: the localization `A'_a` carries its canonical `A_a`-algebra
structure induced by localizing the blowup chart away from `a`. -/
private noncomputable instance localizedNeronBlowupTargetAwayAlgebra
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a) :=
  localizedNeronBlowupSourceAwayAlgebra (S := S) π hπ a

/-- Helper for Lemma 16.4.2: the canonical `A_a`-algebra structure on `A'_a` supplies the scalar
action needed by the localization comparison maps. -/
private noncomputable instance localizedNeronBlowupTargetAwaySMul
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    SMul (Localization.Away a) (localizedNeronBlowupTarget π hπ a) :=
  (localizedNeronBlowupTargetAwayAlgebra (S := S) π hπ a).toSMul

/-- Helper for Lemma 16.4.2: on the localized blowup chart, the direct `R`-algebra structure
agrees with first mapping into `A_a` and then using the canonical away map `A_a → A'_a`. -/
private theorem localizedNeronBlowupTargetAway_algebraMap_eq
    (π : S.R) (hπ : Irreducible π) (a : S.A) (x : S.R) :
    algebraMap S.R (localizedNeronBlowupTarget π hπ a) x =
      algebraMap (Localization.Away a) (localizedNeronBlowupTarget π hπ a)
        (algebraMap S.R (Localization.Away a) x) := by
  -- First rewrite the target `R`-algebra map through `A'`, then through the owner away map.
  calc
    algebraMap S.R (localizedNeronBlowupTarget π hπ a) x =
        algebraMap (affineBlowupChart S.p (neronBlowupParameter π hπ))
          (localizedNeronBlowupTarget π hπ a)
          (algebraMap S.R (affineBlowupChart S.p (neronBlowupParameter π hπ)) x) := by
            rfl
    _ =
        algebraMap (Localization.Away a) (localizedNeronBlowupTarget π hπ a)
          (algebraMap S.A (Localization.Away a) (algebraMap S.R S.A x)) := by
            -- The owner away map commutes with base elements of the blowup chart.
            simpa using
              ((Localization.awayMapₐ
                (Algebra.ofId S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) a).commutes
                (algebraMap S.R S.A x)).symm
    _ =
        algebraMap (Localization.Away a) (localizedNeronBlowupTarget π hπ a)
          (algebraMap S.R (Localization.Away a) x) := by
            -- Finally rewrite the source localization map through the same scalar tower.
            exact congrArg
              (algebraMap (Localization.Away a) (localizedNeronBlowupTarget π hπ a))
              ((congrArg (fun f ↦ f x)
                (IsScalarTower.algebraMap_eq S.R S.A (Localization.Away a))).symm)

/-- The canonical identification of the tensor-product source in Lemma `10.70.3` with the
localization `A'_a` of the Néron blowup `A'`. -/
private noncomputable def localizedNeronBlowupSourceEquiv
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    localizedNeronBlowupSource π hπ a ≃ₐ[Localization.Away a] localizedNeronBlowupTarget π hπ a := by
  letI : Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a) := inferInstance
  -- Route correction: use the owner `Localization.tensorRightAlgEquiv` directly after rewriting
  -- the localized submonoid, instead of rebuilding the away-localization bridge by transport.
  simpa [localizedNeronBlowupSource, localizedNeronBlowupTarget,
    localizedNeronBlowupSourceSubmonoid_eq (S := S) π hπ a] using
    (Localization.tensorRightAlgEquiv (Submonoid.powers a)
      (affineBlowupChart S.p (neronBlowupParameter π hπ)))

/-- Helper for Lemma 16.4.2: the tensor/localization equivalence sends the distinguished image of
`π` to the localized distinguished image. -/
private theorem localizedNeronBlowupSourceEquiv_map_pi
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    localizedNeronBlowupSourceEquiv π hπ a
        (algebraMap S.R
          (localizedNeronBlowupSource π hπ a) π) =
      algebraMap S.R (localizedNeronBlowupTarget π hπ a) π := by
  let e := localizedNeronBlowupSourceEquiv π hπ a
  letI : Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a) := inferInstance
  calc
    e (algebraMap S.R
        (localizedNeronBlowupSource π hπ a) π) =
      e (algebraMap (Localization.Away a)
        (localizedNeronBlowupSource π hπ a)
        (algebraMap S.R (Localization.Away a) π)) := by
          -- Rewrite the source algebra map through the scalar tower `R → A_a → A_a ⊗ A'`.
          exact congrArg (fun f ↦ e (f π))
            (IsScalarTower.algebraMap_eq S.R (Localization.Away a)
              (localizedNeronBlowupSource π hπ a))
    _ = algebraMap (Localization.Away a) (localizedNeronBlowupTarget π hπ a)
        (algebraMap S.R (Localization.Away a) π) := by
          -- The algebra equivalence commutes with the `A_a`-algebra map.
          simpa [e] using e.commutes (algebraMap S.R (Localization.Away a) π)
    _ = algebraMap S.R (localizedNeronBlowupTarget π hπ a) π := by
          -- Rewrite the target algebra map through the canonical away-map compatibility.
          exact (localizedNeronBlowupTargetAway_algebraMap_eq (S := S) π hπ a π).symm

/-- Helper for Lemma 16.4.2: transporting a `π^n`-torsion relation across the tensor/localization
equivalence only rewrites the distinguished element. -/
private theorem localizedNeronBlowupSourceEquiv_map_pi_pow_mul
    (π : S.R) (hπ : Irreducible π) (a : S.A) (n : ℕ)
    (x : localizedNeronBlowupSource π hπ a) :
    localizedNeronBlowupSourceEquiv π hπ a
        ((algebraMap S.R
            (localizedNeronBlowupSource π hπ a) π) ^ n *
          x) =
      (algebraMap S.R (localizedNeronBlowupTarget π hπ a) π) ^ n *
        localizedNeronBlowupSourceEquiv π hπ a x :=
by
  let e := localizedNeronBlowupSourceEquiv π hπ a
  -- Once the distinguished image of `π` matches across the equivalence, multiplicativity
  -- transports the entire `π^n`-torsion relation.
  calc
    e (((algebraMap S.R (localizedNeronBlowupSource π hπ a) π) ^ n) * x) =
        e ((algebraMap S.R (localizedNeronBlowupSource π hπ a) π) ^ n) * e x := by
          rw [map_mul]
    _ =
        (e (algebraMap S.R (localizedNeronBlowupSource π hπ a) π)) ^ n * e x := by
          rw [map_pow]
    _ =
        (algebraMap S.R (localizedNeronBlowupTarget π hπ a) π) ^ n * e x := by
          rw [localizedNeronBlowupSourceEquiv_map_pi (S := S) π hπ a]

/-- The canonical affine-blowup comparison map from the localization `A'_a` of the blowup chart of
`A` to the blowup chart of the extended ideal on `A_a`. -/
private noncomputable def localizedBlowupComparison
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    localizedNeronBlowupTarget π hπ a →ₐ[Localization.Away a]
      affineBlowupChart
        (Ideal.map (algebraMap S.A (Localization.Away a)) S.p)
        (mappedIdealElement S.p (neronBlowupParameter π hπ)) :=
  letI : Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a) :=
    localizedNeronBlowupSourceAwayAlgebra (S := S) π hπ a
  (tensorToAffineBlowupAlgebra
      (Localization.Away a) S.p (neronBlowupParameter π hπ)).comp
    (localizedNeronBlowupSourceEquiv π hπ a).symm.toAlgHom

/-- Bridge to Lemma `10.70.3`: the canonical affine-blowup comparison map is surjective and its
kernel is the `π`-power torsion on the localized source `A'_a`. -/
private theorem localizedBlowupComparison_surjective_and_ker_eq_pi_power_torsion
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Function.Surjective (localizedBlowupComparison π hπ a) ∧
      ∀ x :
          localizedNeronBlowupTarget π hπ a,
        x ∈ RingHom.ker (localizedBlowupComparison π hπ a).toRingHom ↔
          ∃ n : ℕ,
            (algebraMap S.R (localizedNeronBlowupTarget π hπ a) π) ^ n *
              x = 0 :=
by
  let e := localizedNeronBlowupSourceEquiv π hπ a
  let φ :=
    tensorToAffineBlowupAlgebra
      (Localization.Away a) S.p (neronBlowupParameter π hπ)
  let hbase :=
    affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
      (Localization.Away a) S.p (neronBlowupParameter π hπ)
  have hφsurj : Function.Surjective φ := hbase.1
  have hφker :
      ∀ z : localizedNeronBlowupSource π hπ a,
        z ∈ RingHom.ker φ.toRingHom ↔
          ∃ n : ℕ, (algebraMap S.R (localizedNeronBlowupSource π hπ a) π) ^ n * z = 0 := by
    intro z
    -- Rewrite the Chapter 10 torsion criterion into the present `π`-notation on the tensor source.
    simpa [φ, mappedIdealElement, neronBlowupParameter, IsScalarTower.algebraMap_eq] using hbase.2 z
  refine ⟨?_, ?_⟩
  · intro y
    rcases hφsurj y with ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    -- The comparison map is the base-change map precomposed with the canonical source equivalence.
    simp [localizedBlowupComparison, φ, e]
  · intro x
    constructor
    · intro hx
      have hx' : e.symm x ∈ RingHom.ker φ.toRingHom := by
        -- Pull the kernel condition back across `e.symm`.
        rw [RingHom.mem_ker] at hx ⊢
        simpa [localizedBlowupComparison, φ, e] using hx
      rcases (hφker (e.symm x)).mp hx' with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      -- Apply the equivalence to the source torsion equation to recover the target one.
      have hmap := congrArg e hn
      simpa [localizedNeronBlowupSourceEquiv_map_pi_pow_mul (S := S) π hπ a n (e.symm x)] using hmap
    · rintro ⟨n, hn⟩
      have hsourceZero :
          (algebraMap S.R (localizedNeronBlowupSource π hπ a) π) ^ n * e.symm x = 0 := by
        -- Push the target torsion equation back across `e` and use injectivity.
        apply e.injective
        simpa [localizedNeronBlowupSourceEquiv_map_pi_pow_mul (S := S) π hπ a n (e.symm x)] using hn
      have hx' : e.symm x ∈ RingHom.ker φ.toRingHom := by
        exact (hφker (e.symm x)).mpr ⟨n, hsourceZero⟩
      -- Push the kernel statement forward again to the public comparison map.
      rw [RingHom.mem_ker] at hx' ⊢
      simpa [localizedBlowupComparison, φ, e] using hx'

/-- Helper for Lemma 16.4.2: the image of `π` remains a nonzerodivisor after localizing the
Néron blowup chart away from `a`. -/
private theorem localizedNeronBlowupTarget_pi_isSMulRegular
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    IsSMulRegular (localizedNeronBlowupTarget π hπ a)
      (algebraMap S.R (localizedNeronBlowupTarget π hπ a) π) := by
  let A' := affineBlowupChart S.p (neronBlowupParameter π hπ)
  have hregA' :
      IsRegular (algebraMap S.A A' (algebraMap S.R S.A π)) := by
    -- The distinguished parameter on the affine blowup chart is already regular before
    -- localization.
    simpa [A', IsScalarTower.algebraMap_eq] using
      (affineBlowupChart_isRegular S.p (neronBlowupParameter π hπ))
  have hsmulA' :
      IsSMulRegular A' (algebraMap S.A A' (algebraMap S.R S.A π)) := by
    -- Reinterpret regularity of ring multiplication as regularity of the scalar action.
    simpa [A', smul_eq_mul, IsScalarTower.algebraMap_eq] using hregA'.isSMulRegular
  have hloc :
      IsSMulRegular (localizedNeronBlowupTarget π hπ a)
        (algebraMap A' (localizedNeronBlowupTarget π hπ a)
          (algebraMap S.A A' (algebraMap S.R S.A π))) :=
    IsSMulRegular.of_isLocalization
      (localizedNeronBlowupTarget π hπ a)
      (Submonoid.powers (algebraMap S.A A' a))
      hsmulA'
  -- The localized `R`-algebra map is the same element viewed through the scalar tower
  -- `R → A → A' → A'_a`.
  simpa [A', IsScalarTower.algebraMap_eq] using hloc

/-- The canonical affine-blowup comparison map is bijective. -/
private theorem localizedBlowupComparison_bijective
    (π : S.R) (hπ : Irreducible π) (a : S.A) :
    Function.Bijective (localizedBlowupComparison π hπ a) :=
by
  rcases localizedBlowupComparison_surjective_and_ker_eq_pi_power_torsion
      (S := S) π hπ a with ⟨hsurj, hker⟩
  refine ⟨?_, hsurj⟩
  intro x y hxy
  have hxyKer : x - y ∈ RingHom.ker (localizedBlowupComparison π hπ a).toRingHom := by
    -- Equal images imply that the difference lands in the kernel.
    rw [RingHom.mem_ker]
    simp [map_sub, hxy]
  rcases (hker (x - y)).mp hxyKer with ⟨n, hn⟩
  have hπreg := localizedNeronBlowupTarget_pi_isSMulRegular (S := S) π hπ a
  have hsub : x - y = 0 := by
    cases n with
    | zero =>
        -- Torsion exponent `0` already says the difference vanishes.
        simpa using hn
    | succ n =>
        have hpowreg :
            IsSMulRegular (localizedNeronBlowupTarget π hπ a)
              ((algebraMap S.R (localizedNeronBlowupTarget π hπ a) π) ^ (n + 1)) :=
          hπreg.pow (n + 1)
        -- A positive power of a regular element still cancels on the localized blowup chart.
        exact hpowreg.right_eq_zero_of_smul (by simpa [smul_eq_mul] using hn)
  exact sub_eq_zero.mp hsub

section LocalizationBaseChange

variable (π : S.R) (hπ : Irreducible π) (a : S.A) (ha : a ∉ S.p)

local notation "A" => S.A
local notation "Aa" => Localization.Away a
local notation "pA" => S.p
local notation "πA" => neronBlowupParameter π hπ
local notation "A'" => A[pA / πA]
local notation "pa" => neronBlowupLocalizationCenterIdeal a ha
local notation "πa" => neronBlowupLocalizationCenterParameter π hπ a ha
local notation "A'a" => Localization.Away (algebraMap A A' a)

/-- The canonical comparison map from the localization `A'_a` of the Néron blowup `A'` to the
affine Néron blowup of the localized factorization `A_a → Λ`. -/
noncomputable def neronBlowup_localization_baseChangeComparison :
    A'a →ₐ[Aa] affineBlowupChart pa πa := by
  -- Rewrite the localized center ideal and its chosen parameter directly to avoid a brittle cast.
  simpa [pa, πa, neronBlowup_localization_centerIdeal_eq_map (S := S) a ha,
    neronBlowupLocalizationCenterParameter, neronBlowupLocalizationCenterParameter_mem,
    mappedIdealElement, neronBlowupParameter, IsScalarTower.algebraMap_eq] using
    localizedBlowupComparison π hπ a

/-- The canonical comparison map from `A'_a` to the affine Néron blowup of `A_a → Λ` is
bijection. -/
theorem neronBlowup_localization_baseChangeComparison_bijective :
    Function.Bijective (neronBlowup_localization_baseChangeComparison π hπ a ha) := by
  -- The public comparison map is the localized comparison after the same codomain transport.
  simpa [neronBlowup_localization_baseChangeComparison, pa, πa,
    neronBlowup_localization_centerIdeal_eq_map (S := S) a ha,
    neronBlowupLocalizationCenterParameter, neronBlowupLocalizationCenterParameter_mem,
    mappedIdealElement, neronBlowupParameter, IsScalarTower.algebraMap_eq] using
    localizedBlowupComparison_bijective (S := S) π hπ a

/-- Lemma 16.4.2 (1): if `a ∉ 𝔭`, then the affine Néron blowup of the localized factorization
`A_a → Λ` has center ideal `Ideal.map (algebraMap S.A (Localization.Away a)) S.p`, and the
corresponding affine blowup chart is canonically the localization `A'_a` of the Néron blowup
`A'`. -/
@[stacks 0BJ3]
noncomputable def neronBlowup_localization_baseChange
    : affineBlowupChart pa πa ≃ₐ[Aa] A'a :=
  (AlgEquiv.ofBijective
      (neronBlowup_localization_baseChangeComparison π hπ a ha)
      (neronBlowup_localization_baseChangeComparison_bijective π hπ a ha)).symm

end LocalizationBaseChange

section Surjection

section SurjectiveBaseChange

variable (S)
variable (B : Type x) [CommRing B] [Algebra S.R B] [Algebra B S.A] [IsScalarTower S.R B S.A]

/-- The ideal `𝔭_B ⊆ B` attached to the canonical source factorization `B → A → Λ`. -/
def neronBlowup_surjection_centerIdeal : Ideal B :=
  Ideal.comap (S.phi.comp (IsScalarTower.toAlgHom S.R B S.A)).toRingHom (maximalIdeal S.L)

-- Proof sketch: the same ramification-index-one argument as for `A` shows that the image of a
-- uniformizer `π` of `R` lands in the inverse image of `maximalIdeal Λ` under the canonical map
-- `B → A → Λ`.
/-- A chosen uniformizer of `R` maps into the ideal `𝔭_B ⊆ B`. -/
theorem neronBlowup_surjection_uniformizer_mem_centerIdeal {π : S.R} (hπ : Irreducible π) :
    algebraMap S.R B π ∈
      neronBlowup_surjection_centerIdeal S B :=
  by
  -- As in the `A`-case, the uniformizer lies in `maximalIdeal R`.
  have hπmax : π ∈ maximalIdeal S.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (irreducible_iff.mp hπ).1
  -- Pushing that membership to `Λ` gives the required inverse-image condition.
  rw [neronBlowup_surjection_centerIdeal, Ideal.mem_comap]
  have hπL :
      algebraMap S.R S.L π ∈ maximalIdeal S.L := by
    have hmap :
        algebraMap S.R S.L π ∈ Ideal.map (algebraMap S.R S.L) (maximalIdeal S.R) :=
      Ideal.mem_map_of_mem _ hπmax
    simpa [S.map_maximalIdeal_eq] using hmap
  simpa [IsScalarTower.algebraMap_eq S.R B S.A, IsScalarTower.algebraMap_eq S.R S.A S.L] using hπL

/-- The image of a chosen uniformizer `π` viewed as an element of the ideal `𝔭_B ⊆ B`. -/
noncomputable def neronBlowup_surjection_centerParameter (π : S.R) (hπ : Irreducible π) :
    neronBlowup_surjection_centerIdeal S B :=
  ⟨algebraMap S.R B π, neronBlowup_surjection_uniformizer_mem_centerIdeal S B hπ⟩

-- Proof sketch: compare the defining comap ideals of `𝔭_B` and `S.p` using the canonical
-- composite `B → A → Λ`; after pushing forward along `algebraMap B S.A`, the two descriptions
-- agree.
/-- The ideal defining the Néron blowup of `A` is the image of the corresponding ideal of `B`. -/
theorem neronBlowup_surjection_centerIdeal_map_eq
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    Ideal.map (algebraMap B S.A) (neronBlowup_surjection_centerIdeal S B) = S.p := by
  -- Rewrite the source center ideal as the comap of `𝔭` along `B → A`.
  have hcomap :
      neronBlowup_surjection_centerIdeal S B = Ideal.comap (algebraMap B S.A) S.p := by
    ext x
    rfl
  rw [hcomap]
  -- Surjectivity identifies the extension of that comap ideal with the original ideal.
  exact Ideal.map_comap_of_surjective (algebraMap B S.A) hf S.p

section

variable (π : S.R) (hπ : Irreducible π)

local notation "A" => S.A
local notation "pB" => neronBlowup_surjection_centerIdeal S B
local notation "πB" => neronBlowup_surjection_centerParameter S B π hπ
local notation "B'" => affineBlowupChart pB πB
local notation "AB'" => A ⊗[B] B'
local notation "πAB'" => algebraMap B AB' (algebraMap S.R B π)

private theorem surjectiveBaseChangeComparison_surjective :
    Function.Surjective (tensorToAffineBlowupAlgebra A pB πB) := by
  let hbase :=
    affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
      A pB πB
  exact hbase.1

private theorem mem_ker_surjectiveBaseChangeComparison_iff_exists_pow_mul_eq_zero
    (x : AB') :
    x ∈ RingHom.ker (tensorToAffineBlowupAlgebra A pB πB).toRingHom ↔
      ∃ n : ℕ, πAB' ^ n * x = 0 := by
  let hbase :=
    affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
      A pB πB
  exact hbase.2 x

private noncomputable def surjectiveBaseChangeTargetParameter
    (_hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    S.p :=
  neronBlowupParameter π hπ

private noncomputable def surjectiveBaseChangeComparisonToNeronBlowup
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    AB' →ₐ[A]
      affineBlowupChart S.p
        (surjectiveBaseChangeTargetParameter (S := S) (B := B) (π := π) (hπ := hπ) hf) := by
  -- Rewrite the center ideal and chosen parameter directly instead of casting through equalities.
  simpa [pB, πB, surjectiveBaseChangeTargetParameter,
    neronBlowup_surjection_centerIdeal_map_eq (S := S) (B := B) hf,
    neronBlowup_surjection_centerParameter, mappedIdealElement, neronBlowupParameter,
    IsScalarTower.algebraMap_eq] using
    (tensorToAffineBlowupAlgebra A pB πB)

/-- The canonical comparison map from the surjective base change
`A ⊗[B] B[p_B / π_B]` to the affine Néron blowup `A[p_A / π_A]`. -/
noncomputable def neronBlowup_surjection_baseChangeComparison
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    AB' →ₐ[A]
      affineBlowupChart S.p (neronBlowupParameter π hπ) := by
  simpa [surjectiveBaseChangeTargetParameter] using
    surjectiveBaseChangeComparisonToNeronBlowup S B π hπ hf

private theorem surjectiveBaseChangeComparisonToNeronBlowup_surjective
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    Function.Surjective (surjectiveBaseChangeComparisonToNeronBlowup S B π hπ hf) := by
  -- The comparison map is the canonical base-change map viewed through a codomain type cast.
  simpa [surjectiveBaseChangeComparisonToNeronBlowup, pB, πB,
    surjectiveBaseChangeTargetParameter,
    neronBlowup_surjection_centerIdeal_map_eq (S := S) (B := B) hf,
    neronBlowup_surjection_centerParameter, mappedIdealElement, neronBlowupParameter,
    IsScalarTower.algebraMap_eq] using
    surjectiveBaseChangeComparison_surjective (S := S) (B := B) (π := π) (hπ := hπ)

private theorem mem_ker_surjectiveBaseChangeComparisonToNeronBlowup_iff_exists_pow_mul_eq_zero
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) (x : AB') :
    x ∈ RingHom.ker (surjectiveBaseChangeComparisonToNeronBlowup S B π hπ hf).toRingHom ↔
      ∃ n : ℕ, πAB' ^ n * x = 0 := by
  -- The same codomain cast leaves the kernel condition unchanged.
  simpa [surjectiveBaseChangeComparisonToNeronBlowup, pB, πB,
    surjectiveBaseChangeTargetParameter,
    neronBlowup_surjection_centerIdeal_map_eq (S := S) (B := B) hf,
    neronBlowup_surjection_centerParameter, mappedIdealElement, neronBlowupParameter,
    IsScalarTower.algebraMap_eq] using
    mem_ker_surjectiveBaseChangeComparison_iff_exists_pow_mul_eq_zero
      (S := S) (B := B) (π := π) (hπ := hπ) x

/-- The canonical comparison map `A ⊗[B] B' → A[p_A / π_A]` is surjective. -/
theorem neronBlowup_surjection_baseChangeComparison_surjective
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    Function.Surjective (neronBlowup_surjection_baseChangeComparison S B π hπ hf) := by
  -- The public comparison map is the same morphism after the final parameter transport.
  simpa [neronBlowup_surjection_baseChangeComparison, surjectiveBaseChangeTargetParameter] using
    surjectiveBaseChangeComparisonToNeronBlowup_surjective
      (S := S) (B := B) (π := π) (hπ := hπ) hf

/-- An element of `A ⊗[B] B'` lies in the kernel of the comparison map exactly when it is killed by
some power of the distinguished source element. -/
theorem mem_ker_neronBlowup_surjection_baseChangeComparison_iff_exists_pow_mul_eq_zero
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) (x : AB') :
    x ∈ RingHom.ker (neronBlowup_surjection_baseChangeComparison S B π hπ hf).toRingHom ↔
      ∃ n : ℕ, πAB' ^ n * x = 0 := by
  -- The final comparison-map cast does not change the kernel criterion.
  simpa [neronBlowup_surjection_baseChangeComparison, surjectiveBaseChangeTargetParameter] using
    mem_ker_surjectiveBaseChangeComparisonToNeronBlowup_iff_exists_pow_mul_eq_zero
      (S := S) (B := B) (π := π) (hπ := hπ) hf x

-- Proof sketch: specialize Lemma `10.70.3` to the surjective scalar-tower map `B → A`. The
-- canonical base-change morphism is exactly `tensorToAffineBlowupAlgebra`, and the distinguished
-- source element is the ambient `algebraMap` image of `π`.
/- Lemma 16.4.2 (2): if the canonical map `B → A` in the scalar tower is surjective, then the
center ideal of `A` is the image of the center ideal of `B`, and the canonical comparison map from
`A ⊗[B] B'` to `A'` is surjective with kernel equal to the `π`-power torsion; equivalently, `A'`
is the quotient of `A ⊗[B] B'` by its `π`-power torsion. -/
theorem neronBlowup_surjection_baseChange_surjective_with_ker_awayTorsion
    (hf : Function.Surjective (IsScalarTower.toAlgHom S.R B S.A)) :
    Ideal.map (algebraMap B A) pB = S.p ∧
      Function.Surjective (neronBlowup_surjection_baseChangeComparison S B π hπ hf) ∧
        ∀ x : AB',
          x ∈ RingHom.ker (neronBlowup_surjection_baseChangeComparison S B π hπ hf).toRingHom ↔
            ∃ n : ℕ, πAB' ^ n * x = 0 := by
  refine ⟨neronBlowup_surjection_centerIdeal_map_eq S B hf, ?_⟩
  refine ⟨neronBlowup_surjection_baseChangeComparison_surjective S B π hπ hf, ?_⟩
  intro x
  exact mem_ker_neronBlowup_surjection_baseChangeComparison_iff_exists_pow_mul_eq_zero
    S B π hπ hf x

end

end SurjectiveBaseChange

end Surjection

end
