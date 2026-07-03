import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u v

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Theorem 16-16.1-2: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the recovered `k[G]`-linear equivalence as an isomorphism in `Rep k G`.
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  -- Faithfulness of `FDRep ⥤ Rep` transports that isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Theorem 16-16.1-2: a finite-dimensional `k[G]`-module is finite length because
finite-dimensionality over the field `k` implies both noetherian and artinian conditions. -/
theorem isFiniteLength_of_groupAlgebra_module_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    IsFiniteLength k[G] M := by
  -- The vector-space finiteness over `k` controls the `k[G]`-module lattice as well.
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- Helper for Theorem 16-16.1-2: choose a Jordan-Hölder series for a finite-dimensional
`k[G]`-module. -/
noncomputable def finiteLengthCompositionSeries_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    CompositionSeries (Submodule k[G] M) :=
  Classical.choose
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))

/-- Helper for Theorem 16-16.1-2: the chosen finite-length composition series starts at `⊥`. -/
theorem finiteLengthCompositionSeries_head_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries_local (A := A) (G := G) M).head = ⊥ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))).1

/-- Helper for Theorem 16-16.1-2: the chosen finite-length composition series ends at `⊤`. -/
theorem finiteLengthCompositionSeries_last_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries_local (A := A) (G := G) M).last = ⊤ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))).2

/-- Helper for Theorem 16-16.1-2: the quotient factor attached to one step of a composition
series. -/
private abbrev compositionSeriesFactor_local
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :=
  ((s (Fin.succ i)) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype)

/-- Helper for Theorem 16-16.1-2: a `k[G]`-submodule inherits its `k`-module structure by
restriction of scalars. -/
private instance submodule_module_over_base_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : Module k N :=
  Module.compHom N (algebraMap k k[G])

/-- Helper for Theorem 16-16.1-2: the scalar tower `k → k[G]` restricts to every
`k[G]`-submodule. -/
private instance submodule_isScalarTower_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : IsScalarTower k k[G] N :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    ext
    exact IsScalarTower.algebraMap_smul (k[G]) a (x : M)

/-- Helper for Theorem 16-16.1-2: quotients of `k[G]`-modules inherit the underlying
`k`-module structure by restriction of scalars. -/
private instance quotient_module_over_base_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : Module k (M ⧸ N) :=
  Module.compHom (M ⧸ N) (algebraMap k k[G])

/-- Helper for Theorem 16-16.1-2: the scalar tower `k → k[G]` descends to every quotient of a
`k[G]`-module. -/
private instance quotient_isScalarTower_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : IsScalarTower k k[G] (M ⧸ N) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦
    IsScalarTower.algebraMap_smul (k[G]) a x

/-- Helper for Theorem 16-16.1-2: a factor of a composition series matches a fixed simple
`k[G]`-module. -/
private def compositionSeriesFactorMatches_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) : Prop :=
  Nonempty (compositionSeriesFactor_local (s := s) (i := i) ≃ₗ[k[G]] T)

/-- Helper for Theorem 16-16.1-2: the number of factors in a chosen composition series that are
isomorphic to a fixed simple module. -/
private noncomputable def simple_factor_count_of_module_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) : ℕ :=
  Nat.card { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }

/-- Helper for Theorem 16-16.1-2: transporting a factor quotient across a linear equivalence
preserves the property of matching the fixed target module. -/
private theorem compositionSeriesFactorMatches_iff_of_linearEquiv_local
    {T A0 B0 : Type*} [AddCommGroup T] [AddCommGroup A0] [AddCommGroup B0]
    [Module k[G] T] [Module k[G] A0] [Module k[G] B0]
    (e : A0 ≃ₗ[k[G]] B0) :
    Nonempty (A0 ≃ₗ[k[G]] T) ↔ Nonempty (B0 ≃ₗ[k[G]] T) := by
  constructor
  · intro hA
    rcases hA with ⟨eA⟩
    exact ⟨e.symm.trans eA⟩
  · intro hB
    rcases hB with ⟨eB⟩
    exact ⟨e.trans eB⟩

/-- Helper for Theorem 16-16.1-2: equivalent composition series have the same count of matching
factors. -/
private theorem simple_factor_count_series_equiv_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    {s₁ s₂ : CompositionSeries (Submodule k[G] M)}
    (h : s₁.Equivalent s₂) :
    simple_factor_count_of_module_local (T := T) (s := s₁) =
      simple_factor_count_of_module_local (T := T) (s := s₂) := by
  classical
  let e :
      { i : Fin s₁.length // compositionSeriesFactorMatches_local (T := T) (s := s₁) (i := i) } ≃
        { j : Fin s₂.length // compositionSeriesFactorMatches_local (T := T) (s := s₂) (i := j) } :=
    { toFun := fun i => ⟨h.choose i.1, by
        rcases h.choose_spec i.1 with ⟨ei⟩
        exact (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T) (e := ei)).1 i.2⟩
      invFun := fun j => ⟨h.choose.symm j.1, by
        rcases h.choose_spec (h.choose.symm j.1) with ⟨ej⟩
        have hj : h.choose (h.choose.symm j.1) = j.1 := by
          simp
        have ej' :
            compositionSeriesFactor_local (s := s₁) (i := h.choose.symm j.1) ≃ₗ[k[G]]
              compositionSeriesFactor_local (s := s₂) (i := h.choose (h.choose.symm j.1)) := by
          simpa [compositionSeriesFactor_local] using ej
        have hmatch :
            compositionSeriesFactorMatches_local (T := T) (s := s₂)
              (i := h.choose (h.choose.symm j.1)) := by
          simpa [hj] using j.2
        exact (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T) (e := ej')).2 hmatch⟩
      left_inv := by
        intro i
        ext
        simp
      right_inv := by
        intro j
        ext
        simp }
  simpa [simple_factor_count_of_module_local] using Nat.card_congr e

/-- Helper for Theorem 16-16.1-2: mapping a factor quotient along an injective linear map
identifies it with the corresponding factor in the mapped composition series. -/
private noncomputable def compositionSeriesFactor_map_equiv_local
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) (i : Fin s.length) :
    compositionSeriesFactor_local (s := s) (i := i) ≃ₗ[k[G]]
      compositionSeriesFactor_local
        (s := s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩)
        (i := i) := by
  let e : s i.succ ≃ₗ[k[G]] Submodule.map f (s i.succ) :=
    Submodule.equivMapOfInjective (f := f) hf (s i.succ)
  have hmap :
      Submodule.map (e : s i.succ →ₗ[k[G]] Submodule.map f (s i.succ))
          ((s (Fin.castSucc i)).comap (s i.succ).subtype) =
        (Submodule.map f (s (Fin.castSucc i))).comap (Submodule.map f (s i.succ)).subtype := by
    -- Compare the predecessor submodules after transporting along the injective map equivalence.
    rw [Submodule.map_equiv_eq_comap_symm]
    ext z
    constructor
    · intro hz
      change ((e.symm z : s i.succ) : N) ∈ s (Fin.castSucc i) at hz
      change z.1 ∈ Submodule.map f (s (Fin.castSucc i))
      exact ⟨(e.symm z : s i.succ), hz, by simp [e]⟩
    · intro hz
      change ((e.symm z : s i.succ) : N) ∈ s (Fin.castSucc i)
      change z.1 ∈ Submodule.map f (s (Fin.castSucc i)) at hz
      rcases hz with ⟨y, hy, hyz⟩
      rcases z.2 with ⟨w, hw, hwz⟩
      have hwy : w = y := hf (hwz.trans hyz.symm)
      have hyq : y ∈ s i.succ := hwy ▸ hw
      have heyz : e ⟨y, hyq⟩ = z := by
        apply Subtype.ext
        simpa [e] using hyz
      have hEq : (⟨y, hyq⟩ : s i.succ) = e.symm z :=
        e.injective (heyz.trans (e.apply_symm_apply z).symm)
      simpa [hEq.symm] using hy
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      ((s (Fin.castSucc i)).comap (s i.succ).subtype)
      ((Submodule.map f (s (Fin.castSucc i))).comap (Submodule.map f (s i.succ)).subtype)
      e hmap)

/-- Helper for Theorem 16-16.1-2: mapping a composition series along an injective linear map
preserves the count of matching factors. -/
private theorem simple_factor_count_series_map_local
    {T M N : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N]
    [Module k[G] T] [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) :
    simple_factor_count_of_module_local (T := T)
        (s := s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩) =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
  let e :
      { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) } ≃
        { i : Fin s'.length // compositionSeriesFactorMatches_local (T := T) (s := s') (i := i) } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_map_equiv_local (hf := hf) (s := s) (i := i.1))).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_map_equiv_local (hf := hf) (s := s) (i := i.1))).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module_local, s'] using (Nat.card_congr e).symm

/-- Helper for Theorem 16-16.1-2: comapping along a surjective linear map identifies factor
quotients with the original factors. -/
private noncomputable def compositionSeriesFactor_comap_equiv_local
    {M Q : Type*} [AddCommGroup M] [AddCommGroup Q]
    [Module k M] [Module k Q] [Module k[G] M] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) (i : Fin s.length) :
    compositionSeriesFactor_local
        (s := s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩)
        (i := i) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := s) (i := i) := by
  let φ₀ : Submodule.comap g (s i.succ) →ₗ[k[G]] s i.succ :=
    { toFun := fun x => ⟨g x, x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  have hφ₀_surj : Function.Surjective φ₀ := by
    -- Surjectivity comes from surjectivity of `g` on the ambient module.
    intro y
    rcases hg y with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa [hx] using y.2
    · ext
      simp [φ₀, hx]
  let φ :
      Submodule.comap g (s i.succ) →ₗ[k[G]]
        (s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype) :=
    (Submodule.mkQ ((s (Fin.castSucc i)).comap (s i.succ).subtype)).comp φ₀
  have hφ_surj : Function.Surjective φ := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro y
    rcases hφ₀_surj y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hker :
      φ.ker =
        (Submodule.comap g (s (Fin.castSucc i))).comap (Submodule.comap g (s i.succ)).subtype := by
    -- Landing in the previous step is exactly the kernel condition after quotienting.
    ext x
    change
      ((Submodule.mkQ ((s (Fin.castSucc i)).comap (s i.succ).subtype)) (φ₀ x) = 0) ↔
        x.1 ∈ Submodule.comap g (s (Fin.castSucc i))
    simp [φ₀]
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective φ hφ_surj)

/-- Helper for Theorem 16-16.1-2: comapping a composition series along a surjective linear map
preserves the count of matching factors. -/
private theorem simple_factor_count_series_comap_local
    {T M Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k Q] [Module k[G] M] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) :
    simple_factor_count_of_module_local (T := T)
        (s := s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩) =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
  let e :
      { i : Fin s'.length // compositionSeriesFactorMatches_local (T := T) (s := s') (i := i) } ≃
        { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_comap_equiv_local (hg := hg) (s := s) (i := i.1))).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_comap_equiv_local (hg := hg) (s := s) (i := i.1))).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module_local, s'] using Nat.card_congr e

/-- Helper for Theorem 16-16.1-2: the multiplicity of a fixed target module in a finite
`k[G]`-module, computed from the chosen Jordan-Hölder series. -/
private noncomputable def simple_factor_multiplicity_local
    (T : Type*) [AddCommGroup T] [Module k[G] T]
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] : ℕ :=
  simple_factor_count_of_module_local (T := T)
    (s := finiteLengthCompositionSeries_local (A := A) (G := G) M)

/-- Helper for Theorem 16-16.1-2: the chosen-series multiplicity agrees with the count computed
from any other composition series with endpoints `⊥` and `⊤`. -/
private theorem simple_factor_multiplicity_eq_count_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [FiniteDimensional k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (s : CompositionSeries (Submodule k[G] M))
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    simple_factor_multiplicity_local (A := A) (G := G) T M =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  -- Jordan-Hölder identifies the chosen composition series with any other one having the same
  -- endpoints, so the factor count is independent of the chosen series.
  exact simple_factor_count_series_equiv_local (T := T) (h :=
    CompositionSeries.jordan_holder
      (finiteLengthCompositionSeries_local (A := A) (G := G) M) s
      ((finiteLengthCompositionSeries_head_local (A := A) (G := G) M).trans hs_head.symm)
      ((finiteLengthCompositionSeries_last_local (A := A) (G := G) M).trans hs_last.symm))

/-- Helper for Theorem 16-16.1-2: in an exact sequence, the mapped left series and comapped
right series meet at the exact seam. -/
private theorem compositionSeries_map_last_eq_comap_head_of_exact_local
    {M N Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module k M] [Module k N] [Module k Q]
    [Module k[G] M] [Module k[G] N] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N] [IsScalarTower k k[G] Q]
    {f : N →ₗ[k[G]] M} {g : M →ₗ[k[G]] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (t : CompositionSeries (Submodule k[G] N)) (ht : t.last = ⊤)
    (s : CompositionSeries (Submodule k[G] Q)) (hs : s.head = ⊥) :
    let t' : CompositionSeries (Submodule k[G] M) :=
      t.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
    let s' : CompositionSeries (Submodule k[G] M) :=
      s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
    t'.last = s'.head := by
  dsimp
  let t' : CompositionSeries (Submodule k[G] M) :=
    t.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
  -- Exactness identifies `range f` with `ker g`, so the two transported series glue there.
  calc
    t'.last = Submodule.map f (⊤ : Submodule k[G] N) := by
      simpa [t'] using congrArg (Submodule.map f) ht
    _ = Submodule.comap g (⊥ : Submodule k[G] Q) := by
      rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp hfg]
    _ = s'.head := by
      symm
      simpa [s'] using congrArg (Submodule.comap g) hs

/-- Helper for Theorem 16-16.1-2: smashing composition series preserves the factors coming from
the left block. -/
private noncomputable def compositionSeriesFactor_smash_left_equiv_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin t.length) :
    compositionSeriesFactor_local (s := t.smash s h) (i := i.castAdd s.length) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := t) (i := i) := by
  -- Compare the interval endpoints inside the smashed series and in the original left block.
  have hsucc :
      (t.smash s h) (i.castAdd s.length).succ = t i.succ := by
    simpa using (RelSeries.smash_succ_castAdd (p := t) (q := s) h i)
  let e : (t.smash s h) (i.castAdd s.length).succ ≃ₗ[k[G]] t i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.castAdd s.length).succ →ₗ[k[G]] t i.succ)
          (((t.smash s h) (i.castAdd s.length).castSucc).comap
            ((t.smash s h) (i.castAdd s.length).succ).subtype) =
        (t i.castSucc).comap (t i.succ).subtype := by
    ext x
    simp [e, RelSeries.smash_castAdd]
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.castAdd s.length).castSucc).comap
        ((t.smash s h) (i.castAdd s.length).succ).subtype)
      ((t i.castSucc).comap (t i.succ).subtype) e hmap)

/-- Helper for Theorem 16-16.1-2: smashing composition series preserves the factors coming from
the right block. -/
private noncomputable def compositionSeriesFactor_smash_right_equiv_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin s.length) :
    compositionSeriesFactor_local (s := t.smash s h) (i := i.natAdd t.length) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := s) (i := i) := by
  -- The right block also survives unchanged after translating the endpoints through the smash.
  have hsucc :
      (t.smash s h) (i.natAdd t.length).succ = s i.succ := by
    simpa using (RelSeries.smash_succ_natAdd (p := t) (q := s) h i)
  let e : (t.smash s h) (i.natAdd t.length).succ ≃ₗ[k[G]] s i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.natAdd t.length).succ →ₗ[k[G]] s i.succ)
          (((t.smash s h) (i.natAdd t.length).castSucc).comap
            ((t.smash s h) (i.natAdd t.length).succ).subtype) =
        (s i.castSucc).comap (s i.succ).subtype := by
    ext x
    simp [e, -Fin.castSucc_natAdd, RelSeries.smash_natAdd]
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.natAdd t.length).castSucc).comap
        ((t.smash s h) (i.natAdd t.length).succ).subtype)
      ((s i.castSucc).comap (s i.succ).subtype) e hmap)

/-- Helper for Theorem 16-16.1-2: the count of matching factors in a smashed composition series
is the sum of the counts in the two blocks. -/
private theorem simple_factor_count_series_smash_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) :
    simple_factor_count_of_module_local (T := T) (s := t.smash s h) =
      simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
  classical
  have hpred :
      ∀ l : Fin (t.length + s.length),
        compositionSeriesFactorMatches_local (T := T) (s := t.smash s h) (i := l) ↔
          match finSumFinEquiv.symm l with
          | Sum.inl i => compositionSeriesFactorMatches_local (T := T) (s := t) (i := i)
          | Sum.inr i => compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) := by
    intro l
    cases hl : finSumFinEquiv.symm l with
    | inl i =>
        have hl' : l = i.castAdd s.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_castAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_smash_left_equiv_local (t := t) (s := s) (h := h)
              (i := i)))
    | inr i =>
        have hl' : l = i.natAdd t.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_natAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_smash_right_equiv_local (t := t) (s := s) (h := h)
              (i := i)))
  let e :
      { l : Fin (t.length + s.length) //
          compositionSeriesFactorMatches_local (T := T) (s := t.smash s h) (i := l) } ≃
        ({ i : Fin t.length //
            compositionSeriesFactorMatches_local (T := T) (s := t) (i := i) } ⊕
          { i : Fin s.length //
            compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }) :=
    ((finSumFinEquiv.symm).subtypeEquiv hpred).trans
      (Equiv.subtypeSum
        (p := fun u : Fin t.length ⊕ Fin s.length =>
          match u with
          | Sum.inl i => compositionSeriesFactorMatches_local (T := T) (s := t) (i := i)
          | Sum.inr i => compositionSeriesFactorMatches_local (T := T) (s := s) (i := i)))
  -- The matching factors split into the disjoint left and right blocks.
  calc
    simple_factor_count_of_module_local (T := T) (s := t.smash s h) =
        Nat.card
          ({ i : Fin t.length //
              compositionSeriesFactorMatches_local (T := T) (s := t) (i := i) } ⊕
            { i : Fin s.length //
              compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }) := by
          simpa [simple_factor_count_of_module_local] using Nat.card_congr e
    _ = simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
          rw [simple_factor_count_of_module_local, simple_factor_count_of_module_local, Nat.card_sum]

/-- Helper for Theorem 16-16.1-2: fixed-target multiplicity is additive in short exact sequences
of finite `k[G]`-modules. -/
private theorem simple_factor_multiplicity_eq_add_of_exact_local
    {T M N Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k N] [Module k Q]
    [FiniteDimensional k M] [FiniteDimensional k N] [FiniteDimensional k Q]
    [Module k[G] M] [Module k[G] N] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N] [IsScalarTower k k[G] Q]
    {f : N →ₗ[k[G]] M} {g : M →ₗ[k[G]] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    simple_factor_multiplicity_local (A := A) (G := G) T M =
      simple_factor_multiplicity_local (A := A) (G := G) T N +
        simple_factor_multiplicity_local (A := A) (G := G) T Q := by
  let t : CompositionSeries (Submodule k[G] N) :=
    finiteLengthCompositionSeries_local (A := A) (G := G) N
  let s : CompositionSeries (Submodule k[G] Q) :=
    finiteLengthCompositionSeries_local (A := A) (G := G) Q
  let t' : CompositionSeries (Submodule k[G] M) :=
    t.map ⟨Submodule.map f, fun {_ _} h => Submodule.map_covBy_of_injective hf h⟩
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {_ _} h => Submodule.comap_covBy_of_surjective hg h⟩
  let hseam : t'.last = s'.head :=
    compositionSeries_map_last_eq_comap_head_of_exact_local
      (hf := hf) (hg := hg) (hfg := hfg)
      (t := t) (ht := finiteLengthCompositionSeries_last_local (A := A) (G := G) N)
      (s := s) (hs := finiteLengthCompositionSeries_head_local (A := A) (G := G) Q)
  let r : CompositionSeries (Submodule k[G] M) := t'.smash s' hseam
  have ht_head : t.head = ⊥ :=
    finiteLengthCompositionSeries_head_local (A := A) (G := G) N
  have hs_last : s.last = ⊤ :=
    finiteLengthCompositionSeries_last_local (A := A) (G := G) Q
  -- Route correction: prove additivity at the series level on `r := t'.smash s' hseam`, then
  -- transport back to the chosen multiplicities on the three module owners.
  calc
    simple_factor_multiplicity_local (A := A) (G := G) T M =
        simple_factor_count_of_module_local (T := T) (s := r) := by
          apply simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) r
          · simpa [r, t', t, ht_head, -Submodule.map_bot] using Submodule.map_bot f
          · simpa [r, s', s, hs_last, -Submodule.comap_top] using Submodule.comap_top g
    _ = simple_factor_count_of_module_local (T := T) (s := t') +
        simple_factor_count_of_module_local (T := T) (s := s') := by
          simp [r, simple_factor_count_series_smash_local]
    _ = simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
          rw [simple_factor_count_series_map_local (T := T) (hf := hf) (s := t),
            simple_factor_count_series_comap_local (T := T) (hg := hg) (s := s)]
    _ = simple_factor_multiplicity_local (A := A) (G := G) T N +
        simple_factor_multiplicity_local (A := A) (G := G) T Q := by
          rw [← simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) t
              ht_head
              (finiteLengthCompositionSeries_last_local (A := A) (G := G) N),
            ← simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) s
              (finiteLengthCompositionSeries_head_local (A := A) (G := G) Q)
              hs_last]

/-- Helper for Theorem 16-16.1-2: fixed-simple multiplicity packaged as an additive map on the
free abelian group generated by finite-dimensional `k[G]`-representations. -/
private noncomputable abbrev simple_factor_multiplicity_lift_local
    (S : FDRep k G) :
    FreeAbelianGroup (FDRep k G) →+ ℤ :=
  FreeAbelianGroup.lift fun σ ↦
    let ρS : Representation k G S := S.ρ
    letI : Module k[G] S := by
      simpa using (inferInstance : Module k[G] ρS.asModule)
    let ρσ : Representation k G σ := σ.ρ
    letI : Module k[G] σ := by
      simpa using (inferInstance : Module k[G] ρσ.asModule)
    letI : IsScalarTower k k[G] σ := by
      simpa using (inferInstance : IsScalarTower k k[G] ρσ.asModule)
    Int.ofNat (simple_factor_multiplicity_local (A := A) (G := G) S σ)

/-- Helper for Theorem 16-16.1-2: the fixed-simple multiplicity lift vanishes on the defining
Grothendieck relations. -/
private theorem finiteRepGrothendieckRelations_le_simple_factor_multiplicity_lift_ker_local
    (S : FDRep k G) :
    finiteRepGrothendieckRelations k G ≤
      (simple_factor_multiplicity_lift_local (A := A) (G := G) S).ker := by
  let ρS : Representation k G S := S.ρ
  letI : Module k[G] S := by
    simpa using (inferInstance : Module k[G] ρS.asModule)
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨T, hT⟩, rfl⟩
  let ρ₁ : Representation k G T.X₁ := T.X₁.ρ
  let ρ₂ : Representation k G T.X₂ := T.X₂.ρ
  let ρ₃ : Representation k G T.X₃ := T.X₃.ρ
  letI : Module k[G] T.X₁ := by
    simpa using (inferInstance : Module k[G] ρ₁.asModule)
  letI : Module k[G] T.X₂ := by
    simpa using (inferInstance : Module k[G] ρ₂.asModule)
  letI : Module k[G] T.X₃ := by
    simpa using (inferInstance : Module k[G] ρ₃.asModule)
  letI : IsScalarTower k k[G] T.X₁ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₁.asModule)
  letI : IsScalarTower k k[G] T.X₂ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₂.asModule)
  letI : IsScalarTower k k[G] T.X₃ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₃.asModule)
  let F : FDRep k G ⥤ ModuleCat k[G] :=
    forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra
  let U : ShortComplex (ModuleCat k[G]) := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  let f : T.X₁ →ₗ[k[G]] T.X₂ := by
    simpa [U, F] using U.f.hom
  let g : T.X₂ →ₗ[k[G]] T.X₃ := by
    simpa [U, F] using U.g.hom
  have hf : Function.Injective f := by
    simpa [f] using hU.moduleCat_injective_f
  have hg : Function.Surjective g := by
    simpa [g] using hU.moduleCat_surjective_g
  have hfg : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  have hadd :
      simple_factor_multiplicity_local (A := A) (G := G) S T.X₂ =
        simple_factor_multiplicity_local (A := A) (G := G) S T.X₁ +
          simple_factor_multiplicity_local (A := A) (G := G) S T.X₃ := by
    -- Transport the defining short exact sequence to the owner `k[G]`-module carriers and apply
    -- additivity of fixed-simple multiplicity.
    simpa using
      (simple_factor_multiplicity_eq_add_of_exact_local
        (A := A) (G := G) (T := S) hf hg hfg)
  change
    simple_factor_multiplicity_lift_local (A := A) (G := G) S
        (FreeAbelianGroup.of T.X₂ - FreeAbelianGroup.of T.X₁ - FreeAbelianGroup.of T.X₃) = 0
  -- After evaluating the free-abelian-group lift on each generator, the exact-sequence
  -- additivity identity cancels the defining relation.
  simp [simple_factor_multiplicity_lift_local, hadd, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 16-16.1-2: the fixed-simple multiplicity descends to LinearRepresentations_Serre_1977's Grothendieck
group. -/
noncomputable def simple_factor_multiplicity_hom_fixed_local
    (S : FDRep k G) :
    R_k(G) →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (simple_factor_multiplicity_lift_local (A := A) (G := G) S)
    (finiteRepGrothendieckRelations_le_simple_factor_multiplicity_lift_ker_local
      (A := A) (G := G) S)

/-- Helper for Theorem 16-16.1-2: a subtype of `Fin 1` is either empty or has one element,
according to whether the unique index satisfies the defining predicate. -/
private theorem nat_card_subtype_fin_one_eq_ite_local
    (P : Fin 1 → Prop) [DecidablePred P] :
    Nat.card { i : Fin 1 // P i } = if P 0 then 1 else 0 := by
  classical
  by_cases h : P 0
  · have hAll : ∀ i : Fin 1, P i := by
      intro i
      simpa [Fin.eq_zero i] using h
    letI : Unique { i : Fin 1 // P i } :=
      ⟨⟨0, h⟩, fun x => by
        rcases x with ⟨i, hi⟩
        simp [Fin.eq_zero i]⟩
    simp [h]
  · have hNone : ∀ i : Fin 1, ¬ P i := by
      intro i
      simpa [Fin.eq_zero i] using h
    haveI : IsEmpty { i : Fin 1 // P i } := ⟨fun x => hNone x.1 x.2⟩
    simp [h]

/-- Helper for Theorem 16-16.1-2: the fixed-simple multiplicity hom evaluates on a simple class
as the expected Kronecker delta. -/
private theorem simple_factor_multiplicity_hom_apply_simple_local
    (τ σ : FDRep k G) [Simple σ] [Decidable (Nonempty (σ ≅ τ))] :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ [σ]₀ =
      if Nonempty (σ ≅ τ) then 1 else 0 := by
  let ρτ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρτ.asModule)
  let ρσ : Representation k G σ := σ.ρ
  letI : Module k[G] σ := by
    simpa using (inferInstance : Module k[G] ρσ.asModule)
  letI : IsScalarTower k k[G] σ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρσ.asModule)
  have hsimple : IsSimpleModule k[G] σ := by
    letI : Representation.IsIrreducible ρσ := by
      simpa [ρσ] using (FDRep.isIrreducible_of_simple σ)
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule ρσ).mp inferInstance
  have hcov : (⊥ : Submodule k[G] σ) ⋖ ⊤ := by
    -- Route correction: compute the simple-case multiplicity on the explicit `⊥ < ⊤` series.
    rw [covBy_iff_quot_is_simple bot_le]
    let eTop :
        ((⊤ : Submodule k[G] σ) ⧸
          Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] σ))
            (⊥ : Submodule k[G] σ)) ≃ₗ[k[G]] σ :=
      (Submodule.quotEquivOfEqBot _ (by simp)).trans Submodule.topEquiv
    exact (LinearEquiv.isSimpleModule_iff eTop).2 hsimple
  let s : CompositionSeries (Submodule k[G] σ) :=
    (RelSeries.singleton _ (⊥ : Submodule k[G] σ)).snoc ⊤ hcov
  have hs_head : s.head = ⊥ := by
    simpa [s] using
      (RelSeries.head_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] σ)) ⊤ hcov)
  have hs_last : s.last = ⊤ := by
    simpa [s] using
      (RelSeries.last_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] σ)) ⊤ hcov)
  have hslen : s.length = 1 := by
    simp [s]
  let i0 : Fin s.length := hslen.symm ▸ (0 : Fin 1)
  have hmult :
      simple_factor_multiplicity_local (A := A) (G := G) τ σ =
        simple_factor_count_of_module_local (T := τ) (s := s) := by
    exact
      simple_factor_multiplicity_eq_count_local
        (A := A) (G := G) (T := τ) s hs_head hs_last
  have hfactor_equiv :
      compositionSeriesFactor_local (s := s) (i := i0) ≃ₗ[k[G]] σ := by
    simpa [s, i0, hslen, compositionSeriesFactor_local] using
      ((Submodule.quotEquivOfEqBot
          (Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] σ))
            (⊥ : Submodule k[G] σ)) (by simp)).trans
        (Submodule.topEquiv.trans (LinearEquiv.refl k[G] σ)))
  have hmatch :
      compositionSeriesFactorMatches_local (T := τ) (s := s) (i := i0) ↔
        Nonempty (σ ≅ τ) := by
    constructor
    · intro h
      rcases h with ⟨e⟩
      simpa using
        (fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
          (A := A) (G := G) (σ := σ) (τ := τ) ⟨hfactor_equiv.symm.trans e⟩)
    · intro h
      rcases h with ⟨e⟩
      exact ⟨hfactor_equiv.trans
        (by
          simpa using
            ((((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso e).toLinearEquiv))⟩
  have hcount :
      simple_factor_count_of_module_local (T := τ) (s := s) =
        if Nonempty (σ ≅ τ) then 1 else 0 := by
    classical
    let P : Fin 1 → Prop := fun i ↦
      compositionSeriesFactorMatches_local (T := τ) (s := s) (i := hslen.symm ▸ i)
    let eCount :
        { i : Fin s.length //
            compositionSeriesFactorMatches_local (T := τ) (s := s) (i := i) } ≃
          { i : Fin 1 // P i } :=
      { toFun := fun i => ⟨Equiv.cast (congrArg Fin hslen) i.1, by simpa [P] using i.2⟩
        invFun := fun i => ⟨Equiv.cast (congrArg Fin hslen.symm) i.1, by simpa [P] using i.2⟩
        left_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp
        right_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp }
    have hP : ∀ i : Fin 1, P i ↔ Nonempty (σ ≅ τ) := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [P, i0] using hmatch
    calc
      simple_factor_count_of_module_local (T := τ) (s := s) = Nat.card { i : Fin 1 // P i } := by
        rw [simple_factor_count_of_module_local]
        exact Nat.card_congr eCount
      _ = if P 0 then 1 else 0 := nat_card_subtype_fin_one_eq_ite_local P
      _ = if Nonempty (σ ≅ τ) then 1 else 0 := by
            simp [hP 0]
  -- Evaluate the descended map on `[σ]₀`, rewrite the multiplicity through the explicit simple
  -- two-step series, and then count the unique Jordan-Hölder factor.
  calc
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ [σ]₀ =
        simple_factor_multiplicity_lift_local (A := A) (G := G) τ (FreeAbelianGroup.of σ) := by
          simp [simple_factor_multiplicity_hom_fixed_local, finiteRepGrothendieckClass]
    _ = Int.ofNat (simple_factor_multiplicity_local (A := A) (G := G) τ σ) := by
          simp [simple_factor_multiplicity_lift_local]
    _ = Int.ofNat (simple_factor_count_of_module_local (T := τ) (s := s)) := by
          rw [hmult]
    _ = if Nonempty (σ ≅ τ) then 1 else 0 := by
          simp [hcount]

/-- Helper for Theorem 16-16.1-2: on a complete simple family, the fixed-simple multiplicity hom
is the Kronecker-delta functional at the chosen index. -/
private theorem simple_factor_multiplicity_hom_apply_simple_family_local
    (S : FDRep k G) [Simple S]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (j : ι) :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S [π j]₀ =
      if j = iS then 1 else 0 := by
  classical
  letI : Simple (π j) := hπ_complete.isSimple j
  have hdelta :
      (if Nonempty (π j ≅ S) then 1 else 0 : ℤ) = if j = iS then 1 else 0 := by
    by_cases hj : j = iS
    · subst hj
      simp [hS_iso]
    · have hnot : ¬ Nonempty (π j ≅ S) := by
        intro h
        rcases h with ⟨e⟩
        rcases hS_iso with ⟨eS⟩
        exact hπ_pairwise hj (⟨e.trans eS.symm⟩)
      simp [hj, hnot]
  simpa [hdelta] using
    (simple_factor_multiplicity_hom_apply_simple_local
      (A := A) (G := G) (τ := S) (σ := π j))

/-- Helper for Theorem 16-16.1-2: the canonical simple-basis coordinate at `iS` agrees with the
fixed-simple multiplicity functional for any simple `S` represented by `π iS`. -/
theorem simple_basis_coord_eq_fixed_simple_multiplicity_local
    (S : FDRep k G) [Simple S]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (x : R_k(G)) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr x iS =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S x := by
  classical
  let b :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let coord : R_k(G) →+ ℤ :=
    { toFun := fun y ↦ b.repr y iS
      map_zero' := by simp
      map_add' := by
        intro y z
        simp }
  have hbasis :
      ∀ j, simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S (b j) =
        coord (b j) := by
    intro j
    have hleft :
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S (b j) =
          if j = iS then 1 else 0 := by
      simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
        (simple_factor_multiplicity_hom_apply_simple_family_local
          (A := A) (G := G) S π hπ_pairwise hπ_complete iS hS_iso j)
    have hright :
        coord (b j) = if j = iS then 1 else 0 := by
      have hb : b.repr (b j) = Finsupp.single j (1 : ℤ) := by
        simpa using b.repr_self j
      have hbi := congrArg (fun c : ι →₀ ℤ => c iS) hb
      simpa [coord, Finsupp.single_apply] using hbi
    exact hleft.trans hright.symm
  have hhom :
      (simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S).toIntLinearMap =
        coord.toIntLinearMap := by
    apply b.ext
    intro j
    exact hbasis j
  -- Compare the two linear maps on the class `x` after they have been identified on the basis.
  have hx := congrArg (fun f : R_k(G) →ₗ[ℤ] ℤ ↦ f x) hhom
  simpa [coord] using hx.symm

end

end Representation
