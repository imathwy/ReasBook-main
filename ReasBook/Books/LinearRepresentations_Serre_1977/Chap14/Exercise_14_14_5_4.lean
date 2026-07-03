import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_3_5
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MonoidAlgebra

universe u w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {S : Type w} [AddCommGroup S] [Module k[G] S]
variable {P : Type x} [AddCommGroup P] [Module k[G] P]

/-- Helper for Exercise 14-14.5-4: the composition factor at a step of a composition series. -/
private abbrev compositionSeriesFactor
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :=
  ((s (Fin.succ i)) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype)

/-- Helper for Exercise 14-14.5-4: smashing composition series preserves the factors coming from
the left block. -/
private noncomputable def compositionSeriesFactor_smash_left_equiv
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin t.length) :
    compositionSeriesFactor (k := k) (G := G) (t.smash s h) (i.castAdd s.length) ≃ₗ[k[G]]
      compositionSeriesFactor (k := k) (G := G) t i := by
  -- Compare the two interval endpoints inside the smashed series and in the original left block.
  have hsucc :
      (t.smash s h) (i.castAdd s.length).succ = t i.succ := by
    simpa using (RelSeries.smash_succ_castAdd (p := t) (q := s) h i)
  let e :
      (t.smash s h) (i.castAdd s.length).succ ≃ₗ[k[G]] t i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.castAdd s.length).succ →ₗ[k[G]] t i.succ)
          (((t.smash s h) (i.castAdd s.length).castSucc).comap
            ((t.smash s h) (i.castAdd s.length).succ).subtype) =
        (t i.castSucc).comap (t i.succ).subtype := by
    ext x
    simp [e, RelSeries.smash_castAdd]
  simpa [compositionSeriesFactor] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.castAdd s.length).castSucc).comap
        ((t.smash s h) (i.castAdd s.length).succ).subtype)
      ((t i.castSucc).comap (t i.succ).subtype) e hmap)

/-- Helper for Exercise 14-14.5-4: smashing composition series preserves the factors coming from
the right block. -/
private noncomputable def compositionSeriesFactor_smash_right_equiv
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin s.length) :
    compositionSeriesFactor (k := k) (G := G) (t.smash s h) (i.natAdd t.length) ≃ₗ[k[G]]
      compositionSeriesFactor (k := k) (G := G) s i := by
  -- The right block also survives unchanged after translating the endpoints through the smash.
  have hsucc :
      (t.smash s h) (i.natAdd t.length).succ = s i.succ := by
    simpa using (RelSeries.smash_succ_natAdd (p := t) (q := s) h i)
  let e :
      (t.smash s h) (i.natAdd t.length).succ ≃ₗ[k[G]] s i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.natAdd t.length).succ →ₗ[k[G]] s i.succ)
          (((t.smash s h) (i.natAdd t.length).castSucc).comap
            ((t.smash s h) (i.natAdd t.length).succ).subtype) =
        (s i.castSucc).comap (s i.succ).subtype := by
    ext x
    simp [e, -Fin.castSucc_natAdd, RelSeries.smash_natAdd]
  simpa [compositionSeriesFactor] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.natAdd t.length).castSucc).comap
        ((t.smash s h) (i.natAdd t.length).succ).subtype)
      ((s i.castSucc).comap (s i.succ).subtype) e hmap)

/-- Helper for Exercise 14-14.5-4: the `i`-th factor of a composition series matches the fixed
simple module `T`. -/
private def compositionSeriesFactorMatches
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) : Prop :=
  Nonempty (compositionSeriesFactor (k := k) (G := G) s i ≃ₗ[k[G]] T)

/-- Helper for Exercise 14-14.5-4: the number of factors in a composition series that are
isomorphic to the fixed simple module `T`. -/
private noncomputable def simple_factor_count_of_module
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) : ℕ :=
  Nat.card { i : Fin s.length // compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i }

/-- Helper for Exercise 14-14.5-4: transporting a factor quotient across a linear equivalence
preserves the property of matching the fixed simple module `T`. -/
private theorem compositionSeriesFactorMatches_iff_of_linearEquiv
    {T A B : Type*} [AddCommGroup T] [AddCommGroup A] [AddCommGroup B]
    [Module k[G] T] [Module k[G] A] [Module k[G] B] (e : A ≃ₗ[k[G]] B) :
    Nonempty (A ≃ₗ[k[G]] T) ↔ Nonempty (B ≃ₗ[k[G]] T) := by
  constructor
  · intro hA
    rcases hA with ⟨eA⟩
    exact ⟨e.symm.trans eA⟩
  · intro hB
    rcases hB with ⟨eB⟩
    exact ⟨e.trans eB⟩

/-- Helper for Exercise 14-14.5-4: equivalent composition series have the same count of
`T`-factors. -/
private theorem simple_factor_count_series_equiv
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    {s₁ s₂ : CompositionSeries (Submodule k[G] M)} (h : s₁.Equivalent s₂) :
    simple_factor_count_of_module (k := k) (G := G) (T := T) s₁ =
      simple_factor_count_of_module (k := k) (G := G) (T := T) s₂ := by
  classical
  let e :
      { i : Fin s₁.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s₁ i } ≃
        { j : Fin s₂.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s₂ j } :=
    { toFun := fun i => ⟨h.choose i.1, by
        rcases h.choose_spec i.1 with ⟨ei⟩
        exact (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T) ei).1
          i.2⟩
      invFun := fun j => ⟨h.choose.symm j.1, by
        rcases h.choose_spec (h.choose.symm j.1) with ⟨ej⟩
        have hj : h.choose (h.choose.symm j.1) = j.1 := by
          simp
        have ej' :
            compositionSeriesFactor (k := k) (G := G) s₁ (h.choose.symm j.1) ≃ₗ[k[G]]
              compositionSeriesFactor (k := k) (G := G) s₂
                (h.choose (h.choose.symm j.1)) := by
          simpa [compositionSeriesFactor] using ej
        have hmatch :
            compositionSeriesFactorMatches (k := k) (G := G) (T := T) s₂
              (h.choose (h.choose.symm j.1)) := by
          simpa [hj] using j.2
        exact
          (compositionSeriesFactorMatches_iff_of_linearEquiv
            (k := k) (G := G) (T := T) ej').2 hmatch⟩
      left_inv := by
        intro i
        ext
        simp
      right_inv := by
        intro j
        ext
        simp }
  simpa [simple_factor_count_of_module] using Nat.card_congr e

/-- Helper for Exercise 14-14.5-4: mapping a factor quotient along an injective linear map
identifies it with the corresponding factor quotient in the mapped composition series. -/
private noncomputable def compositionSeriesFactor_map_equiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    [Module k[G] M] [Module k[G] N] [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) (i : Fin s.length) :
    compositionSeriesFactor (k := k) (G := G) s i ≃ₗ[k[G]]
      compositionSeriesFactor (k := k) (G := G)
        (s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩) i := by
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
  simpa [compositionSeriesFactor] using
    (Submodule.Quotient.equiv
      ((s (Fin.castSucc i)).comap (s i.succ).subtype)
      ((Submodule.map f (s (Fin.castSucc i))).comap (Submodule.map f (s i.succ)).subtype)
      e hmap)

/-- Helper for Exercise 14-14.5-4: mapping a composition series along an injective linear map
preserves the count of `T`-factors. -/
private theorem simple_factor_count_series_map
    {T M N : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N]
    [Module k[G] T] [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) :
    simple_factor_count_of_module (k := k) (G := G) (T := T)
        (s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩) =
      simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
  -- The mapped series has the same factors, so only the ambient submodules changed.
  let e :
      { i : Fin s.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i } ≃
        { i : Fin s'.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s' i } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_map_equiv (k := k) (G := G) hf s i.1)).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_map_equiv (k := k) (G := G) hf s i.1)).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module, s'] using (Nat.card_congr e).symm

/-- Helper for Exercise 14-14.5-4: comapping along a surjective linear map identifies factor
quotients with the original factors. -/
private noncomputable def compositionSeriesFactor_comap_equiv
    {M Q : Type*} [AddCommGroup M] [AddCommGroup Q] [Module k M] [Module k Q]
    [Module k[G] M] [Module k[G] Q] [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) (i : Fin s.length) :
    compositionSeriesFactor (k := k) (G := G)
        (s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩) i
      ≃ₗ[k[G]] compositionSeriesFactor (k := k) (G := G) s i := by
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

/-- Helper for Exercise 14-14.5-4: comapping a composition series along a surjective linear map
preserves the count of `T`-factors. -/
private theorem simple_factor_count_series_comap
    {T M Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k Q] [Module k[G] M] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) :
    simple_factor_count_of_module (k := k) (G := G) (T := T)
        (s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩) =
      simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
  -- The comapped series has the same quotients after pushing them through the quotient map.
  let e :
      { i : Fin s'.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s' i } ≃
        { i : Fin s.length //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_comap_equiv (k := k) (G := G) hg s i.1)).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_comap_equiv (k := k) (G := G) hg s i.1)).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module, s'] using Nat.card_congr e

/-- Helper for Exercise 14-14.5-4: finite-dimensional `k[G]`-modules have finite length. -/
private theorem isFiniteLength_of_groupAlgebra_module
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    IsFiniteLength k[G] M := by
  -- Restricting scalars along the finite extension preserves both noetherian and artinian
  -- conditions, so Jordan-Hölder applies.
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- Helper for Exercise 14-14.5-4: choose a composition series from `⊥` to `⊤` for a finite
`k[G]`-module after restricting scalars to `k`. -/
private noncomputable def finiteLengthCompositionSeries
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    CompositionSeries (Submodule k[G] M) :=
  Classical.choose
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module (k := k) (G := G) M))

/-- Helper for Exercise 14-14.5-4: the chosen finite-length composition series starts at `⊥`. -/
private theorem finiteLengthCompositionSeries_head
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries (k := k) (G := G) M).head = ⊥ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module (k := k) (G := G) M))).1

/-- Helper for Exercise 14-14.5-4: the chosen finite-length composition series ends at `⊤`. -/
private theorem finiteLengthCompositionSeries_last
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries (k := k) (G := G) M).last = ⊤ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module (k := k) (G := G) M))).2

/-- Helper for Exercise 14-14.5-4: the multiplicity of `T` in a finite `k[G]`-module, computed by
counting matching factors in a chosen composition series. -/
private noncomputable def simple_factor_multiplicity
    (T : Type*) [AddCommGroup T] [Module k[G] T]
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] : ℕ :=
  simple_factor_count_of_module (k := k) (G := G) (T := T)
    (finiteLengthCompositionSeries (k := k) (G := G) M)

/-- Helper for Exercise 14-14.5-4: the chosen-series multiplicity agrees with the count computed
from any other composition series with endpoints `⊥` and `⊤`. -/
private theorem simple_factor_multiplicity_eq_count
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [FiniteDimensional k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    simple_factor_multiplicity (k := k) (G := G) T M =
      simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
  -- Jordan-Hölder identifies the chosen composition series with any other one having the same
  -- endpoints, so the fixed-simple factor count is independent of the chosen series.
  exact simple_factor_count_series_equiv (k := k) (G := G) (T := T)
    (CompositionSeries.jordan_holder
      (finiteLengthCompositionSeries (k := k) (G := G) M) s
      ((finiteLengthCompositionSeries_head (k := k) (G := G) M).trans hs_head.symm)
      ((finiteLengthCompositionSeries_last (k := k) (G := G) M).trans hs_last.symm))

/-- Helper for Exercise 14-14.5-4: in an exact sequence, the mapped left series and comapped
right series meet at the exact seam. -/
private theorem compositionSeries_map_last_eq_comap_head_of_exact
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

/-- Helper for Exercise 14-14.5-4: the count of `T`-factors in a smashed composition series is
the sum of the counts in the two blocks. -/
private theorem simple_factor_count_series_smash
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) :
    simple_factor_count_of_module (k := k) (G := G) (T := T) (t.smash s h) =
      simple_factor_count_of_module (k := k) (G := G) (T := T) t +
        simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
  classical
  have hpred :
      ∀ l : Fin (t.length + s.length),
        compositionSeriesFactorMatches (k := k) (G := G) (T := T) (t.smash s h) l ↔
          match finSumFinEquiv.symm l with
          | Sum.inl i => compositionSeriesFactorMatches (k := k) (G := G) (T := T) t i
          | Sum.inr i => compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i := by
    intro l
    cases hl : finSumFinEquiv.symm l with
    | inl i =>
        have hl' : l = i.castAdd s.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_castAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_smash_left_equiv (k := k) (G := G) t s h i))
    | inr i =>
        have hl' : l = i.natAdd t.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_natAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv (k := k) (G := G) (T := T)
            (compositionSeriesFactor_smash_right_equiv (k := k) (G := G) t s h i))
  let e :
      { l : Fin (t.length + s.length) //
          compositionSeriesFactorMatches (k := k) (G := G) (T := T) (t.smash s h) l } ≃
        ({ i : Fin t.length //
            compositionSeriesFactorMatches (k := k) (G := G) (T := T) t i } ⊕
          { i : Fin s.length //
            compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i }) :=
    ((finSumFinEquiv.symm).subtypeEquiv hpred).trans
      (Equiv.subtypeSum
        (p := fun u : Fin t.length ⊕ Fin s.length =>
          match u with
          | Sum.inl i => compositionSeriesFactorMatches (k := k) (G := G) (T := T) t i
          | Sum.inr i => compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i))
  -- The matching factors split into the disjoint left and right blocks.
  calc
    simple_factor_count_of_module (k := k) (G := G) (T := T) (t.smash s h) =
        Nat.card
          ({ i : Fin t.length //
              compositionSeriesFactorMatches (k := k) (G := G) (T := T) t i } ⊕
            { i : Fin s.length //
              compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i }) := by
          simpa [simple_factor_count_of_module] using Nat.card_congr e
    _ = simple_factor_count_of_module (k := k) (G := G) (T := T) t +
        simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
          rw [simple_factor_count_of_module, simple_factor_count_of_module, Nat.card_sum]

/-- Helper for Exercise 14-14.5-4: fixed-simple multiplicity is additive in short exact
sequences of finite `k[G]`-modules. -/
private theorem simple_factor_multiplicity_eq_add_of_exact
    {T M N Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k N] [Module k Q]
    [FiniteDimensional k M] [FiniteDimensional k N] [FiniteDimensional k Q]
    [Module k[G] M] [Module k[G] N] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N] [IsScalarTower k k[G] Q]
    {f : N →ₗ[k[G]] M} {g : M →ₗ[k[G]] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    simple_factor_multiplicity (k := k) (G := G) T M =
      simple_factor_multiplicity (k := k) (G := G) T N +
        simple_factor_multiplicity (k := k) (G := G) T Q := by
  let t : CompositionSeries (Submodule k[G] N) :=
    finiteLengthCompositionSeries (k := k) (G := G) N
  let s : CompositionSeries (Submodule k[G] Q) :=
    finiteLengthCompositionSeries (k := k) (G := G) Q
  let t' : CompositionSeries (Submodule k[G] M) :=
    t.map ⟨Submodule.map f, fun {_ _} h => Submodule.map_covBy_of_injective hf h⟩
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {_ _} h => Submodule.comap_covBy_of_surjective hg h⟩
  let hseam : t'.last = s'.head :=
    compositionSeries_map_last_eq_comap_head_of_exact (k := k) (G := G) hf hg hfg
      t (finiteLengthCompositionSeries_last (k := k) (G := G) N)
      s (finiteLengthCompositionSeries_head (k := k) (G := G) Q)
  let r : CompositionSeries (Submodule k[G] M) := t'.smash s' hseam
  have ht_head : t.head = ⊥ :=
    finiteLengthCompositionSeries_head (k := k) (G := G) N
  have hs_last : s.last = ⊤ :=
    finiteLengthCompositionSeries_last (k := k) (G := G) Q
  -- Route correction: prove additivity at the series level on `r := t'.smash s' hseam`, then
  -- transport back to the chosen multiplicities on `N`, `M`, and `Q`.
  calc
    simple_factor_multiplicity (k := k) (G := G) T M =
        simple_factor_count_of_module (k := k) (G := G) (T := T) r := by
          apply simple_factor_multiplicity_eq_count (k := k) (G := G) (T := T) r
          · simpa [r, t', t, ht_head, -Submodule.map_bot] using Submodule.map_bot f
          · simpa [r, s', s, hs_last, -Submodule.comap_top] using Submodule.comap_top g
    _ = simple_factor_count_of_module (k := k) (G := G) (T := T) t' +
        simple_factor_count_of_module (k := k) (G := G) (T := T) s' := by
          simp [r, simple_factor_count_series_smash]
    _ = simple_factor_count_of_module (k := k) (G := G) (T := T) t +
        simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
          rw [simple_factor_count_series_map (k := k) (G := G) (T := T) hf t,
            simple_factor_count_series_comap (k := k) (G := G) (T := T) hg s]
    _ = simple_factor_multiplicity (k := k) (G := G) T N +
        simple_factor_multiplicity (k := k) (G := G) T Q := by
          rw [← simple_factor_multiplicity_eq_count (k := k) (G := G) (T := T) t
              ht_head
              (finiteLengthCompositionSeries_last (k := k) (G := G) N),
            ← simple_factor_multiplicity_eq_count (k := k) (G := G) (T := T) s
              (finiteLengthCompositionSeries_head (k := k) (G := G) Q)
              hs_last]

/-- Helper for Exercise 14-14.5-4: a subtype of `Fin 1` is either empty or has one element,
according to whether the unique index satisfies the defining predicate. -/
private theorem nat_card_subtype_fin_one_eq_ite
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

/-- Helper for Exercise 14-14.5-4: a simple module contributes exactly one copy of itself to its
two-step composition series `⊥ < ⊤`. -/
private theorem simple_factor_multiplicity_simple_eq_one
    {T : Type*} [AddCommGroup T] [Module k T] [FiniteDimensional k T] [Module k[G] T]
    [IsScalarTower k k[G] T] (hT : IsSimpleModule k[G] T) :
    simple_factor_multiplicity (k := k) (G := G) T T = 1 := by
  have hcov : (⊥ : Submodule k[G] T) ⋖ ⊤ := by
    -- Execute the source proof directly on the explicit two-step series `⊥ < ⊤`.
    rw [covBy_iff_quot_is_simple bot_le]
    let eTop :
        ((⊤ : Submodule k[G] T) ⧸
          Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] T))
            (⊥ : Submodule k[G] T)) ≃ₗ[k[G]] T :=
      (Submodule.quotEquivOfEqBot _ (by simp)).trans Submodule.topEquiv
    exact (LinearEquiv.isSimpleModule_iff eTop).2 hT
  let s : CompositionSeries (Submodule k[G] T) :=
    (RelSeries.singleton _ (⊥ : Submodule k[G] T)).snoc ⊤ hcov
  have hs_head : s.head = ⊥ := by
    simpa [s] using
      (RelSeries.head_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] T)) ⊤ hcov)
  have hs_last : s.last = ⊤ := by
    simpa [s] using
      (RelSeries.last_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] T)) ⊤ hcov)
  have hslen : s.length = 1 := by
    simp [s]
  let i0 : Fin s.length := hslen.symm ▸ (0 : Fin 1)
  have hmult :
      simple_factor_multiplicity (k := k) (G := G) T T =
        simple_factor_count_of_module (k := k) (G := G) (T := T) s := by
    -- Replace the chosen Jordan-Hölder series by the explicit two-step simple series.
    exact simple_factor_multiplicity_eq_count (k := k) (G := G) (T := T) s hs_head hs_last
  have hfactor :
      compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i0 := by
    let eId : T ≃ₗ[k[G]] T := LinearEquiv.refl _ _
    exact ⟨by
      simpa [s, i0, hslen, compositionSeriesFactor] using
        ((Submodule.quotEquivOfEqBot
            (Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] T))
              (⊥ : Submodule k[G] T)) (by simp)).trans
          (Submodule.topEquiv.trans eId))⟩
  have hcount :
      simple_factor_count_of_module (k := k) (G := G) (T := T) s = 1 := by
    classical
    let P : Fin 1 → Prop := fun i ↦
      compositionSeriesFactorMatches (k := k) (G := G) (T := T) s (hslen.symm ▸ i)
    let eCount :
        { i : Fin s.length //
            compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i } ≃
          { i : Fin 1 // P i } :=
      { toFun := fun i => ⟨Equiv.cast (congrArg Fin hslen) i.1, by simpa [P] using i.2⟩
        invFun := fun i => ⟨Equiv.cast (congrArg Fin hslen.symm) i.1, by simpa [P] using i.2⟩
        left_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp
        right_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp }
    have hP : ∀ i : Fin 1, P i := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [P, i0] using hfactor
    calc
      simple_factor_count_of_module (k := k) (G := G) (T := T) s =
          Nat.card { i : Fin 1 // P i } := by
            rw [simple_factor_count_of_module]
            exact Nat.card_congr eCount
      _ = if P 0 then 1 else 0 := nat_card_subtype_fin_one_eq_ite P
      _ = 1 := by simp [hP 0]
  simpa [hcount] using hmult

/-- Helper for Exercise 14-14.5-4: a factor count at least `2` yields two distinct indices with
matching factors. -/
private theorem exists_two_distinct_simple_factor_indices_of_count_ge_two
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M))
    (hcount : 2 ≤ simple_factor_count_of_module (k := k) (G := G) (T := T) s) :
    ∃ i j : Fin s.length,
      i ≠ j ∧
        compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i ∧
        compositionSeriesFactorMatches (k := k) (G := G) (T := T) s j := by
  classical
  let A := { i : Fin s.length // compositionSeriesFactorMatches (k := k) (G := G) (T := T) s i }
  have hcardA : 2 ≤ Fintype.card A := by
    simpa [A, simple_factor_count_of_module] using hcount
  have hA_nonempty : Nonempty A := by
    exact (Fintype.card_pos_iff.1 (lt_of_lt_of_le (by decide : 0 < 2) hcardA))
  let a : A := Classical.choice hA_nonempty
  have hone : 1 < Fintype.card A := lt_of_lt_of_le (by decide : 1 < 2) hcardA
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hone a
  refine ⟨a.1, b.1, ?_, a.2, b.2⟩
  intro hij
  apply hb
  exact Subtype.ext hij.symm

/-- Helper for Exercise 14-14.5-4: a nonzero map out of a simple module is injective. -/
private theorem simple_nonzero_hom_injective
    {T : Type*} [AddCommGroup T] [Module k[G] T]
    (hS : IsSimpleModule k[G] S) {i : S →ₗ[k[G]] T} (hi : i ≠ 0) :
    Function.Injective i := by
  -- The kernel is either `⊥` or `⊤`; the latter would force the map itself to vanish.
  letI : IsSimpleModule k[G] S := hS
  intro x y hxy
  by_cases hxy' : x - y = 0
  · exact sub_eq_zero.mp hxy'
  · exfalso
    have hmem : x - y ∈ LinearMap.ker i := by
      simp [LinearMap.mem_ker, map_sub, hxy]
    rcases (isSimpleModule_iff k[G] S).mp hS |>.eq_bot_or_eq_top (LinearMap.ker i) with hker | hker
    · exact hxy' (by simpa [hker] using hmem)
    · have hzero : i = 0 := by
        ext z
        have hz : z ∈ LinearMap.ker i := by simpa [hker]
        simpa [LinearMap.mem_ker] using hz
      exact hi hzero

/-- Helper for Exercise 14-14.5-4: the source of a projective envelope of a simple module is
cyclic, hence finite over `k[G]`. -/
private theorem projectiveEnvelope_simple_source_finite
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : IsSimpleModule k[G] S := hS
  letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨x, hx⟩ := hf.surjective s
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hs <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives finite generation.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 14-14.5-4: a finite `k[G]`-module is finite over `k` after restricting
scalars along `k → k[G]`. -/
private theorem groupAlgebra_moduleFinite_restrictScalars
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (hM : Module.Finite k[G] M) :
    Module.Finite k M := by
  -- The group algebra is finite over `k`, so transitivity of finite generation gives the result.
  letI : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  letI : Module.Finite k[G] M := hM
  exact Module.Finite.trans k[G] M

/-- Helper for Exercise 14-14.5-4: the source of a projective envelope of a simple module is
indecomposable. -/
private theorem projectiveEnvelope_simple_target_indecomposable
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope) :
    Indecomposable (ModuleCat.of k[G] P) := by
  letI : IsSimpleModule k[G] S := hS
  refine ⟨?_, ?_⟩
  · -- A zero source would force the simple target to be subsingleton.
    intro hPzero
    have hPsub : Subsingleton P := (ModuleCat.isZero_iff_subsingleton).1 hPzero
    letI : Subsingleton P := hPsub
    have hSsub : Subsingleton S := hf.surjective.subsingleton
    letI : Subsingleton S := hSsub
    exact (not_nontrivial S) (IsSimpleModule.nontrivial (R := k[G]) (M := S))
  · intro Y Z e
    -- Route correction: work directly with the essential map to the simple target.
    let eProd : P ≃ₗ[k[G]] (Y × Z) := (e ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
    let g : Y × Z →ₗ[k[G]] S := f.comp eProd.symm.toLinearMap
    have hg : g.IsEssential := by
      simpa [g, eProd] using
        (LinearMap.isEssential_iff_conj eProd (LinearEquiv.refl k[G] S)).2 hf.toIsEssential
    have hgsurj : Function.Surjective g := by
      intro s
      rcases hf.surjective s with ⟨p, hp⟩
      exact ⟨eProd p, by simpa [g] using hp⟩
    have hcoprod :
        LinearMap.coprod (g.comp (LinearMap.inl k[G] Y Z))
            (g.comp (LinearMap.inr k[G] Y Z)) = g := by
      ext y z <;> simp [g]
    have hRangeTop : LinearMap.range g = ⊤ := LinearMap.range_eq_top.2 hgsurj
    have hLeftSimple :
        LinearMap.range (g.comp (LinearMap.inl k[G] Y Z)) = ⊥ ∨
          LinearMap.range (g.comp (LinearMap.inl k[G] Y Z)) = ⊤ := by
      exact (isSimpleModule_iff k[G] S).1 inferInstance |>.eq_bot_or_eq_top _
    rcases hLeftSimple with hLeftBot | hLeftTop
    · left
      have hRangeRight : LinearMap.range (g.comp (LinearMap.inr k[G] Y Z)) = ⊤ := by
        rw [← hcoprod, LinearMap.range_coprod, hLeftBot, bot_sup_eq] at hRangeTop
        exact hRangeTop
      have hAxisTop :
          ((⊥ : Submodule k[G] Y).prod (⊤ : Submodule k[G] Z)).map g = ⊤ := by
        calc
          ((⊥ : Submodule k[G] Y).prod (⊤ : Submodule k[G] Z)).map g =
              ((⊥ : Submodule k[G] Y).map (g.comp (LinearMap.inl k[G] Y Z))) ⊔
                ((⊤ : Submodule k[G] Z).map (g.comp (LinearMap.inr k[G] Y Z))) := by
              rw [← hcoprod, LinearMap.map_coprod_prod]
              simp
          _ = LinearMap.range (g.comp (LinearMap.inr k[G] Y Z)) := by
              rw [Submodule.map_bot, bot_sup_eq, LinearMap.range_eq_map]
          _ = ⊤ := hRangeRight
      have hAxisEqTop : ((⊥ : Submodule k[G] Y).prod (⊤ : Submodule k[G] Z)) = ⊤ :=
        hg.eq_top_of_map_eq_top _ hAxisTop
      have hYsub : Subsingleton Y := by
        refine ⟨fun y y' ↦ ?_⟩
        have hy : (y - y', 0) ∈ ((⊥ : Submodule k[G] Y).prod (⊤ : Submodule k[G] Z)) := by
          simp [hAxisEqTop]
        exact sub_eq_zero.mp (by simpa using hy.1)
      exact (ModuleCat.isZero_iff_subsingleton).2 hYsub
    · right
      have hAxisTop :
          ((⊤ : Submodule k[G] Y).prod (⊥ : Submodule k[G] Z)).map g = ⊤ := by
        calc
          ((⊤ : Submodule k[G] Y).prod (⊥ : Submodule k[G] Z)).map g =
              ((⊤ : Submodule k[G] Y).map (g.comp (LinearMap.inl k[G] Y Z))) ⊔
                ((⊥ : Submodule k[G] Z).map (g.comp (LinearMap.inr k[G] Y Z))) := by
              rw [← hcoprod, LinearMap.map_coprod_prod]
              simp
          _ = LinearMap.range (g.comp (LinearMap.inl k[G] Y Z)) := by
              rw [Submodule.map_bot, sup_bot_eq, LinearMap.range_eq_map]
          _ = ⊤ := hLeftTop
      have hAxisEqTop : ((⊤ : Submodule k[G] Y).prod (⊥ : Submodule k[G] Z)) = ⊤ :=
        hg.eq_top_of_map_eq_top _ hAxisTop
      have hZsub : Subsingleton Z := by
        refine ⟨fun z z' ↦ ?_⟩
        have hz : (0, z - z') ∈ ((⊤ : Submodule k[G] Y).prod (⊥ : Submodule k[G] Z)) := by
          simp [hAxisEqTop]
        exact sub_eq_zero.mp (by simpa using hz.2)
      exact (ModuleCat.isZero_iff_subsingleton).2 hZsub

/-- Helper for Exercise 14-14.5-4: if the embedded simple copy met the projective-envelope map
nontrivially, the envelope would split and the simple module would be projective. -/
private theorem embedding_range_le_ker_of_nonprojective
    {f : P →ₗ[k[G]] S} {i : S →ₗ[k[G]] P}
    (hS : IsSimpleModule k[G] S) (hi : Function.Injective i) (hf : f.IsProjectiveEnvelope)
    (hS_not_projective : ¬ Module.Projective k[G] S) :
    LinearMap.range i ≤ LinearMap.ker f := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  by_contra hnot
  have hcomp_ne_zero : f.comp i ≠ 0 := by
    intro hcomp_zero
    have hzero : (f.comp i) y = 0 := by simp [hcomp_zero]
    exact hnot <| by simpa [LinearMap.comp_apply, LinearMap.mem_ker] using hzero
  letI : IsSimpleModule k[G] S := hS
  -- Schur's lemma turns the nonzero endomorphism `f ∘ i` of the simple module into an isomorphism.
  have hbij : Function.Bijective (f.comp i) := LinearMap.bijective_of_ne_zero hcomp_ne_zero
  let e : S ≃ₗ[k[G]] S := LinearEquiv.ofBijective (f.comp i) hbij
  let s : S →ₗ[k[G]] P := i.comp e.symm.toLinearMap
  have hs_split : f.comp s = LinearMap.id := by
    ext z
    change (f.comp i) (e.symm z) = z
    exact e.apply_symm_apply z
  have hS_projective : Module.Projective k[G] S := Module.Projective.of_split s f hs_split
  exact hS_not_projective hS_projective

-- Proof sketch: apply Exercise `14-14.5-3` with `E = P` and `F = S`. The projective-envelope map
-- gives a nonzero element of `P →ₗ[k[G]] S`, so the Hom-dimension symmetry forces a nonzero map
-- `S →ₗ[k[G]] P`; simplicity of `S` makes that map injective.
/-- Exercise 14-14.5-4: a projective envelope of a simple `k[G]`-module contains a submodule
isomorphic to that simple module. -/
theorem exists_injective_hom_to_projectiveEnvelope_of_simple
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope) :
    ∃ i : S →ₗ[k[G]] P, Function.Injective i := by
  letI : Module k P := Module.compHom P (algebraMap k k[G])
  letI : Module k S := Module.compHom S (algebraMap k k[G])
  letI : IsScalarTower k k[G] P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower k k[G] S := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Projective k[G] P := hf.toProjective
  let hP_finite : Module.Finite k[G] P := projectiveEnvelope_simple_source_finite (hS := hS) hf
  let hS_finite : Module.Finite k[G] S := Module.Finite.of_surjective f hf.surjective
  letI : FiniteDimensional k P :=
    groupAlgebra_moduleFinite_restrictScalars (k := k) (G := G) hP_finite
  letI : FiniteDimensional k S :=
    groupAlgebra_moduleFinite_restrictScalars (k := k) (G := G) hS_finite
  have hf_ne : f ≠ 0 := by
    -- The projective-envelope map cannot vanish because it is surjective onto a nonzero simple
    -- target.
    intro hf_zero
    letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    rcases hf.surjective s with ⟨p, hp⟩
    exact hs <| by simpa [hf_zero] using hp.symm
  have hleft_pos : 0 < Module.finrank k (P →ₗ[k[G]] S) := by
    have hNotSub : ¬ Subsingleton (P →ₗ[k[G]] S) := by
      intro hsub
      exact hf_ne (Subsingleton.elim _ _)
    letI : Nontrivial (P →ₗ[k[G]] S) := not_subsingleton_iff_nontrivial.mp hNotSub
    exact Module.finrank_pos
  have hswap :=
    finrank_hom_eq_finrank_hom_swap_of_projective
      (k := k) (G := G) (E := P) (F := S)
  have hright_pos : 0 < Module.finrank k (S →ₗ[k[G]] P) := by
    rw [← hswap]
    exact hleft_pos
  letI : Nontrivial (S →ₗ[k[G]] P) := Module.finrank_pos_iff.mp hright_pos
  obtain ⟨i, hi_ne⟩ := exists_ne (0 : S →ₗ[k[G]] P)
  -- Exercise `14-14.5-3` provides a nonzero map back into the envelope; simplicity makes it
  -- injective.
  exact ⟨i, simple_nonzero_hom_injective (hS := hS) hi_ne⟩

-- Proof sketch: combine the previous embedding of `S` into `P` with the projective-envelope map
-- `P → S`. Since `P` is projective, Exercise `14-14.3-5` identifies it as injective; simplicity
-- of `S` and essentiality of the projective envelope force the resulting embedding to be an
-- essential extension.
/-- A projective envelope of a simple `k[G]`-module is also an injective envelope of that simple
module. -/
theorem exists_isInjectiveEnvelope_of_isProjectiveEnvelope_of_simple
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope) :
    ∃ i : S →ₗ[k[G]] P, i.IsInjectiveEnvelope := by
  letI : Module.Projective k[G] P := hf.toProjective
  obtain ⟨i, hi⟩ :=
    exists_injective_hom_to_projectiveEnvelope_of_simple (k := k) (G := G) (hS := hS) hf
  have hi_ne : i ≠ 0 := by
    -- An injective map out of a nontrivial simple module is nonzero.
    intro hi_zero
    letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    exact hs <| hi <| by simpa [hi_zero]
  have hP_indec :=
    projectiveEnvelope_simple_target_indecomposable (k := k) (G := G) (hS := hS) hf
  obtain ⟨T, j, hT_simple, hj⟩ :=
    indecomposable_projective_groupAlgebra_module_exists_simple_injectiveEnvelope
      (k := k) (G := G) (P := ModuleCat.of k[G] P) hP_indec
  letI : Simple T := hT_simple
  letI : IsSimpleModule k[G] T := by infer_instance
  have hi_rangeRestrict_injective : Function.Injective i.rangeRestrict := by
    intro x y hxy
    exact hi (congrArg Subtype.val hxy)
  have hj_rangeRestrict_injective : Function.Injective j.hom.rangeRestrict := by
    intro x y hxy
    exact hj.injective (congrArg Subtype.val hxy)
  let eRangeI : S ≃ₗ[k[G]] LinearMap.range i :=
    LinearEquiv.ofBijective i.rangeRestrict
      ⟨hi_rangeRestrict_injective, LinearMap.surjective_rangeRestrict i⟩
  let eRangeJ : T ≃ₗ[k[G]] LinearMap.range j.hom :=
    LinearEquiv.ofBijective j.hom.rangeRestrict
      ⟨hj_rangeRestrict_injective, LinearMap.surjective_rangeRestrict j.hom⟩
  letI : IsSimpleModule k[G] (LinearMap.range i) := IsSimpleModule.congr eRangeI.symm
  have hInf_ne_bot : LinearMap.range i ⊓ LinearMap.range j.hom ≠ ⊥ := by
    -- Essentiality forces every nonzero submodule, in particular `range i`, to meet `range j`.
    intro hInf
    have hRangeI_bot : LinearMap.range i = ⊥ :=
      hj.toIsEssentialExtension.eq_bot_of_inf_range_eq_bot _ hInf
    exact hi_ne <| by
      ext x
      have hx : i x ∈ LinearMap.range i := LinearMap.mem_range_self _ _
      rw [hRangeI_bot] at hx
      simpa using hx
  let K : Submodule k[G] (LinearMap.range i) := (LinearMap.range j.hom).submoduleOf (LinearMap.range i)
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    have hmap : Submodule.map (LinearMap.range i).subtype K = ⊥ := by
      simpa [K, hK_bot]
    have hInf : LinearMap.range i ⊓ LinearMap.range j.hom = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxK : (⟨x, hx.1⟩ : LinearMap.range i) ∈ K := by
          simpa [K] using hx.2
        have hxMap : x ∈ Submodule.map (LinearMap.range i).subtype K := by
          exact ⟨⟨x, hx.1⟩, hxK, rfl⟩
        rw [hmap] at hxMap
        simpa using hxMap
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        exact ⟨by simpa using LinearMap.mem_range_self i 0,
          by simpa using LinearMap.mem_range_self j.hom 0⟩
    exact hInf_ne_bot hInf
  have hK_top : K = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top K).resolve_left hK_ne_bot
  have hRangeI_le_rangeJ : LinearMap.range i ≤ LinearMap.range j.hom :=
    (Submodule.submoduleOf_eq_top).1 hK_top
  let iToRangeJ : S →ₗ[k[G]] LinearMap.range j.hom :=
    LinearMap.codRestrict (LinearMap.range j.hom) i
      (fun x ↦ hRangeI_le_rangeJ (LinearMap.mem_range_self i x))
  have hiToRangeJ_ne : iToRangeJ ≠ 0 := by
    intro hiToRangeJ_zero
    exact hi_ne <| by
      ext x
      exact congrArg Subtype.val (LinearMap.congr_fun hiToRangeJ_zero x)
  let φ : S →ₗ[k[G]] T := eRangeJ.symm.toLinearMap.comp iToRangeJ
  have hφ_ne : φ ≠ 0 := by
    intro hφ_zero
    have hiToRangeJ_zero : iToRangeJ = 0 := by
      ext x
      simpa [φ] using congrArg eRangeJ (LinearMap.congr_fun hφ_zero x)
    exact hiToRangeJ_ne hiToRangeJ_zero
  have hφ_injective : Function.Injective φ :=
    simple_nonzero_hom_injective (hS := hS) hφ_ne
  have hφ_range_ne_bot : LinearMap.range φ ≠ ⊥ := by
    intro hRange_bot
    exact hφ_ne <| by
      ext x
      have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self _ _
      rw [hRange_bot] at hx
      simpa using hx
  have hφ_range_top : LinearMap.range φ = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range φ)).resolve_left hφ_range_ne_bot
  let eST : S ≃ₗ[k[G]] T :=
    LinearEquiv.ofBijective φ ⟨hφ_injective, LinearMap.range_eq_top.1 hφ_range_top⟩
  refine ⟨j.hom.comp eST.toLinearMap, ?_⟩
  -- The injective-envelope structure is preserved because precomposing by an equivalence does not
  -- change the image submodule.
  refine
    { toInjective := hj.toInjective
      toIsEssentialExtension := ?_
      injective := hj.injective.comp eST.injective }
  refine ⟨fun N hN ↦ ?_⟩
  exact hj.toIsEssentialExtension.eq_bot_of_inf_range_eq_bot N (by simpa using hN)

/-- Helper for Exercise 14-14.5-4: LinearRepresentations_Serre_1977's two exact sequences force at least two occurrences of
the simple module `S` among the composition factors of the projective envelope `P`. -/
private theorem projective_envelope_simple_factor_count_ge_two
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope)
    {s : CompositionSeries (Submodule k[G] P)} (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (hS_not_projective : ¬ Module.Projective k[G] S) :
    2 ≤ simple_factor_count_of_module (k := k) (G := G) (T := S) s := by
  letI : Module k P := Module.compHom P (algebraMap k k[G])
  letI : Module k S := Module.compHom S (algebraMap k k[G])
  letI : IsScalarTower k k[G] P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower k k[G] S := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let hP_finite : Module.Finite k[G] P := projectiveEnvelope_simple_source_finite (hS := hS) hf
  let hS_finite : Module.Finite k[G] S := Module.Finite.of_surjective f hf.surjective
  letI : FiniteDimensional k P :=
    groupAlgebra_moduleFinite_restrictScalars (k := k) (G := G) hP_finite
  letI : FiniteDimensional k S :=
    groupAlgebra_moduleFinite_restrictScalars (k := k) (G := G) hS_finite
  obtain ⟨i, hi⟩ :=
    exists_injective_hom_to_projectiveEnvelope_of_simple (k := k) (G := G) (hS := hS) hf
  have hRange_le_ker :=
    embedding_range_le_ker_of_nonprojective
      (k := k) (G := G) (hS := hS) hi hf hS_not_projective
  let K : Submodule k[G] P := LinearMap.ker f
  let iKer : S →ₗ[k[G]] K :=
    LinearMap.codRestrict K i (fun x ↦ hRange_le_ker (LinearMap.mem_range_self i x))
  let Q : Type x := K ⧸ LinearMap.range iKer
  letI : FiniteDimensional k K :=
    FiniteDimensional.of_injective (K.subtype.restrictScalars k) Subtype.val_injective
  letI : FiniteDimensional k Q :=
    FiniteDimensional.of_surjective ((Submodule.mkQ (LinearMap.range iKer)).restrictScalars k)
      (Submodule.mkQ_surjective (LinearMap.range iKer))
  have hiKer_injective : Function.Injective iKer := by
    intro x y hxy
    exact hi (congrArg Subtype.val hxy)
  have hker_mult :
      simple_factor_multiplicity (k := k) (G := G) S K =
        simple_factor_multiplicity (k := k) (G := G) S S +
          simple_factor_multiplicity (k := k) (G := G) S Q := by
    -- The embedded copy `S ↪ ker f` contributes one outer simple term in LinearRepresentations_Serre_1977's model.
    simpa [Q, iKer] using
      (simple_factor_multiplicity_eq_add_of_exact (k := k) (G := G) (T := S)
        (f := iKer) (g := Submodule.mkQ (LinearMap.range iKer))
        hiKer_injective
        (Submodule.mkQ_surjective (LinearMap.range iKer))
        (LinearMap.exact_map_mkQ_range iKer))
  have hP_mult :
      simple_factor_multiplicity (k := k) (G := G) S P =
        simple_factor_multiplicity (k := k) (G := G) S K +
          simple_factor_multiplicity (k := k) (G := G) S S := by
    -- The quotient term from the projective-envelope map gives the second outer simple term.
    simpa [K] using
      (simple_factor_multiplicity_eq_add_of_exact (k := k) (G := G) (T := S)
        (f := K.subtype) (g := f)
        Subtype.val_injective hf.surjective (LinearMap.exact_subtype_ker_map f))
  have hmult_ge_two : 2 ≤ simple_factor_multiplicity (k := k) (G := G) S P := by
    -- Both exact sequences contribute a copy of `S`; the middle quotient only increases the count.
    rw [hP_mult, hker_mult,
      simple_factor_multiplicity_simple_eq_one (k := k) (G := G) (T := S) hS]
    omega
  rw [simple_factor_multiplicity_eq_count (k := k) (G := G) (T := S) s hs_head hs_last] at hmult_ge_two
  exact hmult_ge_two

-- Proof sketch: one composition factor is the simple quotient `S` coming from the projective
-- envelope map `P → S`; the first theorem gives a second factor arising from a simple submodule
-- `S ↪ P`. If `S` were projective these two appearances could collapse, so the nonprojectivity
-- hypothesis forces two distinct occurrences in any Jordan-Hölder series.
/-- Any composition series of a nonprojective projective envelope contains two distinct factors
isomorphic to the underlying simple module. -/
theorem simple_occurs_twice_in_compositionSeries_of_nonprojective_projectiveEnvelope
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope)
    {s : CompositionSeries (Submodule k[G] P)} (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (hS_not_projective : ¬ Module.Projective k[G] S) :
    ∃ i j : Fin s.length,
      i ≠ j ∧
        Nonempty
          (((s (Fin.succ i)) ⧸
              (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype) ≃ₗ[k[G]] S) ∧
        Nonempty
          (((s (Fin.succ j)) ⧸
              (s (Fin.castSucc j)).comap (s (Fin.succ j)).subtype) ≃ₗ[k[G]] S) := by
  -- Route correction: replace the fragile theorem-local `smash` bookkeeping by LinearRepresentations_Serre_1977's global
  -- invariant, namely the multiplicity of `S` among the Jordan-Hölder factors of `P`.
  have hcount_ge_two :=
    projective_envelope_simple_factor_count_ge_two
      (k := k) (G := G) (hS := hS) hf hs_head hs_last hS_not_projective
  rcases
      exists_two_distinct_simple_factor_indices_of_count_ge_two
        (k := k) (G := G) (T := S) s hcount_ge_two with
    ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, hi, hj⟩

end
