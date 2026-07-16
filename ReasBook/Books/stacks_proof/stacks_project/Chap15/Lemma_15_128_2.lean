import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import stacks_proof.stacks_project.Chap10.Lemma_10_10_2
import stacks_proof.stacks_project.Chap10.Lemma_10_78_9
import stacks_proof.stacks_project.Chap10.Lemma_10_79_1
import stacks_proof.stacks_project.Chap15.Situation_15_128_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: fibrewise linear algebra on the quotient fibre `M(x) = M / xM` at a closed point;
- owner declarations sampled for this file:
  `closedPointFiber`,
  `LocalizedModule.Away`,
  `LocalizedModule.map`,
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`;
- source-facing layer: the localized splitting-after-inverting predicate from the source statement,
  expressed against the chapter owner `V(x)` for the visible quotient of the fibre;
- core/canonical layer: the owner localization map `LocalizedModule.map` and the visible quotient
  owner declarations imported from `Situation_15_128_1`;
- bridge/view: the free localized source `LocalizedModule.Away f (Fin r → R)` is canonically a
  finite free `Localization.Away f`-module, but the source predicate is best phrased as a left
  inverse to the localized owner map rather than through a tensor-product presentation;
- primitive data: the closed point `x`, the chosen sections `s`, and the localization parameter
  `f`;
- derived API: the visible classes supplied by the chapter owner file and the localized splitting
  predicate below.
-/

local notation "Ω" => closedPoints (PrimeSpectrum R)

/-- The `R`-linear map sending the standard basis of `R^r` to the chosen sections. -/
private noncomputable abbrev selectedSectionsMap {r : ℕ} (s : Fin r → M) : (Fin r → R) →ₗ[R] M :=
  (Pi.basisFun R (Fin r)).constr R s

/-- The textbook condition that the sections `s₁, …, s_r` become the inclusion of a direct summand
after inverting some element away from the closed point `x`. -/
def selectedSectionsSplitAfterInverting {r : ℕ} (x : Ω) (s : Fin r → M) : Prop :=
  ∃ f : R, f ∉ x.1.asIdeal ∧
    ∃ ρ : LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f (Fin r → R),
      Function.LeftInverse ρ (LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))

section

variable [Module.FinitePresentation R M]

/-- Helper for Lemma 15.128.2: localizing the finite free module `R^r` away from `f` is the same
as taking coordinatewise values in the away-localized ring. -/
private noncomputable def localizedFreeSectionsEquivR {r : ℕ} (f : R) :
    LocalizedModule.Away f (Fin r → R) ≃ₗ[R] (Fin r → Localization.Away f) :=
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
    (LinearMap.pi fun i : Fin r ↦
      (Algebra.linearMap R (Localization.Away f)).comp (LinearMap.proj i))

/-- Helper for Lemma 15.128.2: the previous free-module localization equivalence is also linear
over `R_f = Localization.Away f`. -/
private noncomputable def localizedFreeSectionsEquiv {r : ℕ} (f : R) :
    LocalizedModule.Away f (Fin r → R) ≃ₗ[Localization.Away f] (Fin r → Localization.Away f) :=
  LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
    (localizedFreeSectionsEquivR (R := R) (r := r) f)

/-- Helper for Lemma 15.128.2: on a localized generator, the free-module equivalence just applies
the ring localization map in each coordinate. -/
private theorem localizedFreeSectionsEquivR_mk_apply {r : ℕ} (f : R) (v : Fin r → R) (i : Fin r) :
    localizedFreeSectionsEquivR (R := R) (r := r) f
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R)) v) i =
      algebraMap R (Localization.Away f) (v i) := by
  -- Evaluate the localization comparison on a source generator and then read off the `i`-th
  -- coordinate of the pointwise localized vector.
  simpa [localizedFreeSectionsEquivR] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
        (LinearMap.pi fun j : Fin r ↦
          (Algebra.linearMap R (Localization.Away f)).comp (LinearMap.proj j)) v) i

/-- Helper for Lemma 15.128.2: the section map sends the `i`-th standard basis vector of `R^r`
to the chosen section `s i`. -/
private theorem selectedSectionsMap_basisFun {r : ℕ} (s : Fin r → M) (i : Fin r) :
    selectedSectionsMap s ((Pi.basisFun R (Fin r)) i) = s i := by
  -- Expand the basis-induced map `selectedSectionsMap` and evaluate it on the `i`-th basis vector.
  simp [selectedSectionsMap]

/-- Helper for Lemma 15.128.2: for a finitely presented module `N`, localizing `Hom_R(N, R)`
identifies with `R`-linear maps from `N_f` to `R_f`. -/
private noncomputable def localizedLinearFormsEquivAway
    {N : Type*} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N] (f : R) :
    LocalizedModule.Away f (Module.Dual R N) ≃ₗ[R]
      (LocalizedModule.Away f N →ₗ[R] Localization.Away f) :=
  (Module.FinitePresentation.linearEquivMap (M := N) (N := R) (Submonoid.powers f)).trans
    ((IsLocalizedModule.linearEquiv (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
        (Algebra.linearMap R (Localization.Away f))).congrRight)

/-- Helper for Lemma 15.128.2: on source generators, the localized linear-forms comparison sends
the localization class of `φ : Nᘁ → R` to the obvious localized evaluation map. -/
private theorem localizedLinearFormsEquivAway_mk_apply
    {N : Type*} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (f : R) (φ : Module.Dual R N) (m : N) :
    localizedLinearFormsEquivAway (R := R) (N := N) f
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R N)) φ)
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) N) m) =
      algebraMap R (Localization.Away f) (φ m) := by
  -- First rewrite the finite-presentation comparison on a localized generator of `Hom_R(N, R)`.
  rw [localizedLinearFormsEquivAway, LinearEquiv.trans_apply,
    Module.FinitePresentation.linearEquivMap_apply]
  -- Then collapse the localized evaluation map back to the localized scalar `φ m`.
  change (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
      (Algebra.linearMap R (Localization.Away f)))
    (((IsLocalizedModule.map (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) R)) φ)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N) m)) =
    algebraMap R (Localization.Away f) (φ m)
  have hmap :
      ((IsLocalizedModule.map (Submonoid.powers f)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) R)) φ)
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) N) m) =
      (LocalizedModule.mkLinearMap (Submonoid.powers f) R) (φ m) := by
    -- `IsLocalizedModule.map` is characterized by commuting with the localization maps.
    simpa using
      LinearMap.congr_fun
        (IsLocalizedModule.map_comp (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) R) φ)
        m
  rw [hmap]
  simpa using
    (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
      (Algebra.linearMap R (Localization.Away f)) (φ m))

/-- Helper for Lemma 15.128.2: localizing global linear forms identifies `Hom_R(M, R)` after
inverting `f` with `R`-linear maps `M_f → R_f`. -/
private noncomputable abbrev localizedGlobalLinearFormsEquiv (f : R) :
    LocalizedModule.Away f (Module.Dual R M) ≃ₗ[R]
      (LocalizedModule.Away f M →ₗ[R] Localization.Away f) :=
  localizedLinearFormsEquivAway (R := R) (N := M) f

/-- Helper for Lemma 15.128.2: on denominator-`1` generators, the naturality square for
`localizedLinearFormsEquivAway` and `dualMap` evaluates to the same localized scalar on both
sides. -/
private theorem localizedLinearFormsEquivAway_map_dualMap_mk_apply
    {N₁ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.FinitePresentation R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂] [Module.FinitePresentation R N₂]
    (f : R) (l : N₁ →ₗ[R] N₂) (φ : Module.Dual R N₂) (m : N₁) :
    localizedLinearFormsEquivAway (R := R) (N := N₁) f
        (((LocalizedModule.map (Submonoid.powers f) l.dualMap).restrictScalars R)
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R N₂)) φ))
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N₁) m) =
      (LinearMap.lcomp R (Localization.Away f)
          ((LocalizedModule.map (Submonoid.powers f) l).restrictScalars R))
        (localizedLinearFormsEquivAway (R := R) (N := N₂) f
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R N₂)) φ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) N₁) m) := by
  -- Route correction: compute the naturality square only on denominator-`1` generators first, so
  -- both sides collapse to the same localized scalar `algebraMap _ _ (φ (l m))`.
  rw [LinearMap.lcomp_apply]
  change ((localizedLinearFormsEquivAway (R := R) (N := N₁) f)
      ((LocalizedModule.map (Submonoid.powers f) l.dualMap) (LocalizedModule.mk φ 1)))
      (LocalizedModule.mk m 1) =
    ((localizedLinearFormsEquivAway (R := R) (N := N₂) f) (LocalizedModule.mk φ 1))
      ((LocalizedModule.map (Submonoid.powers f) l) (LocalizedModule.mk m 1))
  rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
  calc
    ((localizedLinearFormsEquivAway (R := R) (N := N₁) f) (LocalizedModule.mk (l.dualMap φ) 1))
        (LocalizedModule.mk m 1)
        = algebraMap R (Localization.Away f) ((l.dualMap φ) m) := by
            simpa using
              localizedLinearFormsEquivAway_mk_apply
                (R := R) (N := N₁) f (l.dualMap φ) m
    _ = algebraMap R (Localization.Away f) (φ (l m)) := by
          simp [LinearMap.dualMap_apply]
    _ = ((localizedLinearFormsEquivAway (R := R) (N := N₂) f) (LocalizedModule.mk φ 1))
          (LocalizedModule.mk (l m) 1) := by
            symm
            simpa using
              localizedLinearFormsEquivAway_mk_apply
                (R := R) (N := N₂) f φ (l m)

/-- Helper for Lemma 15.128.2: the localized comparison for linear forms is natural with respect
to precomposition by an `R`-linear map. -/
private theorem localizedLinearFormsEquivAway_map_dualMap
    {N₁ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.FinitePresentation R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂] [Module.FinitePresentation R N₂]
    (f : R) (l : N₁ →ₗ[R] N₂) :
    localizedLinearFormsEquivAway (R := R) (N := N₁) f ∘ₗ
        (LocalizedModule.map (Submonoid.powers f) l.dualMap).restrictScalars R =
      LinearMap.lcomp R (Localization.Away f)
          ((LocalizedModule.map (Submonoid.powers f) l).restrictScalars R) ∘ₗ
        localizedLinearFormsEquivAway (R := R) (N := N₂) f := by
  let F :
      LocalizedModule.Away f (Module.Dual R N₂) →ₗ[R]
        (LocalizedModule.Away f N₁ →ₗ[R] Localization.Away f) :=
    localizedLinearFormsEquivAway (R := R) (N := N₁) f ∘ₗ
      (LocalizedModule.map (Submonoid.powers f) l.dualMap).restrictScalars R
  let G :
      LocalizedModule.Away f (Module.Dual R N₂) →ₗ[R]
        (LocalizedModule.Away f N₁ →ₗ[R] Localization.Away f) :=
    LinearMap.lcomp R (Localization.Away f)
        ((LocalizedModule.map (Submonoid.powers f) l).restrictScalars R) ∘ₗ
      localizedLinearFormsEquivAway (R := R) (N := N₂) f
  -- The universal property of localization first reduces the source equality to numerator
  -- generators in the localized dual module.
  have hcompare : F = G := by
    apply IsLocalizedModule.linearMap_ext (S := Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R N₂))
      ((localizedLinearFormsEquivAway (R := R) (N := N₁) f).toLinearMap.comp
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R N₁)))
    apply LinearMap.ext
    intro φ
    -- For each numerator dual class, equality of the resulting localized linear forms is again a
    -- localization-extensionality statement on denominator-`1` generators of `N₁`.
    apply IsLocalizedModule.linearMap_ext (S := Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N₁)
      (Algebra.linearMap R (Localization.Away f))
    apply LinearMap.ext
    intro m
    simpa [F, G, LinearMap.comp_apply] using
      localizedLinearFormsEquivAway_map_dualMap_mk_apply
        (R := R) (N₁ := N₁) (N₂ := N₂) f l φ m
  simpa [F, G] using hcompare

/-- Helper for Lemma 15.128.2: the quotient-ring-valued form induced by a global linear form
vanishes on `xM`, so it descends to the closed fiber `M(x)`. -/
private theorem closedPointFiberGlobalLinearFormQuotientBase_le_ker
    (x : Ω) (φ : Module.Dual R M) :
    x.1.asIdeal • (⊤ : Submodule R M) ≤
      LinearMap.ker (((Ideal.Quotient.mkₐ R x.1.asIdeal).toLinearMap).comp φ) := by
  -- Expand membership in `xM` and check directly that the quotient map kills every generator.
  intro m hm
  change (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ m) = 0
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr n hn
    simpa [Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul] using
      (Ideal.Quotient.eq_zero_iff_mem.2 <| x.1.asIdeal.mul_mem_right (φ n) hr :
        Ideal.Quotient.mk x.1.asIdeal (r * φ n) = 0)
  · intro a b ha hb
    calc
      (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ (a + b)) =
          (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ a) +
            (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ b) := by
            rw [map_add, map_add]
      _ = 0 := by rw [ha, hb, add_zero]

/-- Helper for Lemma 15.128.2: the induced quotient-ring-valued linear form on `M(x)`. -/
private noncomputable abbrev closedPointFiberGlobalLinearFormQuotientBase
    (x : Ω) (φ : Module.Dual R M) :
    M﹙x﹚ →ₗ[R] (R ⧸ x.1.asIdeal) :=
  ((x.1.asIdeal) • (⊤ : Submodule R M)).liftQ
    (((Ideal.Quotient.mkₐ R x.1.asIdeal).toLinearMap).comp φ)
    (closedPointFiberGlobalLinearFormQuotientBase_le_ker (R := R) (M := M) x φ)

/-- Helper for Lemma 15.128.2: the descended quotient-valued form is linear over `R / x`. -/
private theorem closedPointFiberGlobalLinearFormQuotient_map_smul
    (x : Ω) (φ : Module.Dual R M) :
    ∀ (c : R ⧸ x.1.asIdeal) (q : M﹙x﹚),
      closedPointFiberGlobalLinearFormQuotientBase (R := R) (M := M) x φ (c • q) =
        c • closedPointFiberGlobalLinearFormQuotientBase (R := R) (M := M) x φ q := by
  intro c q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine Quotient.inductionOn' q ?_
  intro m
  have hmk :
      Ideal.Quotient.mk x.1.asIdeal r • (Submodule.Quotient.mk m : M﹙x﹚) =
        (Submodule.Quotient.mk (r • m) : M﹙x﹚) :=
    (Module.Quotient.mk_smul_mk M x.1.asIdeal r m :
      Ideal.Quotient.mk x.1.asIdeal r •
          (Submodule.Quotient.mk m : M ⧸ x.1.asIdeal • (⊤ : Submodule R M)) =
        (Submodule.Quotient.mk (r • m) : M ⧸ x.1.asIdeal • (⊤ : Submodule R M)))
  -- Reduce to a representative of the quotient fiber and compare the two evaluations there.
  simpa [closedPointFiberGlobalLinearFormQuotientBase, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq] using
    congrArg (closedPointFiberGlobalLinearFormQuotientBase (R := R) (M := M) x φ) hmk

/-- Helper for Lemma 15.128.2: the quotient-valued global fiber form on `M(x)`. -/
private noncomputable def closedPointFiberGlobalLinearFormQuotient
    (x : Ω) (φ : Module.Dual R M) :
    Module.Dual (R ⧸ x.1.asIdeal) (M﹙x﹚) :=
  let f := closedPointFiberGlobalLinearFormQuotientBase (R := R) (M := M) x φ
  { toFun := f
    map_add' := f.map_add
    map_smul' := closedPointFiberGlobalLinearFormQuotient_map_smul
      (R := R) (M := M) x φ }

/-- Helper for Lemma 15.128.2: after identifying `R / x` with `κ(x)`, the descended quotient form
is linear over the residue field. -/
private theorem closedPointFiberGlobalLinearForm_map_smul
    (x : Ω) (φ : Module.Dual R M) :
    ∀ (c : κ(x)) (m : M﹙x﹚),
      let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
      let ψ := closedPointFiberGlobalLinearFormQuotient (R := R) (M := M) x φ
      eκ (ψ ((eκ.symm c) • m)) = c • eκ (ψ m) := by
  intro c m
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  let ψ := closedPointFiberGlobalLinearFormQuotient (R := R) (M := M) x φ
  -- Rewrite `κ(x)`-scalar multiplication through the quotient-ring action and transport via `eκ`.
  change eκ (ψ ((eκ.symm c) • m)) = c • eκ (ψ m)
  rw [ψ.map_smul]
  change eκ (eκ.symm c * ψ m) = c • eκ (ψ m)
  rw [map_mul, eκ.apply_symm_apply]
  simp

/-- Helper for Lemma 15.128.2: the public copy of the global fiber form map
`Hom_R(M, R) → Hom_{κ(x)}(M(x), κ(x))`. -/
private noncomputable def closedPointFiberGlobalLinearForm
    (x : Ω) (φ : Module.Dual R M) :
    Module.Dual (κ(x)) (M﹙x﹚) :=
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  let ψ := closedPointFiberGlobalLinearFormQuotient (R := R) (M := M) x φ
  { toFun := fun m ↦ eκ (ψ m)
    map_add' := by
      intro a b
      simp
    map_smul' := closedPointFiberGlobalLinearForm_map_smul
      (R := R) (M := M) x φ }

/-- Helper for Lemma 15.128.2: evaluating a global fiber form on the class of `m` just reduces to
the residue-field image of `φ m`. -/
private theorem closedPointFiberGlobalLinearForm_apply_mk
    (x : Ω) (φ : Module.Dual R M) (m : M) :
    closedPointFiberGlobalLinearForm (R := R) (M := M) x φ (m⟮x⟯) =
      algebraMap R (κ(x)) (φ m) := by
  -- Unfold the descended quotient form on a numerator representative of the closed fiber.
  rfl

/-- Helper for Lemma 15.128.2: an `R`-linear map `M → κ(x)` kills the submodule `xM`, so it
descends to the closed fiber `M(x)`. -/
private theorem closedPointFiberResidueLinearForm_le_ker
    (x : Ω) (φ : M →ₗ[R] κ(x)) :
    x.1.asIdeal • (⊤ : Submodule R M) ≤ LinearMap.ker φ := by
  -- Expand membership in `xM` and use that every element of `x` maps to zero in `κ(x)`.
  intro m hm
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr n hn
    have hr0 : algebraMap R (κ(x)) r = 0 := by
      let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
      -- Transport the vanishing statement through the quotient-to-residue-field equivalence.
      rw [← eκ.map_zero, ← eκ.commutes r]
      exact congrArg eκ (Ideal.Quotient.eq_zero_iff_mem.2 hr)
    rw [LinearMap.mem_ker, φ.map_smul, Algebra.smul_def, hr0, zero_mul]
  · intro a b ha hb
    rw [LinearMap.mem_ker] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

/-- Helper for Lemma 15.128.2: the quotient descent of an `R`-linear map `M → κ(x)` to the closed
fiber `M(x)`. -/
private noncomputable abbrev closedPointFiberResidueLinearFormBase
    (x : Ω) (φ : M →ₗ[R] κ(x)) :
    M﹙x﹚ →ₗ[R] κ(x) :=
  ((x.1.asIdeal) • (⊤ : Submodule R M)).liftQ φ
    (closedPointFiberResidueLinearForm_le_ker (R := R) (M := M) x φ)

/-- Helper for Lemma 15.128.2: the descended residue-field-valued form is linear over `κ(x)` on
the closed fiber. -/
private theorem closedPointFiberResidueLinearForm_map_smul
    (x : Ω) (φ : M →ₗ[R] κ(x)) :
    ∀ (c : κ(x)) (q : M﹙x﹚),
      closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ (c • q) =
        c • closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ q := by
  intro c q
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  -- Rewrite the `κ(x)`-action on the quotient fiber through the quotient-ring representative.
  change closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ ((eκ.symm c) • q) =
    c • closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (eκ.symm c)
  have hr_left : eκ.symm c = Ideal.Quotient.mk x.1.asIdeal r := by
    symm
    exact hr
  have hr_right : c = eκ (Ideal.Quotient.mk x.1.asIdeal r) := by
    calc
      c = eκ (eκ.symm c) := by rw [eκ.apply_symm_apply]
      _ = eκ (Ideal.Quotient.mk x.1.asIdeal r) := by rw [hr_left]
  rw [hr_left, hr_right]
  refine Quotient.inductionOn' q ?_
  intro m
  have hmk :
      Ideal.Quotient.mk x.1.asIdeal r • (Submodule.Quotient.mk m : M﹙x﹚) =
        (Submodule.Quotient.mk (r • m) : M﹙x﹚) :=
    (Module.Quotient.mk_smul_mk M x.1.asIdeal r m :
      Ideal.Quotient.mk x.1.asIdeal r •
          (Submodule.Quotient.mk m : M ⧸ x.1.asIdeal • (⊤ : Submodule R M)) =
        (Submodule.Quotient.mk (r • m) : M ⧸ x.1.asIdeal • (⊤ : Submodule R M)))
  calc
    closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ
        (Ideal.Quotient.mk x.1.asIdeal r • (Submodule.Quotient.mk m : M﹙x﹚))
        =
      closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ
        (Submodule.Quotient.mk (r • m) : M﹙x﹚) := by
          rw [hmk]
    _ = algebraMap R (κ(x)) r • φ m := by
          calc
            closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ
                (Submodule.Quotient.mk (r • m) : M﹙x﹚) =
              φ (r • m) := by
                rfl
            _ = algebraMap R (κ(x)) r • φ m := by
                  simpa [Algebra.smul_def] using (φ.map_smul r m)
    _ = (closedPointFiberResidueFieldAlgEquiv (R := R) x)
          (Ideal.Quotient.mk x.1.asIdeal r) •
        closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ
          (Submodule.Quotient.mk m : M﹙x﹚) := by
          -- Evaluate both the quotient coefficient and the descended form on the numerator `m`.
          simp [closedPointFiberResidueLinearFormBase]

/-- Helper for Lemma 15.128.2: quotient descent gives a `κ(x)`-linear map from
`Hom_R(M, κ(x))` to the dual of the closed fiber `M(x)`. -/
private noncomputable def fiberLinearFormsToClosedPointFiberDual
    (x : Ω) :
    (M →ₗ[R] κ(x)) →ₗ[κ(x)] Module.Dual (κ(x)) (M﹙x﹚) :=
  { toFun := fun φ ↦
      let f := closedPointFiberResidueLinearFormBase (R := R) (M := M) x φ
      { toFun := f
        map_add' := f.map_add
        map_smul' := closedPointFiberResidueLinearForm_map_smul
          (R := R) (M := M) x φ }
    map_add' := by
      intro φ ψ
      -- Compare the two descended forms on quotient numerators.
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro m
      rfl
    map_smul' := by
      intro c φ
      -- The descent is pointwise linear in the source form.
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro m
      rfl }

/-- Helper for Lemma 15.128.2: residue-field-valued forms on `M` are canonically the same as
dual vectors of the closed fiber `M(x)`. -/
private noncomputable def fiberLinearFormsEquiv_closedPointFiberDual
    (x : Ω) :
    (M →ₗ[R] κ(x)) ≃ₗ[κ(x)] Module.Dual (κ(x)) (M﹙x﹚) :=
  { toLinearMap := fiberLinearFormsToClosedPointFiberDual (R := R) (M := M) x
    invFun := fun ψ ↦
      (ψ.restrictScalars R).comp (Submodule.mkQ (x.1.asIdeal • (⊤ : Submodule R M)))
    left_inv := by
      intro φ
      -- Evaluating the descended form on denominator-`1` classes recovers the original map.
      apply LinearMap.ext
      intro m
      rfl
    right_inv := by
      intro ψ
      -- Every fiber class is represented by a global section, so the inverse is checked on
      -- quotient numerators.
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro m
      rfl }

/-- Helper for Lemma 15.128.2: under the residue/fiber-dual equivalence, evaluating the descended
form on the class of `m` just gives the original value `φ m`. -/
private theorem fiberLinearFormsEquiv_closedPointFiberDual_apply_mk
    (x : Ω) (φ : M →ₗ[R] κ(x)) (m : M) :
    fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x φ (m⟮x⟯) = φ m := by
  -- This is the defining computation rule of the quotient descent.
  rfl

/-- Helper for Lemma 15.128.2: the invisible subspace is still the dual coannihilator of the span
of the locally reconstructed global fiber forms. -/
private theorem closedPointFiberInvisibleSubspace_eq_global_forms_dualCoannihilator
    (x : Ω) :
    closedPointFiberInvisibleSubspace M x =
      (Submodule.span (κ(x))
        (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))).dualCoannihilator := by
  -- The local public copy was chosen to match the owner-private construction definitionally.
  rfl

/-- Helper for Lemma 15.128.2: duals of the visible quotient are exactly the global fiber forms in
the span of the reconstructed image. -/
private theorem visible_quotient_dual_equiv_global_forms_span
    (x : Ω) :
    let W : Subspace (κ(x)) (Module.Dual (κ(x)) (M﹙x﹚)) :=
      Submodule.span (κ(x))
        (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))
    Function.Bijective
      (W.quotDualCoannihilatorToDual.flip :
        W →ₗ[κ(x)] Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x)) := by
  intro W
  letI : FiniteDimensional (κ(x)) (M﹙x﹚) :=
    closedPointFiber_finiteDimensional (R := R) (M := M) x
  have hvisible :
      closedPointFiberVisibleQuotient M x = (M﹙x﹚ ⧸ W.dualCoannihilator) := by
    calc
      closedPointFiberVisibleQuotient M x = (M﹙x﹚ ⧸ closedPointFiberInvisibleSubspace M x) := rfl
      _ = (M﹙x﹚ ⧸ W.dualCoannihilator) := by
            rw [closedPointFiberInvisibleSubspace_eq_global_forms_dualCoannihilator
              (R := R) (M := M) x]
  -- Transport the finite-dimensional quotient-dual pairing along the visible-quotient definition.
  simpa [hvisible] using W.flip_quotDualCoannihilatorToDual_bijective

/-- Helper for Lemma 15.128.2: evaluating a dual vector of the visible quotient on the chosen
classes gives a coordinate vector in `κ(x)^r`. -/
private noncomputable abbrev visibleClassEvalMap (x : Ω) {r : ℕ} (s : Fin r → M) :
    Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x) →ₗ[κ(x)] (Fin r → κ(x)) :=
  LinearMap.pi fun i ↦
    LinearMap.applyₗ' (R := κ(x)) (S := κ(x))
      (M := closedPointFiberVisibleQuotient M x) (M₂ := κ(x))
      (closedPointFiberVisibleClass x (s i))

/-- Helper for Lemma 15.128.2: the evaluation map reads off the value of a dual visible class on
the `i`-th chosen section. -/
private theorem visibleClassEvalMap_apply (x : Ω) {r : ℕ} (s : Fin r → M)
    (τ : Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x)) (i : Fin r) :
    visibleClassEvalMap (M := M) x s τ i = τ (closedPointFiberVisibleClass x (s i)) := by
  -- Unfold the coordinate evaluation map and the `pi`-linear map one coordinate at a time.
  rfl

/-- Helper for Lemma 15.128.2: surjectivity of the visible-class evaluation map is equivalent to
having a family of quotient dual vectors that separates the chosen visible classes by the
Kronecker delta. -/
private theorem visibleClassEvalMap_surjective_iff_exists_separating_visible_forms
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    Function.Surjective (visibleClassEvalMap (M := M) x s) ↔
      ∃ τ : Fin r → Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x),
        ∀ i j, τ i (closedPointFiberVisibleClass x (s j)) = if i = j then 1 else 0 := by
  constructor
  · intro hsurj
    classical
    -- Choose preimages of the standard basis vectors to get the separating family.
    refine ⟨fun i ↦ Classical.choose (hsurj (Pi.basisFun (κ(x)) (Fin r) i)), ?_⟩
    intro i j
    have hi :=
      Classical.choose_spec (hsurj (Pi.basisFun (κ(x)) (Fin r) i))
    simpa [visibleClassEvalMap_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm] using
      congrFun hi j
  · rintro ⟨τ, hτ⟩
    -- A linear combination of the chosen separating forms hits any target coordinate vector.
    intro y
    refine ⟨∑ i, y i • τ i, ?_⟩
    ext j
    have hsum :
        ((∑ i, y i • τ i : Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
          (closedPointFiberVisibleClass x (s j))) =
          ∑ i, y i * (if i = j then 1 else 0) := by
      calc
        ((∑ i, y i • τ i : Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
            (closedPointFiberVisibleClass x (s j)))
            = ∑ i, (y i • τ i) (closedPointFiberVisibleClass x (s j)) := by
                simp
        _ = ∑ i, y i * (if i = j then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [LinearMap.smul_apply, hτ i j, smul_eq_mul]
    calc
      (∑ i, y i • τ i) (closedPointFiberVisibleClass x (s j))
          = ∑ i, y i * (if i = j then 1 else 0) := hsum
      _ = y j := by
            simp

/-- Helper for Lemma 15.128.2: linear independence of the visible classes is equivalent to the
existence of visible fiber forms that separate the chosen sections. -/
private theorem linearIndependent_visibleClasses_iff_exists_separating_visible_forms
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s) ↔
      ∃ τ : Fin r → Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x),
        ∀ i j, τ i (closedPointFiberVisibleClass x (s j)) = if i = j then 1 else 0 := by
  letI :
      Module.Free (κ(x)) (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x)) :=
    Module.Free.of_divisionRing (κ(x))
      (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
  let v : Fin r → closedPointFiberVisibleQuotient M x := closedPointFiberVisibleClass x ∘ s
  let w : Fin r → Module.Dual (κ(x))
      (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x)) :=
    fun i ↦ Module.Dual.eval (κ(x)) (closedPointFiberVisibleQuotient M x) (v i)
  let lfun :
      Module.Dual (κ(x)) (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x)) →ₗ[κ(x)]
        (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x) → κ(x)) :=
    LinearMap.ltoFun (κ(x))
      (Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
      (κ(x)) (κ(x))
  have hdoubleDual :
      LinearIndependent (κ(x)) v ↔
        LinearIndependent (κ(x)) w := by
    constructor
    · intro hv
      -- The canonical map into the double dual is injective, so it preserves linear independence.
      simpa [w] using
        hv.map' (Module.Dual.eval (κ(x)) (closedPointFiberVisibleQuotient M x)) <|
          Module.eval_ker (K := κ(x)) (V := closedPointFiberVisibleQuotient M x)
    · intro hv
      -- Linear independence of the images already forces linear independence upstairs.
      exact LinearIndependent.of_comp
        (Module.Dual.eval (κ(x)) (closedPointFiberVisibleQuotient M x)) <| by
          simpa [w] using hv
  have hlfun :
      LinearMap.ker lfun = ⊥ := by
    -- Forgetting linearity to a bare function is injective by extensionality.
    refine LinearMap.ker_eq_bot.mpr ?_
    intro φ ψ hφψ
    ext τ
    exact congrFun hφψ τ
  have hflip :
      flip (lfun ∘ w) =
        ⇑(visibleClassEvalMap (M := M) x s) := by
    -- The double-dual evaluation sends a visible class to the functional “evaluate at that class”.
    funext τ
    funext i
    rfl
  have hspan :
      LinearIndependent (κ(x))
          (lfun ∘ w) ↔
        Submodule.span (κ(x)) (Set.range (visibleClassEvalMap (M := M) x s)) = ⊤ := by
    -- Over a finite index set, linear independence is equivalent to the transpose spanning all
    -- coordinate functionals.
    simpa [hflip] using
      (span_flip_eq_top_iff_linearIndependent
        (ι := Fin r) (α := Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
        (F := κ(x))
        (f := lfun ∘ w)).symm
  have hsurj :
      Submodule.span (κ(x)) (Set.range (visibleClassEvalMap (M := M) x s)) = ⊤ ↔
        Function.Surjective (visibleClassEvalMap (M := M) x s) := by
    -- The range of a linear map is already a subspace, so spanning its image is the same as
    -- asking for its range to be all of `κ(x)^r`.
    have hrange :
        Submodule.span (κ(x)) (Set.range (visibleClassEvalMap (M := M) x s)) =
          LinearMap.range (visibleClassEvalMap (M := M) x s) := by
      exact
        (Submodule.span_eq (R := κ(x))
          (p := LinearMap.range (visibleClassEvalMap (M := M) x s)))
    rw [hrange, LinearMap.range_eq_top]
  constructor
  · intro hv
    -- Send the visible classes through the quotient pairing and read off separating forms from the
    -- resulting surjective evaluation map.
    exact
      (visibleClassEvalMap_surjective_iff_exists_separating_visible_forms (M := M) x s).1 <|
        hsurj.1 <| hspan.1 <|
          (hdoubleDual.1 <| by simpa [v] using hv).map' lfun hlfun
  · intro hsep
    -- A separating family yields surjectivity of the evaluation map, hence the dual-coordinate
    -- family is linearly independent, and injectivity of the quotient pairing brings that back to
    -- the visible classes.
    exact
      hdoubleDual.2 <| LinearIndependent.of_comp lfun <|
        hspan.2 <| hsurj.2 <|
          (visibleClassEvalMap_surjective_iff_exists_separating_visible_forms (M := M) x s).2 hsep

/-- Helper for Lemma 15.128.2: the tensor-Hom comparison map commutes with precomposition. -/
private theorem rTensorHomToHomRTensor_lcomp
    {P : Type*} [AddCommMonoid P] [Module R P]
    {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
    {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
    (u : P →ₗ[R] M₁) :
    TensorProduct.rTensorHomToHomRTensor (.id R) P R M₂ ∘ₗ
        (LinearMap.lcomp R R u).rTensor M₂ =
      LinearMap.lcomp R (R ⊗[R] M₂) u ∘ₗ
        TensorProduct.rTensorHomToHomRTensor (.id R) M₁ R M₂ := by
  ext f l m
  -- Evaluate both tensor-Hom composites on a simple tensor and then on a source element.
  simp [LinearMap.comp_apply]

/-- Helper for Lemma 15.128.2: the tensor-Hom comparison map commutes with precomposition by the
section map `R^r → M`. -/
private theorem rTensorHomToHomRTensor_lcomp_selectedSectionsMap
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    TensorProduct.rTensorHomToHomRTensor (.id R) (Fin r → R) R (κ(x)) ∘ₗ
        LinearMap.rTensor (κ(x)) ((selectedSectionsMap s).dualMap) =
      LinearMap.lcomp R (R ⊗[R] κ(x)) (selectedSectionsMap s) ∘ₗ
        TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x)) := by
  -- This is the specialized source-free instance of the general precomposition square above.
  simpa using
    (rTensorHomToHomRTensor_lcomp (R := R) (P := Fin r → R) (M₁ := M) (M₂ := κ(x))
      (u := selectedSectionsMap s))

/-- Helper for Lemma 15.128.2: tensoring global linear forms with `κ(x)` and then evaluating on the
closed fiber gives a canonical family of fiberwise linear forms. -/
private noncomputable abbrev tensor_global_forms_to_fiber_dual
    (x : Ω) :
    (Module.Dual R M ⊗[R] κ(x)) →ₗ[R] Module.Dual (κ(x)) (M﹙x﹚) :=
  ((fiberLinearFormsToClosedPointFiberDual (R := R) (M := M) x).restrictScalars R) ∘ₗ
    (LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap) ∘ₗ
      TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x))

/-- Helper for Lemma 15.128.2: a left inverse to a localized map makes precomposition on localized
linear forms surjective. -/
private theorem localized_lcomp_surjective_of_leftInverse
    {N₁ : Type*} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂]
    {f : R}
    (g : LocalizedModule.Away f N₁ →ₗ[Localization.Away f] LocalizedModule.Away f N₂)
    {ρ : LocalizedModule.Away f N₂ →ₗ[Localization.Away f] LocalizedModule.Away f N₁}
    (hρ : Function.LeftInverse ρ g) :
    Function.Surjective
      (LinearMap.lcomp (Localization.Away f) (Localization.Away f) g) := by
  intro ψ
  refine ⟨ψ.comp ρ, ?_⟩
  ext n
  -- Collapse the composite using the given localized retraction.
  change ψ (ρ (g n)) = ψ n
  rw [hρ n]

/-- Helper for Lemma 15.128.2: a localized splitting yields localized linear forms whose values on
the localized chosen sections are the standard coordinate vectors. -/
private theorem exists_localized_separating_forms_of_selectedSectionsSplitAfterInverting
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    selectedSectionsSplitAfterInverting x s →
      ∃ f : R, f ∉ x.1.asIdeal ∧
        ∃ τ : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f,
          ∀ i j,
            τ i
              (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
                ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
                  ((Pi.basisFun R (Fin r)) j))) =
              if i = j then 1 else 0 := by
  rintro ⟨f, hf, ρ, hρ⟩
  let τ : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f :=
    fun i ↦
      ((LinearMap.proj (R := Localization.Away f)
          (φ := fun _ : Fin r ↦ Localization.Away f) i).restrictScalars R).comp
        (((localizedFreeSectionsEquivR (R := R) (r := r) f).toLinearMap).comp
          (ρ.restrictScalars R))
  refine ⟨f, hf, τ, ?_⟩
  intro i j
  have hρj :
      ρ
        ((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j))) =
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
          ((Pi.basisFun R (Fin r)) j) := by
    exact hρ _
  have hρj' :
      ρ (LocalizedModule.mk (s j) 1) =
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
          ((Pi.basisFun R (Fin r)) j) := by
    -- Normalize the localized section map on the `j`-th basis vector before using the retraction.
    simpa [LocalizedModule.map_mk, selectedSectionsMap_basisFun] using hρj
  -- Evaluate the localized retraction on the `j`-th basis vector and then read off the `i`-th
  -- coordinate through the explicit free-module localization equivalence.
  calc
    τ i
        (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j)))
        = localizedFreeSectionsEquivR (R := R) (r := r) f
            (ρ (LocalizedModule.mk (s j) 1)) i := by
            simp [τ, LocalizedModule.map_mk]
    _ = localizedFreeSectionsEquivR (R := R) (r := r) f
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j)) i := by
          rw [hρj']
    _ = algebraMap R (Localization.Away f) (((Pi.basisFun R (Fin r)) j) i) := by
          simpa using
            localizedFreeSectionsEquivR_mk_apply (R := R) (r := r) f
              (Pi.basisFun R (Fin r) j) i
    _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst hij
            simp [Pi.basisFun_apply]
          · simp [Pi.basisFun_apply, hij]

/-- Helper for Lemma 15.128.2: if `f` does not vanish at `x`, then its image in the residue field
`κ(x)` is a unit. -/
private theorem away_to_residueField_isUnit (x : Ω) {f : R} (hf : f ∉ x.1.asIdeal) :
    IsUnit (algebraMap R (κ(x)) f) := by
  refine isUnit_iff_ne_zero.mpr ?_
  intro hfκ
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  have hzero :
      eκ (Ideal.Quotient.mk x.1.asIdeal f) = eκ 0 := by
    change eκ (algebraMap R (R ⧸ x.1.asIdeal) f) = eκ 0
    rw [eκ.commutes f, map_zero]
    exact hfκ
  have hquot :
      Ideal.Quotient.mk x.1.asIdeal f = 0 := by
    simpa using eκ.injective hzero
  exact hf (Ideal.Quotient.eq_zero_iff_mem.mp hquot)

/-- Helper for Lemma 15.128.2: any away localization `R_f` with `f ∉ x` specializes canonically
to the residue field `κ(x)`. -/
private noncomputable def awayToResidueField (x : Ω) {f : R} (hf : f ∉ x.1.asIdeal) :
    Localization.Away f →ₐ[R] κ(x) :=
  { toRingHom := IsLocalization.Away.lift f
      (away_to_residueField_isUnit (R := R) x hf)
    commutes' := by
      intro a
      change IsLocalization.Away.lift f
          (away_to_residueField_isUnit (R := R) x hf)
          (algebraMap R (Localization.Away f) a) =
        algebraMap R (κ(x)) a
      simpa using
        IsLocalization.Away.lift_eq f
          (away_to_residueField_isUnit (R := R) x hf) a }

/-- Helper for Lemma 15.128.2: the specialization `R_f → κ(x)` agrees with the usual residue-field
map on denominator-`1` elements. -/
private theorem awayToResidueField_apply_algebraMap (x : Ω) {f : R} (hf : f ∉ x.1.asIdeal)
    (a : R) :
    awayToResidueField (R := R) x hf (algebraMap R (Localization.Away f) a) =
      algebraMap R (κ(x)) a := by
  -- This is the defining computation rule of the away-localization lift.
  simpa [awayToResidueField] using
    IsLocalization.Away.lift_eq f
      (away_to_residueField_isUnit (R := R) x hf) a

/-- Helper for Lemma 15.128.2: specializing localized separating forms at `x` produces residue
field valued forms on `M` with the same Kronecker-delta values on the chosen sections. -/
private theorem exists_residue_separating_forms_of_exists_localized_separating_forms
    (x : Ω) {r : ℕ} (s : Fin r → M) {f : R} (hf : f ∉ x.1.asIdeal)
    {τ : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f}
    (hτ :
      ∀ i j,
        τ i
          (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j))) =
          if i = j then 1 else 0) :
    let ψ : Fin r → M →ₗ[R] κ(x) :=
      fun i ↦
        ((awayToResidueField (R := R) x hf).toLinearMap.comp (τ i)).comp
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    ∀ i j, ψ i (s j) = if i = j then 1 else 0 := by
  intro i j
  -- First rewrite the localized section value through the selected-basis generator identity.
  have hτ' :
      τ i ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) (s j)) = if i = j then 1 else 0 := by
    simpa [LocalizedModule.map_mk, selectedSectionsMap_basisFun] using hτ i j
  -- Then specialize the resulting scalar from `R_f` to `κ(x)`.
  calc
    ψ i (s j) =
      awayToResidueField (R := R) x hf
        (τ i ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) (s j))) := by
          rfl
    _ = awayToResidueField (R := R) x hf (if i = j then 1 else 0) := by rw [hτ']
    _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst hij
            simp [awayToResidueField_apply_algebraMap]
          · simp [hij, awayToResidueField_apply_algebraMap]

/-- Helper for Lemma 15.128.2: separating residue-field-valued forms on `M` descend to separating
forms on the closed fiber `M(x)`. -/
private theorem exists_closedPointFiber_separating_forms_of_exists_residue_separating_forms
    (x : Ω) {r : ℕ} (s : Fin r → M)
    (hψ :
      ∃ ψ : Fin r → M →ₗ[R] κ(x),
        ∀ i j, ψ i (s j) = if i = j then 1 else 0) :
    ∃ ω : Fin r → Module.Dual (κ(x)) (M﹙x﹚),
      ∀ i j, ω i ((s j)⟮x⟯) = if i = j then 1 else 0 := by
  rcases hψ with ⟨ψ, hψ⟩
  refine ⟨fun i ↦ fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x (ψ i), ?_⟩
  intro i j
  -- Evaluate the descended fiber form on the class of `s j`.
  simpa using
    (fiberLinearFormsEquiv_closedPointFiberDual_apply_mk
      (R := R) (M := M) x (ψ i) (s j)).trans (hψ i j)

/-- Helper for Lemma 15.128.2: specializing a localized linear form at `x` agrees with descending
the induced residue-field-valued form to the closed fiber. -/
private theorem specialized_localized_form_descends_to_fiber_dual
    (x : Ω) {f : R} (hf : f ∉ x.1.asIdeal)
    (τ : LocalizedModule.Away f M →ₗ[R] Localization.Away f) :
    let ζ : LocalizedModule.Away f (Module.Dual R M) :=
      (localizedLinearFormsEquivAway (R := R) (N := M) f).symm τ
    let F :
        LocalizedModule.Away f (Module.Dual R M) →ₗ[R] Module.Dual (κ(x)) (M﹙x﹚) :=
      ((fiberLinearFormsToClosedPointFiberDual (R := R) (M := M) x).restrictScalars R) ∘ₗ
        (LinearMap.lcomp R (κ(x)) (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) ∘ₗ
          (LinearMap.compRight R (awayToResidueField (R := R) x hf).toLinearMap) ∘ₗ
            (localizedLinearFormsEquivAway (R := R) (N := M) f).toLinearMap
    F ζ =
      fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x
        ((((awayToResidueField (R := R) x hf).toLinearMap.comp τ).comp
            (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := by
  dsimp
  -- Compare both descended forms on quotient numerators of the closed fiber.
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro m
  -- On a numerator representative, both sides are the same specialized scalar.
  change
    ((awayToResidueField (R := R) x hf).toLinearMap
      (((localizedLinearFormsEquivAway (R := R) (N := M) f)
          ((localizedLinearFormsEquivAway (R := R) (N := M) f).symm τ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m))) =
      ((awayToResidueField (R := R) x hf).toLinearMap
        (τ ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m)))
  simpa using
    congrArg
      (fun σ : LocalizedModule.Away f M →ₗ[R] Localization.Away f ↦
        (awayToResidueField (R := R) x hf).toLinearMap
          (σ ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m)))
      (LinearEquiv.apply_symm_apply
        (localizedLinearFormsEquivAway (R := R) (N := M) f) τ)

/-- Helper for Lemma 15.128.2: on a pure tensor `φ ⊗ c`, the tensorized global-form map gives the
scalar multiple `c • closedPointFiberGlobalLinearForm x φ`. -/
private theorem tensor_global_forms_to_fiber_dual_tmul
    (x : Ω) (φ : Module.Dual R M) (c : κ(x)) :
    tensor_global_forms_to_fiber_dual (R := R) (M := M) x (φ ⊗ₜ[R] c) =
      c • closedPointFiberGlobalLinearForm (R := R) (M := M) x φ := by
  -- Evaluate both sides on quotient numerators of `M(x)` and compare the resulting scalars.
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro m
  let χ : M →ₗ[R] κ(x) :=
    (LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap)
      (TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x)) (φ ⊗ₜ[R] c))
  calc
    tensor_global_forms_to_fiber_dual (R := R) (M := M) x
        (φ ⊗ₜ[R] c) (m⟮x⟯) = χ m := by
          simpa [tensor_global_forms_to_fiber_dual, χ, LinearMap.comp_apply] using
            fiberLinearFormsEquiv_closedPointFiberDual_apply_mk
              (R := R) (M := M) x χ m
    _ = algebraMap R (κ(x)) (φ m) * c := by
          simp [χ, LinearMap.comp_apply, TensorProduct.lid_tmul, Algebra.smul_def]
    _ = c * algebraMap R (κ(x)) (φ m) := by
          rw [mul_comm]
    _ = (c • closedPointFiberGlobalLinearForm (R := R) (M := M) x φ) (m⟮x⟯) := by
          simp [closedPointFiberGlobalLinearForm_apply_mk, Algebra.smul_def]

/-- Helper for Lemma 15.128.2: multiplying an image of `tensor_global_forms_to_fiber_dual` by a
residue-field scalar still comes from an explicit tensor preimage. -/
private theorem exists_preimage_smul_tensor_global_forms_to_fiber_dual
    (x : Ω) (a : κ(x)) :
    ∀ z : Module.Dual R M ⊗[R] κ(x),
      ∃ z' : Module.Dual R M ⊗[R] κ(x),
        tensor_global_forms_to_fiber_dual (R := R) (M := M) x z' =
          a • tensor_global_forms_to_fiber_dual (R := R) (M := M) x z := by
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    rw [LinearMap.map_zero, LinearMap.map_zero, smul_zero]
  · intro φ c
    refine ⟨φ ⊗ₜ[R] (a * c), ?_⟩
    rw [tensor_global_forms_to_fiber_dual_tmul (R := R) (M := M) x φ (a * c)]
    rw [tensor_global_forms_to_fiber_dual_tmul (R := R) (M := M) x φ c]
    simp [smul_smul, mul_assoc]
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, hw₁⟩
    rcases hz₂ with ⟨w₂, hw₂⟩
    refine ⟨w₁ + w₂, ?_⟩
    simp [LinearMap.map_add, hw₁, hw₂, smul_add]

/-- Helper for Lemma 15.128.2: the span of global fiber forms lies in the range of the tensorized
global-form map after restricting scalars from `κ(x)` to `R`. -/
private theorem global_forms_span_le_tensor_global_forms_range
    (x : Ω) :
    (Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))).restrictScalars R ≤
      LinearMap.range (tensor_global_forms_to_fiber_dual (R := R) (M := M) x) := by
  -- Build preimages by induction on the `κ(x)`-span of the global fiber forms.
  intro ω hω
  change ω ∈
    Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x)) at hω
  change ∃ z : Module.Dual R M ⊗[R] κ(x),
    tensor_global_forms_to_fiber_dual (R := R) (M := M) x z = ω
  refine Submodule.span_induction
      (s := Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))
      (p := fun y _ ↦
        ∃ z : Module.Dual R M ⊗[R] κ(x),
          tensor_global_forms_to_fiber_dual (R := R) (M := M) x z = y)
      ?_ ?_ ?_ ?_ hω
  · intro y hy
    rcases hy with ⟨φ, rfl⟩
    refine ⟨φ ⊗ₜ[R] (1 : κ(x)), ?_⟩
    rw [tensor_global_forms_to_fiber_dual_tmul (R := R) (M := M) x φ (1 : κ(x))]
    simp
  · exact ⟨0, by simp⟩
  · intro y z hy hz hyP hzP
    rcases hyP with ⟨y', hy'⟩
    rcases hzP with ⟨z', hz'⟩
    refine ⟨y' + z', ?_⟩
    simp [LinearMap.map_add, hy', hz']
  · intro a y hy hyP
    rcases hyP with ⟨z, hz⟩
    rcases exists_preimage_smul_tensor_global_forms_to_fiber_dual
        (R := R) (M := M) x a z with ⟨z', hz'⟩
    exact ⟨z', by simpa [hz] using hz'⟩

/-- Helper for Lemma 15.128.2: the range of the tensorized global-form map is exactly the span of
global fiber forms, viewed as an `R`-submodule by restriction of scalars. -/
private theorem tensor_global_forms_range_eq_global_forms_span
    (x : Ω) :
    LinearMap.range (tensor_global_forms_to_fiber_dual (R := R) (M := M) x) =
      (Submodule.span (κ(x))
        (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))).restrictScalars R := by
  apply le_antisymm
  · intro ω hω
    rcases hω with ⟨z, rfl⟩
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · -- The zero tensor maps to the zero fiber form, which is already in the restricted span.
      simp
    · intro φ c
      -- A pure tensor maps to a scalar multiple of a span generator.
      rw [tensor_global_forms_to_fiber_dual_tmul (R := R) (M := M) x φ c]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨φ, rfl⟩)
    · intro z₁ z₂ hz₁ hz₂
      -- The restricted span is closed under addition.
      simpa [LinearMap.map_add] using Submodule.add_mem _ hz₁ hz₂
  · exact global_forms_span_le_tensor_global_forms_range (R := R) (M := M) x

/-- Helper for Lemma 15.128.2: specializing a localized linear form at `x` produces a fiber form
lying in the span of the global fiber forms. -/
private theorem fiber_form_specialized_from_localized_form_mem_global_forms_span
    (x : Ω) {f : R} (hf : f ∉ x.1.asIdeal)
    (τ : LocalizedModule.Away f M →ₗ[R] Localization.Away f) :
    let ψ : M →ₗ[R] κ(x) :=
      ((awayToResidueField (R := R) x hf).toLinearMap.comp τ).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    let ω := fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x ψ
    ω ∈ Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x)) := by
  dsimp
  let ζ : LocalizedModule.Away f (Module.Dual R M) :=
    (localizedLinearFormsEquivAway (R := R) (N := M) f).symm τ
  let F :
      LocalizedModule.Away f (Module.Dual R M) →ₗ[R] Module.Dual (κ(x)) (M﹙x﹚) :=
    ((fiberLinearFormsToClosedPointFiberDual (R := R) (M := M) x).restrictScalars R) ∘ₗ
      (LinearMap.lcomp R (κ(x)) (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) ∘ₗ
        (LinearMap.compRight R (awayToResidueField (R := R) x hf).toLinearMap) ∘ₗ
          (localizedLinearFormsEquivAway (R := R) (N := M) f).toLinearMap
  have htarget :
      F ζ =
        fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x
          ((((awayToResidueField (R := R) x hf).toLinearMap.comp τ).comp
              (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := by
    -- The abstract specialization map is exactly the named comparison proved just above.
    simpa [ζ, F] using
      specialized_localized_form_descends_to_fiber_dual
        (R := R) (M := M) x hf τ
  have hFmk :
      ∀ φ : Module.Dual R M,
        F (LocalizedModule.mk φ 1) =
          closedPointFiberGlobalLinearForm (R := R) (M := M) x φ := by
    intro φ
    apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro m
    -- Evaluate on quotient numerators to reduce the specialized localized form to the scalar
    -- `algebraMap R (κ(x)) (φ m)`.
    change awayToResidueField (R := R) x hf
        (((localizedLinearFormsEquivAway (R := R) (N := M) f)
          (LocalizedModule.mk φ 1))
          (LocalizedModule.mk m 1)) =
      closedPointFiberGlobalLinearForm (R := R) (M := M) x φ (m⟮x⟯)
    have hmk :
        ((localizedLinearFormsEquivAway (R := R) (N := M) f)
          (LocalizedModule.mk φ 1))
          (LocalizedModule.mk m 1) =
        algebraMap R (Localization.Away f) (φ m) := by
      simpa using localizedLinearFormsEquivAway_mk_apply
        (R := R) (N := M) f φ m
    calc
      awayToResidueField (R := R) x hf
          (((localizedLinearFormsEquivAway (R := R) (N := M) f)
            (LocalizedModule.mk φ 1))
            (LocalizedModule.mk m 1)) =
          awayToResidueField (R := R) x hf
            (algebraMap R (Localization.Away f) (φ m)) := by
              rw [hmk]
      _ = algebraMap R (κ(x)) (φ m) := by
            simpa using awayToResidueField_apply_algebraMap (R := R) x hf (φ m)
      _ = closedPointFiberGlobalLinearForm (R := R) (M := M) x φ (m⟮x⟯) := by
            symm
            simpa using closedPointFiberGlobalLinearForm_apply_mk
              (R := R) (M := M) x φ m
  obtain ⟨⟨φ, t⟩, ht⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R M)) ζ
  have ht' :
      LocalizedModule.mk φ 1 = t • ζ := by
    -- Clear one denominator in the localized dual and rewrite it as a scalar multiple of `ζ`.
    simpa [LocalizedModule.mk] using ht.symm
  have hscaled :
      algebraMap R (κ(x)) (t : R) • F ζ =
        closedPointFiberGlobalLinearForm (R := R) (M := M) x φ := by
    -- Apply the specialization map `F` to the cleared-denominator identity.
    calc
      algebraMap R (κ(x)) (t : R) • F ζ = F (t • ζ) := by
        simp [F, Submonoid.smul_def]
      _ = F (LocalizedModule.mk φ 1) := by rw [← ht']
      _ = closedPointFiberGlobalLinearForm (R := R) (M := M) x φ := hFmk φ
  have htunit : IsUnit (algebraMap R (κ(x)) (t : R)) := by
    rcases t with ⟨t, ⟨n, rfl⟩⟩
    simpa [map_pow] using (away_to_residueField_isUnit (R := R) x hf).pow n
  rcases htunit with ⟨u, hu⟩
  have hgen :
      closedPointFiberGlobalLinearForm (R := R) (M := M) x φ ∈
        Submodule.span (κ(x))
          (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x)) :=
    Submodule.subset_span ⟨φ, rfl⟩
  have hscaled_mem :
      algebraMap R (κ(x)) (t : R) • F ζ ∈
        Submodule.span (κ(x))
          (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x)) := by
    rw [hscaled]
    exact hgen
  -- The specialized denominator becomes a unit in `κ(x)`, so the original fiber form lies in the
  -- same span.
  rw [← htarget]
  rw [← hu] at hscaled_mem
  simpa [smul_smul] using Submodule.smul_mem
    (Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x)))
    (↑u⁻¹ : κ(x))
    hscaled_mem

/-- Helper for Lemma 15.128.2: a localized splitting yields visible quotient dual vectors that
separate the chosen visible classes. -/
private theorem exists_visible_separating_forms_of_selectedSectionsSplitAfterInverting
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    selectedSectionsSplitAfterInverting x s →
      ∃ τv : Fin r → Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x),
        ∀ i j, τv i (closedPointFiberVisibleClass x (s j)) = if i = j then 1 else 0 := by
  intro hsplit
  rcases exists_localized_separating_forms_of_selectedSectionsSplitAfterInverting
      (R := R) (M := M) x s hsplit with ⟨f, hf, τ, hτ⟩
  let ψ : Fin r → M →ₗ[R] κ(x) :=
    fun i ↦
      ((awayToResidueField (R := R) x hf).toLinearMap.comp (τ i)).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  have hψ : ∀ i j, ψ i (s j) = if i = j then 1 else 0 := by
    -- Reuse the explicit specialization lemma so the same family `ψ` can also be fed into the
    -- global-form-span comparison below.
    simpa [ψ] using
      exists_residue_separating_forms_of_exists_localized_separating_forms
        (R := R) (M := M) x s hf hτ
  let W : Subspace (κ(x)) (Module.Dual (κ(x)) (M﹙x﹚)) :=
    Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))
  let eW :
      W ≃ₗ[κ(x)] Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x) :=
    LinearEquiv.ofBijective
      (W.quotDualCoannihilatorToDual.flip :
        W →ₗ[κ(x)] Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
      (visible_quotient_dual_equiv_global_forms_span (R := R) (M := M) x)
  let ω : Fin r → Module.Dual (κ(x)) (M﹙x﹚) :=
    fun i ↦ fiberLinearFormsEquiv_closedPointFiberDual (R := R) (M := M) x (ψ i)
  have hωsep :
      ∀ i j, ω i ((s j)⟮x⟯) = if i = j then 1 else 0 := by
    intro i j
    -- Evaluate the descended fiber form on the chosen section and read back the previously
    -- specialized Kronecker-delta values on `M`.
    simpa [ω] using
      (fiberLinearFormsEquiv_closedPointFiberDual_apply_mk
        (R := R) (M := M) x (ψ i) (s j)).trans (hψ i j)
  have hωW : ∀ i, ω i ∈ W := by
    intro i
    -- Each specialized localized separator comes from the span of global fiber forms.
    simpa [W, ω, ψ] using
      fiber_form_specialized_from_localized_form_mem_global_forms_span
        (R := R) (M := M) x hf (τ i)
  refine ⟨fun i ↦ eW ⟨ω i, hωW i⟩, ?_⟩
  intro i j
  -- Descending through the visible quotient does not change the separating values on the chosen
  -- classes.
  calc
    eW ⟨ω i, hωW i⟩ (closedPointFiberVisibleClass x (s j))
        = ω i ((s j)⟮x⟯) := by
            rfl
    _ = if i = j then 1 else 0 := hωsep i j

/-- Helper for Lemma 15.128.2: linear independence of the visible classes already makes the
visible-class evaluation map surjective. -/
private theorem surjective_visibleClassEvalMap_of_linearIndependent_visibleClasses
    (x : Ω) {r : ℕ} (s : Fin r → M)
    (hlin : LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s)) :
    Function.Surjective (visibleClassEvalMap (M := M) x s) := by
  -- Convert linear independence into separating visible forms and then package them as a
  -- surjective evaluation map.
  exact
    (visibleClassEvalMap_surjective_iff_exists_separating_visible_forms (M := M) x s).2 <|
      (linearIndependent_visibleClasses_iff_exists_separating_visible_forms
        (M := M) x s).1 hlin

/-- Helper for Lemma 15.128.2: the coordinate map sends a linear form on `R^r` to its values on
the standard basis vectors. -/
private noncomputable def free_residue_forms_coordinateMap
    (x : Ω) {r : ℕ} :
    ((Fin r → R) →ₗ[R] κ(x)) →ₗ[κ(x)] (Fin r → κ(x)) where
  toFun := fun τ i ↦ τ ((Pi.basisFun R (Fin r)) i)
  map_add' τ₁ τ₂ := by
    -- Read coordinates pointwise; addition is computed coordinatewise.
    ext i
    simp
  map_smul' a τ := by
    -- The `κ(x)`-scalar action on linear forms is also pointwise on the codomain.
    ext i
    simp

/-- Helper for Lemma 15.128.2: an `R`-linear form on the free module `R^r` is determined by its
values on the standard basis. -/
private noncomputable def free_residue_forms_equiv_coordinates
    (x : Ω) {r : ℕ} :
    ((Fin r → R) →ₗ[R] κ(x)) ≃ₗ[κ(x)] (Fin r → κ(x)) where
  toLinearMap := free_residue_forms_coordinateMap (R := R) x
  invFun := fun v ↦ (Pi.basisFun R (Fin r)).constr R v
  left_inv τ := by
    -- Expand an arbitrary vector in the standard basis and compare the two linear forms there.
    apply LinearMap.ext
    intro w
    have hw :
        w = ∑ i : Fin r, w i • (Pi.basisFun R (Fin r)) i := by
      simpa [Pi.basisFun_repr] using ((Pi.basisFun R (Fin r)).sum_repr w).symm
    -- Apply `τ` to the standard-basis expansion and read the coefficients back as coordinates.
    simpa [free_residue_forms_coordinateMap, map_sum] using (congrArg τ hw).symm
  right_inv v := by
    -- On each basis vector, the reconstructed form returns the prescribed coordinate.
    ext i
    simp [free_residue_forms_coordinateMap]

/-- Helper for Lemma 15.128.2: the coordinate equivalence reads off the values on the standard
basis vectors of `R^r`. -/
private theorem free_residue_forms_equiv_coordinates_apply
    (x : Ω) {r : ℕ} (τ : (Fin r → R) →ₗ[R] κ(x)) (i : Fin r) :
    free_residue_forms_equiv_coordinates (R := R) x τ i =
      τ ((Pi.basisFun R (Fin r)) i) := by
  -- This is exactly how the coordinate equivalence was defined.
  rfl

/-- Helper for Lemma 15.128.2: after tensoring the dual section map and passing to coordinates, one
obtains evaluation of the induced fiber form on the chosen sections. -/
private theorem tensor_dual_selectedSectionsMap_coordinates
    (x : Ω) {r : ℕ} (s : Fin r → M)
    (z : Module.Dual R M ⊗[R] κ(x)) :
    (((free_residue_forms_equiv_coordinates (R := R) x).toLinearMap.restrictScalars R) ∘ₗ
        (LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap) ∘ₗ
          TensorProduct.rTensorHomToHomRTensor (.id R) (Fin r → R) R (κ(x)) ∘ₗ
            LinearMap.rTensor (κ(x)) ((selectedSectionsMap s).dualMap)) z =
      fun i ↦
        tensor_global_forms_to_fiber_dual (R := R) (M := M) x z ((s i)⟮x⟯) := by
  -- First rewrite the tensor-Hom comparison through precomposition by the section map.
  rw [rTensorHomToHomRTensor_lcomp_selectedSectionsMap (R := R) (M := M) x s]
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · -- The zero tensor gives the zero coordinate vector on both sides.
    ext i
    simp [tensor_global_forms_to_fiber_dual]
  · intro φ c
    ext i
    let χ : M →ₗ[R] κ(x) :=
      (LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap)
        (TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x)) (φ ⊗ₜ[R] c))
    -- Both sides evaluate the same descended residue-field-valued form on the chosen section `s i`.
    calc
      ((((free_residue_forms_equiv_coordinates (R := R) x).toLinearMap.restrictScalars R) ∘ₗ
            (LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap) ∘ₗ
              LinearMap.lcomp R (R ⊗[R] κ(x)) (selectedSectionsMap s) ∘ₗ
                TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x)))
          (φ ⊗ₜ[R] c)) i
          = χ (selectedSectionsMap s ((Pi.basisFun R (Fin r)) i)) := by
              change
                free_residue_forms_equiv_coordinates (R := R) x
                    (((LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap) ∘ₗ
                        LinearMap.lcomp R (R ⊗[R] κ(x)) (selectedSectionsMap s) ∘ₗ
                          TensorProduct.rTensorHomToHomRTensor (.id R) M R (κ(x)))
                      (φ ⊗ₜ[R] c)) i =
                  χ (selectedSectionsMap s ((Pi.basisFun R (Fin r)) i))
              rw [free_residue_forms_equiv_coordinates_apply]
              rfl
      _ = χ (s i) := by
            rw [selectedSectionsMap_basisFun]
      _ = tensor_global_forms_to_fiber_dual (R := R) (M := M) x
            (φ ⊗ₜ[R] c) ((s i)⟮x⟯) := by
            symm
            simpa [tensor_global_forms_to_fiber_dual, χ, LinearMap.comp_apply] using
              fiberLinearFormsEquiv_closedPointFiberDual_apply_mk
                (R := R) (M := M) x χ (s i)
  · intro z₁ z₂ hz₁ hz₂
    -- Both sides are linear in the tensor argument, so the additive case follows by simplification.
    ext i
    simp [LinearMap.map_add, hz₁, hz₂]

/-- Helper for Lemma 15.128.2: linear independence of the visible classes forces surjectivity of
the tensorized dual section map on the residue field fiber. -/
private theorem tensor_dual_selectedSectionsMap_surjective_of_linearIndependent_visibleClasses
    (x : Ω) {r : ℕ} (s : Fin r → M)
    (hlin : LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s)) :
    Function.Surjective
      ((((selectedSectionsMap s).dualMap).rTensor (κ(x))) :
        (Module.Dual R M ⊗[R] κ(x)) →ₗ[R]
          (Module.Dual R (Fin r → R) ⊗[R] κ(x))) := by
  let W : Subspace (κ(x)) (Module.Dual (κ(x)) (M﹙x﹚)) :=
    Submodule.span (κ(x))
      (Set.range (closedPointFiberGlobalLinearForm (R := R) (M := M) x))
  let eW :
      W ≃ₗ[κ(x)] Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x) :=
    LinearEquiv.ofBijective
      (W.quotDualCoannihilatorToDual.flip :
        W →ₗ[κ(x)] Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x))
      (visible_quotient_dual_equiv_global_forms_span (R := R) (M := M) x)
  let A :
      (Module.Dual R M ⊗[R] κ(x)) →ₗ[R]
        (Module.Dual R (Fin r → R) ⊗[R] κ(x)) :=
    (((selectedSectionsMap s).dualMap).rTensor (κ(x)))
  let B :
      (Module.Dual R (Fin r → R) ⊗[R] κ(x)) →ₗ[R]
        ((Fin r → R) →ₗ[R] (R ⊗[R] κ(x))) :=
    TensorProduct.rTensorHomToHomRTensor (.id R) (Fin r → R) R (κ(x))
  let C :
      ((Fin r → R) →ₗ[R] (R ⊗[R] κ(x))) →ₗ[R] ((Fin r → R) →ₗ[R] κ(x)) :=
    LinearMap.compRight R (TensorProduct.lid R (κ(x))).toLinearMap
  let D :
      ((Fin r → R) →ₗ[R] κ(x)) →ₗ[R] (Fin r → κ(x)) :=
    (free_residue_forms_equiv_coordinates (R := R) x).toLinearMap.restrictScalars R
  let coordMap : (Module.Dual R M ⊗[R] κ(x)) →ₗ[R] (Fin r → κ(x)) :=
    D ∘ₗ C ∘ₗ B ∘ₗ A
  have hvisibleSurj :
      Function.Surjective (visibleClassEvalMap (M := M) x s) := by
    exact
      surjective_visibleClassEvalMap_of_linearIndependent_visibleClasses
        (M := M) x s hlin
  have hcoordSurj : Function.Surjective coordMap := by
    intro y
    rcases hvisibleSurj y with ⟨τv, hτv⟩
    let w : W := eW.symm τv
    have hw_range :
        w.1 ∈ LinearMap.range (tensor_global_forms_to_fiber_dual (R := R) (M := M) x) := by
      rw [tensor_global_forms_range_eq_global_forms_span (x := x)]
      exact w.2
    rcases hw_range with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    ext i
    have hw_eval :
        eW w (closedPointFiberVisibleClass x (s i)) =
          w.1 ((s i)⟮x⟯) := by
      rfl
    calc
      coordMap z i =
        tensor_global_forms_to_fiber_dual (R := R) (M := M) x z ((s i)⟮x⟯) := by
          simpa [coordMap, A, B, C, D] using
            congrArg (fun v : Fin r → κ(x) ↦ v i)
              (tensor_dual_selectedSectionsMap_coordinates
                (R := R) (M := M) x s z)
      _ = w.1 ((s i)⟮x⟯) := by
            rw [hz]
      _ = eW w (closedPointFiberVisibleClass x (s i)) := by
            rw [hw_eval]
      _ = τv (closedPointFiberVisibleClass x (s i)) := by
            simpa [w] using congrArg
              (fun τ : Module.Dual (κ(x)) (closedPointFiberVisibleQuotient M x) ↦
                τ (closedPointFiberVisibleClass x (s i)))
              (LinearEquiv.apply_symm_apply eW τv)
      _ = y i := by
            simpa [visibleClassEvalMap_apply] using congrFun hτv i
  have hBinj : Function.Injective B := by
    exact
      (rTensorHomToHomRTensor_bijective_of_finite_projective
        (R := R) (L := κ(x)) (M := Fin r → R) (N := R)).1
  have hCinj : Function.Injective C := by
    intro τ₁ τ₂ hτ
    have hτ' := congrArg
      (LinearMap.compRight R (TensorProduct.lid R (κ(x))).symm.toLinearMap) hτ
    simpa [C, LinearMap.comp_apply] using hτ'
  have hDinj : Function.Injective D := by
    exact (free_residue_forms_equiv_coordinates (R := R) x).injective
  intro u
  rcases hcoordSurj (D (C (B u))) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply hBinj
  apply hCinj
  apply hDinj
  simpa [coordMap, A, B, C, D] using hz

/-- Helper for Lemma 15.128.2: surjectivity of the localized dual section map produces localized
linear forms whose values on the chosen localized basis vectors are the Kronecker symbols. -/
private theorem exists_localized_separating_forms_of_localized_dual_surjective
    {r : ℕ} (f : R) (s : Fin r → M)
    (hsurj :
      Function.Surjective
        (LocalizedModule.map (Submonoid.powers f) ((selectedSectionsMap s).dualMap))) :
    ∃ τ : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f,
      ∀ i j,
        τ i
          (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j))) =
          if i = j then 1 else 0 := by
  classical
  let ψ : Fin r → LocalizedModule.Away f (Module.Dual R M) :=
    fun i ↦ Classical.choose
      (hsurj ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R (Fin r → R)))
        (LinearMap.proj i)))
  let τ : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f :=
    fun i ↦ localizedLinearFormsEquivAway (R := R) (N := M) f (ψ i)
  refine ⟨τ, ?_⟩
  intro i j
  have hψ :
      (LocalizedModule.map (Submonoid.powers f) ((selectedSectionsMap s).dualMap)) (ψ i) =
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R (Fin r → R)))
          (LinearMap.proj i) := by
    exact Classical.choose_spec
      (hsurj ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R (Fin r → R)))
        (LinearMap.proj i)))
  have hnat :=
    LinearMap.congr_fun
      (congrArg
        (fun T ↦ T (ψ i))
        (localizedLinearFormsEquivAway_map_dualMap
          (R := R) (N₁ := Fin r → R) (N₂ := M) f (selectedSectionsMap s))
        )
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
        ((Pi.basisFun R (Fin r)) j))
  -- Rewrite the transported localized dual preimage through the naturality square, then evaluate
  -- the localized coordinate projection on the `j`-th basis vector.
  calc
    τ i
        (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j)))
        =
          localizedLinearFormsEquivAway (R := R) (N := Fin r → R) f
            ((LocalizedModule.map (Submonoid.powers f) ((selectedSectionsMap s).dualMap))
              (ψ i))
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j)) := by
            simpa [τ] using hnat.symm
    _ =
        localizedLinearFormsEquivAway (R := R) (N := Fin r → R) f
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R (Fin r → R)))
            (LinearMap.proj i))
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j)) := by
          simpa using congrArg
            (fun z ↦
              localizedLinearFormsEquivAway (R := R) (N := Fin r → R) f z
                ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
                  ((Pi.basisFun R (Fin r)) j)))
            hψ
    _ = algebraMap R (Localization.Away f) ((Pi.basisFun R (Fin r) j) i) := by
          simpa using
            localizedLinearFormsEquivAway_mk_apply
              (R := R) (N := Fin r → R) f (LinearMap.proj i) (Pi.basisFun R (Fin r) j)
    _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst hij
            simp [Pi.basisFun_apply]
          · simp [Pi.basisFun_apply, hij]

/-- Helper for Lemma 15.128.2: once localized separating forms are known as `R`-linear maps, the
canonical away-localization equivalence upgrades them to `R_f`-linear forms without changing their
values on the chosen localized sections. -/
private theorem away_linear_separating_forms_of_restrictScalars_separating_forms
    {r : ℕ} (f : R) (s : Fin r → M)
    (τR : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f)
    (hτR :
      ∀ i j,
        τR i
          (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j))) =
          if i = j then 1 else 0) :
    ∃ τ : Fin r → LocalizedModule.Away f M →ₗ[Localization.Away f] Localization.Away f,
      ∀ i j,
        τ i
          ((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j))) =
          if i = j then 1 else 0 := by
  let τ : Fin r → LocalizedModule.Away f M →ₗ[Localization.Away f] Localization.Away f :=
    fun i ↦
      LinearMap.extendScalarsOfIsLocalizationEquiv
        (Submonoid.powers f) (Localization.Away f) (τR i)
  refine ⟨τ, ?_⟩
  intro i j
  -- The upgrade only changes the linearity structure; the underlying function on localized
  -- sections is unchanged.
  simpa [τ] using hτR i j

/-- Helper for Lemma 15.128.2: localized separating forms on the chosen sections package into a
localized left inverse to the section map. -/
private theorem selectedSectionsSplitAfterInverting_of_exists_localized_separating_forms
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    (∃ f : R, f ∉ x.1.asIdeal ∧
      ∃ τ : Fin r → LocalizedModule.Away f M →ₗ[Localization.Away f] Localization.Away f,
        ∀ i j,
          τ i
            ((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))
              ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
                ((Pi.basisFun R (Fin r)) j))) =
            if i = j then 1 else 0) →
      selectedSectionsSplitAfterInverting x s := by
  rintro ⟨f, hf, τ, hτ⟩
  let ρcoords : LocalizedModule.Away f M →ₗ[Localization.Away f] (Fin r → Localization.Away f) :=
    LinearMap.pi τ
  let ρ :
      LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f (Fin r → R) :=
    ((localizedFreeSectionsEquiv (R := R) (r := r) f).symm.toLinearMap).comp ρcoords
  refine ⟨f, hf, ρ, ?_⟩
  have hcoord (i : Fin r) :
      ((τ i).restrictScalars R).comp
          ((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R) =
        ((LinearMap.proj (R := Localization.Away f)
            (φ := fun _ : Fin r ↦ Localization.Away f) i).restrictScalars R).comp
          (localizedFreeSectionsEquivR (R := R) (r := r) f).toLinearMap := by
    -- Compare the `i`-th coordinate maps on numerator generators of the localized free module.
    apply IsLocalizedModule.linearMap_ext (S := Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
      (Algebra.linearMap R (Localization.Away f))
    apply LinearMap.ext
    intro v
    have hv :
        v = ∑ j : Fin r, v j • (Pi.basisFun R (Fin r)) j := by
      simpa [Pi.basisFun_repr] using ((Pi.basisFun R (Fin r)).sum_repr v).symm
    rw [hv, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    calc
      τ i
          ((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))
            ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
              ((Pi.basisFun R (Fin r)) j))) =
        if i = j then 1 else 0 := hτ i j
      _ = algebraMap R (Localization.Away f) (((Pi.basisFun R (Fin r)) j) i) := by
            by_cases hij : i = j
            · subst hij
              simp [Pi.basisFun_apply]
            · simp [Pi.basisFun_apply, hij]
      _ = (((LinearMap.proj (R := Localization.Away f)
              (φ := fun _ : Fin r ↦ Localization.Away f) i).restrictScalars R).comp
            (localizedFreeSectionsEquivR (R := R) (r := r) f).toLinearMap)
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
            ((Pi.basisFun R (Fin r)) j)) := by
            simpa [LinearMap.comp_apply] using
              (localizedFreeSectionsEquivR_mk_apply (R := R) (r := r) f
                (Pi.basisFun R (Fin r) j) i).symm
  intro n
  apply (localizedFreeSectionsEquiv (R := R) (r := r) f).injective
  -- Apply the localization/free-module comparison so the left inverse reduces to the coordinate
  -- identities already proved on each basis direction.
  ext i
  have hi := congrArg
    (fun T : LocalizedModule.Away f (Fin r → R) →ₗ[R] Localization.Away f ↦ T n)
    (hcoord i)
  simpa [ρ, ρcoords, localizedFreeSectionsEquiv, LinearMap.comp_apply,
    LinearEquiv.extendScalarsOfIsLocalization_apply] using hi

/-- Helper for Lemma 15.128.2: to prove splitting after inverting, it already suffices to
construct localized separating forms as `R`-linear maps; the previous adapter upgrades them to the
`R_f`-linear forms required by the splitting criterion. -/
private theorem selectedSectionsSplitAfterInverting_of_exists_restrictScalars_localized_separating_forms
    (x : Ω) {r : ℕ} (s : Fin r → M)
    (h :
      ∃ f : R, f ∉ x.1.asIdeal ∧
      ∃ τR : Fin r → LocalizedModule.Away f M →ₗ[R] Localization.Away f,
        ∀ i j,
          τR i
            (((LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s)).restrictScalars R)
              ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin r → R))
                ((Pi.basisFun R (Fin r)) j))) =
            if i = j then 1 else 0) :
    selectedSectionsSplitAfterInverting x s := by
  rcases h with ⟨f, hf, τR, hτR⟩
  rcases away_linear_separating_forms_of_restrictScalars_separating_forms
      (R := R) (M := M) f s τR hτR with ⟨τ, hτ⟩
  -- After upgrading the localized forms to away-linearity, the existing splitting criterion
  -- applies verbatim.
  exact
    selectedSectionsSplitAfterInverting_of_exists_localized_separating_forms
      (R := R) (M := M) x s ⟨f, hf, τ, hτ⟩

-- Proof sketch: identify `B(x)` with the orthogonal of the image of `Hom_R(M, R)` in the dual of
-- the fibre `M(x)`. If the localized section map splits, pull the dual basis back to obtain
-- functionals whose classes separate the images of the chosen sections, giving linear independence
-- in `V(x)`. Conversely, lift independent classes in `V(x)` to fibrewise linear forms, use finite
-- presentation together with the localization statement from Algebra, Lemma 10.10.2, and recover a
-- retraction after inverting an element outside `x`.
/-- Lemma 15.128.2: for a closed point `x`, the canonical quotient `V(x)` of the fibre by the
subspace `B(x)` detects when finitely many sections split off a free summand after inverting an
element away from `x`; equivalently, the corresponding classes in `V(x)` are linearly independent
over `κ(x)`. -/
@[stacks 0GV9]
theorem selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    selectedSectionsSplitAfterInverting x s ↔
      LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s) :=
  by
    constructor
    · intro hsplit
      -- Route correction: the source-faithful algebraic core is now isolated in
      -- `linearIndependent_visibleClasses_iff_exists_separating_visible_forms`; the remaining work
      -- is now only to factor the closed-fiber separating forms produced below through the visible
      -- quotient at `x`.
      exact
        (linearIndependent_visibleClasses_iff_exists_separating_visible_forms
          (M := M) x s).2 <|
          exists_visible_separating_forms_of_selectedSectionsSplitAfterInverting
            (R := R) (M := M) x s hsplit
    · intro hlin
      let φ : (Fin r → R) →ₗ[R] M := selectedSectionsMap s
      let U : Set (PrimeSpectrum R) :=
        { p : PrimeSpectrum R |
          Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ.dualMap) }
      have hfiber_surj :
          Function.Surjective
            ((((selectedSectionsMap s).dualMap).rTensor (κ(x))) :
              (Module.Dual R M ⊗[R] κ(x)) →ₗ[R]
                (Module.Dual R (Fin r → R) ⊗[R] κ(x))) := by
        exact
          tensor_dual_selectedSectionsMap_surjective_of_linearIndependent_visibleClasses
            (R := R) (M := M) x s hlin
      have hxU :
          x.1 ∈ U := by
        -- Name the surjective locus once so the openness argument reuses the same object.
        rw [moduleMapSurjectiveLocus_eq_moduleMapFiberSurjectiveLocus (φ := φ.dualMap)]
        simpa [U, φ] using hfiber_surj
      have hopen :
          IsOpen U := by
        -- Reuse the named surjective locus instead of elaborating the same set repeatedly.
        simpa [U, φ] using isOpen_moduleMapSurjectiveLocus (φ := φ.dualMap)
      have hxnhds :
          U ∈ nhds x.1 := by
        exact hopen.mem_nhds hxU
      rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hxnhds with
        ⟨U, hU, hxU', hUsub⟩
      rcases hU with ⟨f, rfl⟩
      have hf : f ∉ x.1.asIdeal := by
        exact (PrimeSpectrum.mem_basicOpen f x.1).1 hxU'
      have hloc_surj :
          Function.Surjective (LocalizedModule.map (.powers f) φ.dualMap) := by
        exact
          surjective_localizedAway_of_D_subset_moduleMapSurjectiveLocus
            (φ := φ.dualMap) f hUsub
      rcases exists_localized_separating_forms_of_localized_dual_surjective
          (R := R) (M := M) (f := f) s hloc_surj with ⟨τR, hτR⟩
      exact
        selectedSectionsSplitAfterInverting_of_exists_restrictScalars_localized_separating_forms
          (R := R) (M := M) x s ⟨f, hf, τR, hτR⟩

end

end
