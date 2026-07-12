import Mathlib
import StacksProject_2024.Chap10.Lemma_10_23_2
import StacksProject_2024.Chap15.Lemma_15_81_1
import StacksProject_2024.Chap15.Lemma_15_81_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

open scoped TensorProduct

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules and locality on a finite principal-open
  cover;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.iff_overAnyFinitelyPresentedCover`,
  `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`,
  `module_finitePresentation_of_localizationAway`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a finitely presented `R`-algebra cover of `A` together with a finite
  presentation of `M` after restricting scalars to that cover;
- derived API: localization and descent lemmas that turn that owner data into ordinary finite
  presentation on local charts and back.

Source/core/bridge triage:
- `source-facing`: the locality theorem below for `Module.FinitePresentationRelativeTo`;
- `core/canonical`: `Module.FinitePresentation` and the principal-open descent theorem
  `module_finitePresentation_of_localizationAway`;
- `bridge/view`: Lemma `15.81.1`, which converts between the relative owner and finite
  presentation over finitely presented covers of `A`.

The public API should stay centered on `Module.FinitePresentationRelativeTo`; the ordinary
finite-presentation theorem is auxiliary descent data, not a second owner for this notion. -/

-- Proof sketch: for `→`, a source-facing relative presentation already implies
-- `Algebra.FiniteType R A`; localize that presentation and apply the chapter's
-- finite-presentation base-change theorem
-- `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`, then identify the
-- resulting tensor product with `LocalizedModule.Away` via `LocalizedModule.equivTensorProduct`.
-- For `←`, each local hypothesis implies `Algebra.FiniteType R (Localization.Away f.1)`, so
-- `Algebra.FiniteType.of_span_eq_top_source hs` recovers `Algebra.FiniteType R A`. Then choose a
-- finitely presented cover of `A`; the local hypotheses and Lemma `15.81.1` make each induced
-- localized module finitely presented over the corresponding localized cover, Lemma `10.23.2`
-- descends finite presentation over that cover, and Lemma `15.81.1` packages the result back
-- into `FinitePresentationRelativeTo`, with the ordinary finite-presentation descent step routed
-- through the chapter's principal-open locality theorem
-- `module_finitePresentation_of_localizationAway`.

namespace Module.FinitePresentationRelativeTo

/-- Helper for Lemma 15.81.8: relative finite presentation transports across an `A`-linear
equivalence. -/
lemma of_equiv
    {N : Type*} {N' : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') :
    FinitePresentationRelativeTo R A N → FinitePresentationRelativeTo R A N' := by
  intro hN
  rcases hN with ⟨n, α, hα, hNfp⟩
  let P := MvPolynomial (Fin n) R
  letI : Module P N := Module.compHom N α.toRingHom
  letI : Module P N' := Module.compHom N' α.toRingHom
  have hmap_smul :
      ∀ c : P, ∀ x : N, e ((α c) • x) = (α c) • e x := by
    -- The transported `P`-action factors through the original `A`-linear equivalence.
    intro c x
    exact e.map_smul (α c) x
  let eP : N ≃ₗ[P] N' :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := hmap_smul }
  -- Keep the same polynomial cover and transport only the finite-presentation witness.
  exact ⟨n, α, hα, Module.FinitePresentation.of_equiv eP⟩

/-- Helper for Lemma 15.81.8: localizing a surjective cover at one element stays surjective. -/
lemma localizationAway_cover_surjective_of_surjective
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (hφ : Function.Surjective φ) (g : B) :
    Function.Surjective (Localization.awayMapₐ φ g) := by
  intro z
  rcases (IsLocalization.mk'_surjective (Submonoid.powers (φ g)) z) with ⟨⟨a, y⟩, rfl⟩
  rcases hφ a with ⟨b, rfl⟩
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨n, rfl⟩
  let hyMap : Submonoid.powers g ≤ Submonoid.comap φ.toRingHom (Submonoid.powers (φ g)) := by
    -- Powers of `g` map to powers of `φ g`, so the universal localization map is defined.
    intro x hx
    rcases hx with ⟨m, rfl⟩
    exact ⟨m, by simp⟩
  refine ⟨IsLocalization.mk' (Localization.Away g) b
      ⟨g ^ n, show g ^ n ∈ Submonoid.powers g from ⟨n, rfl⟩⟩, ?_⟩
  -- On a standard fraction representative, the localized away map acts by applying `φ`
  -- coefficientwise and leaves the denominator power unchanged.
  simpa [Localization.awayMapₐ, hyMap] using
    (IsLocalization.map_mk' (Q := Localization.Away (φ g)) hyMap b
      ⟨g ^ n, show g ^ n ∈ Submonoid.powers g from ⟨n, rfl⟩⟩)

/-- Helper for Lemma 15.81.8: one surjective finitely presented cover of `A` on which `M` is
finitely presented already witnesses relative finite presentation over `R`. -/
lemma of_finitelyPresentedCover
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (φ : B →ₐ[R] A) (hφ : Function.Surjective φ)
    (hM :
      let _ : Module B M := Module.compHom M φ.toRingHom
      Module.FinitePresentation B M) :
    FinitePresentationRelativeTo R A M := by
  letI : Module B M := Module.compHom M φ.toRingHom
  obtain ⟨n, α, hα, hkerα⟩ := (inferInstance : Algebra.FinitePresentation R B).out
  let P := MvPolynomial (Fin n) R
  letI : Algebra P B := α.toRingHom.toAlgebra
  letI : Module P B := Module.compHom B α.toRingHom
  have hPB : Module.FinitePresentation P B := by
    -- Present the cover algebra itself over one polynomial algebra over `R`.
    refine Module.finitePresentation_of_surjective (Algebra.linearMap P B) hα ?_
    simpa using hkerα
  letI : Module.FinitePresentation P B := hPB
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P B M := IsScalarTower.of_compHom P B M
  have hPM : Module.FinitePresentation P M := Module.FinitePresentation.trans P M B
  have hcomp : Function.Surjective ((φ.restrictScalars R).comp α) := by
    -- Compose the chosen polynomial presentation of `B` with the surjective cover `B → A`.
    intro a
    rcases hφ a with ⟨b, rfl⟩
    rcases hα b with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  -- Package the composed polynomial cover together with finite presentation obtained by
  -- transitivity through the finitely presented cover algebra `B`.
  refine ⟨n, (φ.restrictScalars R).comp α, hcomp, ?_⟩
  simpa [P] using hPM

/-- Helper for Lemma 15.81.8: localizing `M` at `g` through the restricted `B`-module structure
agrees with localizing it at `φ g` through the given `A`-module structure, after restricting
scalars along the away map `B[g⁻¹] → A[(φ g)⁻¹]`. -/
private instance localizedModule_awayMap_restrictScalars_id_isLocalizedModule
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B)
    [Module B (Away (φ g) M)]
    [Module (Localization.Away g) (Away (φ g) M)]
    [IsScalarTower B (Localization.Away g) (Away (φ g) M)] :
    IsLocalizedModule (Submonoid.powers g)
      (LinearMap.id : Away (φ g) M →ₗ[B] Away (φ g) M) := by
  -- Once `Away (φ g) M` is viewed as a module over `B[g⁻¹]`, the identity map is already a
  -- localization map for the powers of `g`.
  simpa using
    (isLocalizedModule_id (Submonoid.powers g) (Away (φ g) M) (Localization.Away g))

/-- Helper for Lemma 15.81.8: after restricting scalars along `φ : B →ₐ[R] A`, every `A`-linear
map is automatically `B`-linear. -/
private instance localizedModule_compHom_compatibleSmul
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A)
    {N : Type*} {N' : Type*}
    [AddCommMonoid N] [AddCommMonoid N']
    [Module A N] [Module A N'] :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B N := Module.compHom N φ.toRingHom
    let _ : Module B N' := Module.compHom N' φ.toRingHom
    LinearMap.CompatibleSMul N N' B A := by
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B N := Module.compHom N φ.toRingHom
  let _ : Module B N' := Module.compHom N' φ.toRingHom
  -- The restricted `B`-action is defined through `φ`, so `A`-linearity already gives the
  -- required `B`-linearity.
  refine ⟨?_⟩
  intro f b x
  exact f.map_smul (φ b) x

/-- Helper for Lemma 15.81.8: the canonical map to `Away (φ g) M`, viewed with scalars restricted
along `φ`, is an explicit `B`-linear map. -/
private noncomputable abbrev localizedModule_awayMap_restrictScalars_map
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    let _ : Module B (Away (φ g) M) := Module.compHom (Away (φ g) M) φ.toRingHom
    M →ₗ[B] Away (φ g) M :=
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B M := Module.compHom M φ.toRingHom
  let _ : Module B (Away (φ g) M) := Module.compHom (Away (φ g) M) φ.toRingHom
  let _ : LinearMap.CompatibleSMul M (Away (φ g) M) B A :=
    localizedModule_compHom_compatibleSmul (R := R) (A := A) (φ := φ)
  (LocalizedModule.mkLinearMap (Submonoid.powers (φ g)) M).restrictScalars B

/-- Helper for Lemma 15.81.8: multiplying the standard representative `m / (φ g)^n` by the same
power clears the denominator on the target-side localization. -/
private lemma away_power_smul_mk_eq_mk_one
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) (m : M) (n : ℕ) :
    ((φ (g ^ n)) : A) •
        (LocalizedModule.mk m
          ⟨(φ g) ^ n, show (φ g) ^ n ∈ Submonoid.powers (φ g) from ⟨n, rfl⟩⟩ :
          Away (φ g) M) =
      (LocalizedModule.mkLinearMap (Submonoid.powers (φ g)) M) m := by
  -- Rewrite the scalar action on the standard fraction and then apply the canonical denominator
  -- cancellation formula in the localized module.
  rw [LocalizedModule.smul'_mk]
  simpa [LocalizedModule.mkLinearMap_apply, map_pow] using
    (LocalizedModule.mk_cancel
      (s := ⟨(φ g) ^ n, show (φ g) ^ n ∈ Submonoid.powers (φ g) from ⟨n, rfl⟩⟩)
      (m := m))

/-- Helper for Lemma 15.81.8: equality in `Away (φ g) M` clears after a single power of `g` on
the target-side `A`-module structure. -/
private lemma away_power_exists_of_eq
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) {x₁ x₂ : M}
    (hEq :
      (LocalizedModule.mkLinearMap (Submonoid.powers (φ g)) M) x₁ =
        (LocalizedModule.mkLinearMap (Submonoid.powers (φ g)) M) x₂) :
    ∃ n : ℕ, ((φ (g ^ n)) : A) • x₁ = ((φ (g ^ n)) : A) • x₂ := by
  -- Use the owner localization API over `A`, then rewrite the resulting denominator as `(φ g)^n`.
  obtain ⟨t, ht⟩ :=
    IsLocalizedModule.exists_of_eq (S := Submonoid.powers (φ g))
      (f := LocalizedModule.mkLinearMap (Submonoid.powers (φ g)) M) hEq
  rcases t with ⟨t, htPow⟩
  rcases htPow with ⟨n, rfl⟩
  exact ⟨n, by simpa [map_pow] using ht⟩

/-- Helper for Lemma 15.81.8: `Away (φ g) M` carries its canonical `B[g⁻¹]`-module structure via
the away map `B[g⁻¹] → A[(φ g)⁻¹]`. -/
private noncomputable instance awayMap_targetModule
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    Module (Localization.Away g) (Away (φ g) M) :=
  Module.compHom (Away (φ g) M) (Localization.awayMapₐ φ g).toRingHom

/-- Helper for Lemma 15.81.8: the target localization keeps the original `B`-action after
restricting scalars along `φ : B → A`. -/
private noncomputable instance compHom_targetModule
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    Module B (Away (φ g) M) :=
  Module.compHom (Away (φ g) M) φ.toRingHom

/-- Helper for Lemma 15.81.8: the `B[g⁻¹]`-action on the target-side localization extends the
restricted `B`-action coming from `φ : B →ₐ[R] A`. -/
private noncomputable instance awayMap_target_isScalarTower
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    IsScalarTower B (Localization.Away g) (Away (φ g) M) := by
  let _ : Module (Localization.Away g) (Away (φ g) M) := awayMap_targetModule (R := R) (A := A)
    (M := M) φ g
  let _ : Module B (Away (φ g) M) := compHom_targetModule (R := R) (A := A) (M := M) φ g
  -- Both scalar actions are defined by applying `φ` to the numerator, so the tower is
  -- definitionally compatible on the target localized module.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro b m
  let hyMap : Submonoid.powers g ≤ Submonoid.comap φ.toRingHom (Submonoid.powers (φ g)) := by
    -- Powers of `g` map to powers of `φ g`, so the away map is the canonical localization map.
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  have hmap :
      (Localization.awayMapₐ φ g) (algebraMap B (Localization.Away g) b) =
        algebraMap A (Localization.Away (φ g)) (φ b) := by
    -- Evaluate the away map on the standard numerator `b / 1`.
    rw [← IsLocalization.mk'_one (M := Submonoid.powers g) (Localization.Away g) b]
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (φ g))
      (Localization.Away (φ g)) (φ b)]
    simpa [Localization.awayMapₐ, hyMap] using
      (IsLocalization.map_mk' (Q := Localization.Away (φ g)) hyMap b (1 : Submonoid.powers g))
  -- After rewriting the scalar from `B[g⁻¹]`, the action is the original `A`-action.
  change ((Localization.awayMapₐ φ g) (algebraMap B (Localization.Away g) b)) • m = b • m
  rw [hmap]
  show (algebraMap A (Localization.Away (φ g)) (φ b)) • m = (φ b) • m
  exact IsScalarTower.algebraMap_smul (Localization.Away (φ g)) (φ b) m

/-- Helper for Lemma 15.81.8: localizing `M` at `g` through the restricted `B`-module structure
agrees with localizing it at `φ g` through the given `A`-module structure, after restricting
scalars along the away map `B[g⁻¹] → A[(φ g)⁻¹]`. -/
private lemma localizedModule_awayMap_restrictScalars_isLocalizedModule
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    IsLocalizedModule (Submonoid.powers g)
      (localizedModule_awayMap_restrictScalars_map (R := R) (A := A) (M := M) φ g) := by
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B M := Module.compHom M φ.toRingHom
  let _ : Module (Localization.Away g) (Away (φ g) M) := awayMap_targetModule (R := R) (A := A)
    (M := M) φ g
  let _ : Module B (Away (φ g) M) := compHom_targetModule (R := R) (A := A) (M := M) φ g
  let _ : IsScalarTower B (Localization.Away g) (Away (φ g) M) :=
    awayMap_target_isScalarTower (R := R) (A := A) (M := M) φ g
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro x
    -- The target carries a genuine `B[g⁻¹]`-module structure, so powers of `g` act by units.
    exact IsLocalizedModule.map_units
      (f := (LinearMap.id : Away (φ g) M →ₗ[B] Away (φ g) M)) x
  · intro y
    -- Every target-side fraction has a representative `m / (φ g)^n`, and the same power of `g`
    -- clears that denominator after restricting scalars along `φ`.
    refine LocalizedModule.induction_on ?_ y
    intro m s
    rcases s with ⟨s, hs⟩
    rcases hs with ⟨n, rfl⟩
    refine ⟨⟨m, ⟨g ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
    change ((φ (g ^ n)) : A) •
        (LocalizedModule.mk m
          ⟨(φ g) ^ n, show (φ g) ^ n ∈ Submonoid.powers (φ g) from ⟨n, rfl⟩⟩ :
          Away (φ g) M) =
      (localizedModule_awayMap_restrictScalars_map (R := R) (A := A) (M := M) φ g) m
    simpa [localizedModule_awayMap_restrictScalars_map] using
      away_power_smul_mk_eq_mk_one (R := R) (A := A) (M := M) φ g m n
  · intro x₁ x₂ hEq
    -- Equality on the target localization clears after one power of `g`, and that same power is
    -- exactly the restricted `B`-scalar on the source module.
    obtain ⟨n, hn⟩ :=
      away_power_exists_of_eq (R := R) (A := A) (M := M) φ g hEq
    refine ⟨⟨g ^ n, ⟨n, rfl⟩⟩, ?_⟩
    change ((φ (g ^ n)) : A) • x₁ = ((φ (g ^ n)) : A) • x₂
    simpa [map_pow] using hn

/-- Helper for Lemma 15.81.8: localizing `M` at `g` through the restricted `B`-module structure
agrees with localizing it at `φ g` through the given `A`-module structure, after restricting
scalars along the away map `B[g⁻¹] → A[(φ g)⁻¹]`. -/
noncomputable abbrev localizedModule_awayMap_restrictScalars_base_equiv
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    Away g M ≃ₗ[B] Away (φ g) M := by
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B M := Module.compHom M φ.toRingHom
  let _ : Module (Localization.Away g) (Away (φ g) M) := awayMap_targetModule (R := R) (A := A)
    (M := M) φ g
  let _ : Module B (Away (φ g) M) := compHom_targetModule (R := R) (A := A) (M := M) φ g
  let _ : IsScalarTower B (Localization.Away g) (Away (φ g) M) :=
    awayMap_target_isScalarTower (R := R) (A := A) (M := M) φ g
  let _ : IsLocalizedModule (Submonoid.powers g)
      (localizedModule_awayMap_restrictScalars_map (R := R) (A := A) (M := M) φ g) :=
    localizedModule_awayMap_restrictScalars_isLocalizedModule (R := R) (A := A) (M := M) φ g
  -- Compare the universal `B[g⁻¹]`-localization of the restricted `B`-module with the same
  -- localization viewed on the `A`-side after restricting scalars along `φ`.
  exact IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (localizedModule_awayMap_restrictScalars_map (R := R) (A := A) (M := M) φ g)

/-- Helper for Lemma 15.81.8: localizing `M` at `g` through the restricted `B`-module structure
agrees with localizing it at `φ g` through the given `A`-module structure, after restricting
scalars along the away map `B[g⁻¹] → A[(φ g)⁻¹]`. -/
noncomputable abbrev localizedModule_awayMap_restrictScalars_equiv
    {B : Type*} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (g : B) :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    Away g M ≃ₗ[Localization.Away g] Away (φ g) M := by
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B M := Module.compHom M φ.toRingHom
  let _ : Module (Localization.Away g) (Away (φ g) M) := awayMap_targetModule (R := R) (A := A)
    (M := M) φ g
  let _ : Module B (Away (φ g) M) := compHom_targetModule (R := R) (A := A) (M := M) φ g
  let _ : IsScalarTower B (Localization.Away g) (Away (φ g) M) :=
    awayMap_target_isScalarTower (R := R) (A := A) (M := M) φ g
  -- Route correction: first build the comparison over the source ring `B`, then upgrade it to
  -- the away localization `B[g⁻¹]` by scalar extension.
  exact
    LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers g) (Localization.Away g)
      (localizedModule_awayMap_restrictScalars_base_equiv (R := R) (A := A) (M := M) φ g)

/-- Helper for Lemma 15.81.8: after localizing a surjective finitely presented cover `φ : B → A`
at one chosen lift `g : B`, the source-side localized module is finitely presented over
`B[g⁻¹]` whenever the target-side localized module is finitely presented relative to `R`. -/
lemma finitePresentation_on_localized_cover_chart
    {B : Type x} [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (φ : B →ₐ[R] A) (hφ : Function.Surjective φ) (g : B)
    (hchart : FinitePresentationRelativeTo R (Localization.Away (φ g)) (Away (φ g) M)) :
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    Module.FinitePresentation (Localization.Away g) (Away g M) := by
  let _ : Algebra B A := φ.toRingHom.toAlgebra
  let _ : Module B M := Module.compHom M φ.toRingHom
  let S := Localization.Away g
  let Sup := ULift.{u} S
  let ψ : Sup →ₐ[R] Localization.Away (φ g) :=
    (Localization.awayMapₐ φ g).comp
      (ULift.algEquiv : Sup ≃ₐ[R] S).toAlgHom
  have hψ : Function.Surjective ψ := by
    -- The localized cover remains surjective after inserting the `ULift` universe adapter.
    intro z
    rcases localizationAway_cover_surjective_of_surjective (R := R) (A := A) φ hφ g z with
      ⟨y, hy⟩
    refine ⟨ULift.up y, ?_⟩
    simpa [ψ, Sup, S]
  letI : Algebra.FinitePresentation R S := by
    -- First localize the finitely presented cover algebra `B`, then compose with `R → B`.
    exact Algebra.FinitePresentation.trans R B S
  letI : Algebra.FinitePresentation R Sup := by
    -- Transport finite presentation across the canonical `ULift` algebra equivalence.
    exact Algebra.FinitePresentation.equiv
      ((ULift.algEquiv : Sup ≃ₐ[R] S).symm)
  let moduleS : Module S (Away (φ g) M) :=
    awayMap_targetModule (R := R) (A := A) (M := M) φ g
  letI : Module S (Away (φ g) M) := moduleS
  letI : Module B (Away (φ g) M) := compHom_targetModule (R := R) (A := A) (M := M) φ g
  letI : IsScalarTower B S (Away (φ g) M) :=
    awayMap_target_isScalarTower (R := R) (A := A) (M := M) φ g
  let moduleSup : Module Sup (Away (φ g) M) := Module.compHom (Away (φ g) M) ψ.toRingHom
  letI : Module Sup (Away (φ g) M) := moduleSup
  have hSup :
      Module.FinitePresentation Sup (Away (φ g) M) := by
    -- Apply the source-facing cover theorem on the localized chart `A[(φ g)⁻¹]`.
    simpa [ψ, Sup, S] using
      hchart.overAnyFinitelyPresentedCover Sup ψ hψ
  let tower : IsScalarTower S Sup (Away (φ g) M) := IsScalarTower.of_algebraMap_smul fun s m ↦ by
    -- The lifted action is exactly the localized `B[g⁻¹]`-action composed with `ULift.down`.
    change ψ (algebraMap S Sup s) • m =
      (Localization.awayMapₐ φ g) s • m
    rfl
  letI : IsScalarTower S Sup (Away (φ g) M) := tower
  let finiteSup : Module.Finite S Sup := by
    -- Every lifted localization element comes from its `down` representative.
    have hsurj : Function.Surjective (algebraMap S Sup) := by
      intro q
      refine ⟨q.down, ?_⟩
      cases q
      rfl
    exact Module.Finite.of_surjective (Algebra.linearMap S Sup) hsurj
  let algFpSup : Algebra.FinitePresentation S Sup := by
    let upAlg : S →ₐ[S] Sup := Algebra.ofId S Sup
    have hupSurj : Function.Surjective upAlg := by
      intro q
      refine ⟨q.down, ?_⟩
      cases q
      rfl
    have hupInj : Function.Injective upAlg := by
      intro s₁ s₂ hs
      exact congrArg ULift.down hs
    have hker : (RingHom.ker upAlg.toRingHom).FG := by
      have hker_eq : RingHom.ker upAlg.toRingHom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot upAlg.toRingHom).mp hupInj
      rw [hker_eq]
      exact Submodule.fg_bot
    exact Algebra.FinitePresentation.of_surjective (f := upAlg) hupSurj hker
  letI : Module.Finite S Sup := finiteSup
  letI : Algebra.FinitePresentation S Sup := algFpSup
  have hS :
      Module.FinitePresentation S (Away (φ g) M) := by
    -- Descend along the finite finitely presented algebra map `S → ULift S`.
    have hiff :
        Module.FinitePresentation S (Away (φ g) M) ↔
          Module.FinitePresentation Sup (Away (φ g) M) :=
      @Module.FinitePresentation.iff_of_finite_finitePresentation S Sup (Away (φ g) M)
        inferInstance inferInstance inferInstance inferInstance moduleSup moduleS tower
        finiteSup algFpSup
    exact hiff.mpr hSup
  letI : Module.FinitePresentation S (Away (φ g) M) := hS
  -- Transport finite presentation back to the source-side localized module.
  exact Module.FinitePresentation.of_equiv
    (localizedModule_awayMap_restrictScalars_equiv (R := R) (A := A) (M := M) φ g).symm

/-- Helper for Lemma 15.81.8: a finite family spanning the unit ideal admits an explicit unit
relation indexed by that family. -/
lemma exists_unit_relation_on_finset
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤) :
    ∃ c : A → A, Finset.sum s (fun a ↦ c a * a) = 1 := by
  have hOne : (1 : A) ∈ Ideal.span (s : Set A) := by
    -- Convert the unit-ideal hypothesis into the concrete membership witness needed by
    -- `Submodule.mem_span_finset`.
    simpa [Ideal.eq_top_iff_one] using hs
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hOne
  -- `Submodule.mem_span_finset` already returns the sum over the original finset `s`.
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

/-- Helper for Lemma 15.81.8: quotienting a polynomial ring by one explicit relation stays
finitely presented over the base ring. -/
lemma finitePresentation_of_single_relation_quotient
    (n : ℕ) (u : MvPolynomial (Fin n) R) :
    Algebra.FinitePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span ({u} : Set (MvPolynomial (Fin n) R))) := by
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := Ideal.span ({u} : Set P)
  letI : Algebra.FinitePresentation R P := by
    -- The polynomial ring itself is finitely presented over `R`.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := R) (Fin n))
  have hI : I.FG := by
    -- A principal relation ideal is finitely generated by its single defining element.
    simpa [I] using (Submodule.fg_span (Set.finite_singleton u) : I.FG)
  -- Quotient finite presentation along the finitely generated relation ideal.
  simpa [P, I] using
    (Algebra.FinitePresentation.quotient (R := R) (A := P) (I := I) hI)

/-- Helper for Lemma 15.81.8: the quotient images of generators satisfying one lifted unit
relation still span the unit ideal after imposing that relation. -/
lemma span_top_of_single_relation_quotient_lifts
    (n : ℕ) (s : Finset A) (aLift cLift : s → MvPolynomial (Fin n) R) :
    let P := MvPolynomial (Fin n) R
    let u : P := (∑ f : s, cLift f * aLift f) - 1
    let I : Ideal P := Ideal.span ({u} : Set P)
    let B := P ⧸ I
    let gLift : s → B := fun f ↦ Ideal.Quotient.mk I (aLift f)
    Ideal.span (Set.range gLift) = ⊤ := by
  classical
  let P := MvPolynomial (Fin n) R
  let u : P := (∑ f : s, cLift f * aLift f) - 1
  let I : Ideal P := Ideal.span ({u} : Set P)
  let B := P ⧸ I
  let gLift : s → B := fun f ↦ Ideal.Quotient.mk I (aLift f)
  rw [Ideal.eq_top_iff_one]
  have hu_zero : (Ideal.Quotient.mk I u : B) = 0 := by
    -- The defining relation vanishes in the quotient by construction.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [u]))
  have hsum_eq :
      ∑ f : s, (Ideal.Quotient.mk I (cLift f) : B) * gLift f = 1 := by
    -- Rewriting the quotient image of the defining relation isolates the unit combination.
    have hu_sum :
        (Ideal.Quotient.mk I u : B) =
          (∑ f : s, (Ideal.Quotient.mk I (cLift f) : B) * gLift f) - 1 := by
      simp [u, gLift, map_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [hu_sum] at hu_zero
    exact sub_eq_zero.mp hu_zero
  -- The explicit unit combination already lies in the span of the quotient lifts.
  refine hsum_eq ▸ Submodule.sum_mem _ ?_
  intro f hf
  have hg : gLift f ∈ Ideal.span (Set.range gLift) := Ideal.subset_span (Set.mem_range_self f)
  exact Ideal.mul_mem_left _ _ hg

omit [CommRing A] in
/-- Helper for Lemma 15.81.8: the finite image of the attached generators is exactly their set
range. -/
lemma attach_image_eq_range
    {B : Type*} [DecidableEq B] (s : Finset A) (gLift : s → B) :
    (((s.attach.image gLift : Finset B) : Set B) = Set.range gLift) := by
  ext b
  constructor
  · intro hb
    rw [Finset.mem_coe, Finset.mem_image] at hb
    rcases hb with ⟨f, -, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    rw [Finset.mem_coe]
    exact Finset.mem_image.mpr ⟨f, Finset.mem_attach _ _, rfl⟩

/-- Helper for Lemma 15.81.8: from a unit relation on the chosen cover generators, build a single
finitely presented cover of `A` whose chosen lifts already span the unit ideal. -/
lemma exists_finitelyPresented_cover_with_unit_ideal_lifts
    [Algebra.FiniteType R A]
    (s : Finset A) (c : A → A) (hc : Finset.sum s (fun a ↦ c a * a) = 1) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B)
      (_ : Algebra.FinitePresentation R B) (φ : B →ₐ[R] A),
      Function.Surjective φ ∧
        ∃ gLift : s → B, (∀ f : s, φ (gLift f) = f.1) ∧
          Ideal.span (Set.range gLift) = ⊤ := by
  classical
  obtain ⟨n, α, hα⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
  let P := MvPolynomial (Fin n) R
  let aLift : s → P := fun f ↦ Classical.choose (hα f.1)
  have haLift : ∀ f : s, α (aLift f) = f.1 := fun f ↦ Classical.choose_spec (hα f.1)
  let cLift : s → P := fun f ↦ Classical.choose (hα (c f.1))
  have hcLift : ∀ f : s, α (cLift f) = c f.1 := fun f ↦ Classical.choose_spec (hα (c f.1))
  let u : P := (∑ f : s, cLift f * aLift f) - 1
  let I : Ideal P := Ideal.span ({u} : Set P)
  let B₀ := P ⧸ I
  let φ₀ : B₀ →ₐ[R] A :=
    Ideal.Quotient.liftₐ I α <| by
      intro z hz
      have hIker : I ≤ RingHom.ker α.toRingHom := by
        -- The quotient relation was chosen so that its image under `α` is exactly zero.
        refine Ideal.span_le.2 ?_
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        have hc_swap := by
          simpa [mul_comm] using hc
        simpa [RingHom.mem_ker, u, hc_swap, haLift, hcLift, map_sum, map_sub,
          mul_comm, mul_left_comm, mul_assoc]
      simpa [RingHom.mem_ker] using hIker hz
  have hφ₀_surj : Function.Surjective φ₀ := by
    -- Surjectivity descends from the original polynomial presentation through the quotient map.
    intro a
    rcases hα a with ⟨p, rfl⟩
    refine ⟨Ideal.Quotient.mk I p, ?_⟩
    rfl
  have hB₀fp : Algebra.FinitePresentation R B₀ := by
    -- The cover ring is a single-relation quotient of a polynomial ring.
    simpa [B₀, I, u, P] using
      finitePresentation_of_single_relation_quotient (R := R) n u
  let gLift₀ : s → B₀ := fun f ↦ Ideal.Quotient.mk I (aLift f)
  have hspan₀ : Ideal.span (Set.range gLift₀) = ⊤ := by
    simpa [B₀, I, u, P, gLift₀] using
      span_top_of_single_relation_quotient_lifts (R := R) (A := A) n s aLift cLift
  let B := ULift.{max v w} B₀
  have hBfp : Algebra.FinitePresentation R B := by
    -- Transport finite presentation across the canonical `ULift` algebra equivalence.
    exact Algebra.FinitePresentation.equiv
      ((ULift.algEquiv : B ≃ₐ[R] B₀).symm)
  let φ : B →ₐ[R] A :=
    φ₀.comp (ULift.algEquiv : B ≃ₐ[R] B₀).toAlgHom
  have hφ_surj : Function.Surjective φ := by
    -- The lifted cover remains surjective because `ULift.up` is a section of `down`.
    intro a
    rcases hφ₀_surj a with ⟨b, hb⟩
    exact ⟨ULift.up b, hb⟩
  let gLift : s → B := fun f ↦ ULift.up (gLift₀ f)
  have hrange :
      Set.image ((ULift.algEquiv : B ≃ₐ[R] B₀).symm.toRingHom) (Set.range gLift₀) =
        Set.range gLift := by
    ext b
    constructor
    · rintro ⟨b₀, ⟨f, rfl⟩, hb⟩
      exact ⟨f, by simpa [gLift] using hb⟩
    · rintro ⟨f, rfl⟩
      exact ⟨gLift₀ f, ⟨f, rfl⟩, rfl⟩
  have hrange' :
      ((fun a ↦ (ULift.algEquiv : B ≃ₐ[R] B₀).symm a) '' Set.range gLift₀) = Set.range gLift := by
    simpa using hrange
  have hspan : Ideal.span (Set.range gLift) = ⊤ := by
    -- The `ULift` algebra equivalence carries the spanning family to the lifted one.
    have hmap :=
      congrArg (Ideal.map ((ULift.algEquiv : B ≃ₐ[R] B₀).symm.toRingHom)) hspan₀
    have hmap' :
        Ideal.span (((fun a ↦ (ULift.algEquiv : B ≃ₐ[R] B₀).symm a) '' Set.range gLift₀)) = ⊤ := by
      simpa [Ideal.map_span, Ideal.map_top] using hmap
    simpa [hrange'] using hmap'
  refine ⟨B, inferInstance, inferInstance, hBfp, φ, hφ_surj, gLift, ?_, hspan⟩
  · intro f
    -- The chosen quotient lift still maps to the original generator in `A`.
    change φ₀ (gLift₀ f) = f.1
    change α (aLift f) = f.1
    exact haLift f

/-- Lemma 15.81.8: for an `R`-algebra `A`, an `A`-module `M`, and finitely many elements of `A`
generating the unit ideal, `M` is finitely presented relative to `R` if and only if each
principal localization `M_f` is finitely presented relative to `R`; the localized hypotheses
already force `A` to be finite type over `R`. -/
@[stacks 065D]
theorem iff_localizationAway_unitIdeal
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤) :
    FinitePresentationRelativeTo R A M ↔
      ∀ f : s, FinitePresentationRelativeTo R (Localization.Away f.1) (Away f.1 M) := by
  constructor
  · intro hM f
    letI : Algebra.FinitePresentation A (Localization.Away f.1) :=
      IsLocalization.Away.finitePresentation f.1
    -- Base change the relative presentation to the principal localization `A[f⁻¹]`.
    have hTensor :
        Module.FinitePresentationRelativeTo R (Localization.Away f.1)
          ((Localization.Away f.1) ⊗[A] M) :=
      Module.finitePresentationRelativeTo_baseChange_of_finitePresentation
        (R := R) (A := A) (A' := Localization.Away f.1) (M := M) hM
    let eTensor : Away f.1 M ≃ₗ[Localization.Away f.1] (Localization.Away f.1) ⊗[A] M :=
      LocalizedModule.equivTensorProduct (Submonoid.powers f.1) M
    -- Transport the localized finite-presentation witness across the tensor/localization
    -- comparison equivalence.
    exact of_equiv (R := R) (A := Localization.Away f.1) eTensor.symm hTensor
  · intro h
    have hAft : Algebra.FiniteType R A := by
      -- The local relative hypotheses imply finite type on each principal chart, so finite type
      -- descends from the target-side cover.
      refine Algebra.FiniteType.of_span_eq_top_target (s := (s : Set A)) hs ?_
      intro a ha
      exact (h ⟨a, ha⟩).finiteType
    classical
    letI : Algebra.FiniteType R A := hAft
    obtain ⟨c, hc⟩ := exists_unit_relation_on_finset (A := A) s hs
    obtain ⟨B, hBComm, hBRAlg, hBfp, φ, hφ, gLift, hgLift, hspan⟩ :
        ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B)
          (_ : Algebra.FinitePresentation R B) (φ : B →ₐ[R] A),
          Function.Surjective φ ∧
            ∃ gLift : s → B, (∀ f : s, φ (gLift f) = f.1) ∧
              Ideal.span (Set.range gLift) = ⊤ :=
      exists_finitelyPresented_cover_with_unit_ideal_lifts
        (R := R) (A := A) s c hc
    letI : CommRing B := hBComm
    letI : Algebra R B := hBRAlg
    letI : Algebra.FinitePresentation R B := hBfp
    let _ : Algebra B A := φ.toRingHom.toAlgebra
    let _ : Module B M := Module.compHom M φ.toRingHom
    have hBM : Module.FinitePresentation B M := by
      -- Route correction: keep the explicit quotient cover fixed and descend chartwise over the
      -- lifted principal-open cover before repackaging through the finitely presented cover.
      let t : Finset B := s.attach.image gLift
      have htspan : Ideal.span (t : Set B) = ⊤ := by
        -- Rewrite the span-top hypothesis from the lifted family `gLift` to the finite chart set
        -- used by the principal-open descent theorem.
        rw [attach_image_eq_range (A := A) (B := B) s gLift]
        simpa [t] using hspan
      have hchart :
          ∀ g : t, Module.FinitePresentation (Localization.Away g.1) (Away g.1 M) := by
        intro g
        -- Recover the original source generator whose chosen lift is the chart element `g`.
        rcases Finset.mem_image.mp g.2 with ⟨f, -, hf⟩
        have hfg :
            FinitePresentationRelativeTo R (Localization.Away (φ (gLift f)))
              (Away (φ (gLift f)) M) := by
          rw [hgLift f]
          exact h f
        have hgf :
            Module.FinitePresentation (Localization.Away (gLift f)) (Away (gLift f) M) :=
          finitePresentation_on_localized_cover_chart
            (R := R) (A := A) (M := M) φ hφ (gLift f) hfg
        rw [← hf]
        exact hgf
      -- The lifted generators define a finite principal-open cover of `Spec B`, so apply the
      -- ordinary locality theorem there.
      exact module_finitePresentation_of_localizationAway (R := B) (s := t) htspan hchart
    -- The finitely presented cover now packages the descended `B`-module presentation back into
    -- relative finite presentation over `R`.
    exact of_finitelyPresentedCover (R := R) (A := A) (M := M) φ hφ <| by
      simpa using hBM

end Module.FinitePresentationRelativeTo

end
