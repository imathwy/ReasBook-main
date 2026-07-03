import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_9_1 (from Chap10) -/
universe u

section

variable (R : Type u) [MulOneClass R]

/- Definition 10.9.1 (Tag 00CN) is recalled canonically by `Submonoid R`: a multiplicative subset
of `R` is exactly a subset containing `1` and closed under multiplication. -/
recall Submonoid

/- Primitive data of the owner structure are its carrier together with `one_mem'` and `mul_mem'`.
Downstream API should use the canonical coercion to `Set R` and the derived theorems below. -/
#check (SetLike.coe : Submonoid R → Set R)

/- Companion recall: the textbook condition `1 ∈ S` is the canonical theorem `Submonoid.one_mem`. -/
recall Submonoid.one_mem

/- Companion recall: the textbook closure condition is the canonical theorem `Submonoid.mul_mem`. -/
recall Submonoid.mul_mem

end

/-! ### Definition_10_9_2 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] (S : Submonoid A)

/- Definition 10.9.2: for a commutative ring `A` and a submonoid `S`, the canonical ring
`Localization S` is the localization of `A` with respect to `S`. -/
recall Localization

/- Companion recall: the owner abstraction for the statement that `Localization S` is the
localization of `A` with respect to `S` is the canonical instance
`Localization.isLocalization : IsLocalization S (Localization S)`. -/
recall Localization.isLocalization

/- Companion recall: the natural localization map `A → Localization S`, sending `x` to `x / 1`,
is the canonical ring homomorphism `algebraMap A (Localization S)`, characterized by
`Localization.mk_one_eq_algebraMap`. -/
recall Localization.mk_one_eq_algebraMap

end

/-! ### Proposition_10_9_3 (from Chap10) -/
section

universe u v

variable {A : Type u} [CommRing A]
variable (S : Submonoid A)
variable {B : Type v} [CommRing B]

/- Domain triage:
* source-facing clauses: the universal property of the localization map `A → Localization S`.
* core/canonical owner: `IsLocalization`.
* primitive data: the localization instance and `algebraMap A (Localization S)`.
* derived API used here: `IsLocalization.lift`, `IsLocalization.lift_comp`,
  `IsLocalization.ringHom_ext`, and `IsLocalization.lift_unique`.
-/

/- Proposition 10.9.3 (1): if `f : A →+* B` sends every element of `S` to a unit, then the
universal property of localization is exactly the canonical owner construction
`IsLocalization.lift`. -/
recall IsLocalization.lift

/- Proposition 10.9.3 (2): the canonical lift commutes with the localization map. This is exactly
`IsLocalization.lift_comp`. -/
recall IsLocalization.lift_comp

/-
Companion recall: equality of ring homomorphisms out of a localization is already controlled by
precomposition with the localization map.
-/
recall IsLocalization.ringHom_ext

/- Proposition 10.9.3 (3): any ring homomorphism `Localization S →+* B` agreeing with `f` after
precomposition with the localization map is equal to the canonical lift. This is exactly
`IsLocalization.lift_unique`. -/
recall IsLocalization.lift_unique

end

/-! ### Lemma_10_9_4 (from Chap10) -/
universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.4 is a `bridge/view` item. Its owner abstraction is the canonical localization
theorem `IsLocalization.subsingleton_iff`; the textbook statement is its specialization to
`Localization S`. -/
recall IsLocalization.subsingleton_iff

end

/-! ### Lemma_10_9_5 (from Chap10) -/
open CategoryTheory
open IsLocalizedModule

universe u

-- `IsLocalizedModule` is available over commutative semirings, but this item is expressed in
-- `ModuleCat`, whose bundled change-of-rings and localization APIs are ring-based.
variable {R : Type u} [CommRing R] (S : Submonoid R)

private def invertibleActionProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)

private theorem isLocalizedModule_id_of_invertibleAction
    (M : ModuleCat R) (hM : invertibleActionProperty S M) :
    IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) where
  map_units := hM
  surj m := ⟨(m, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

private def localizedIdProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)

private theorem localizedIdProperty_iff_invertibleAction (M : ModuleCat R) :
    localizedIdProperty S M ↔ invertibleActionProperty S M := by
  constructor
  · intro h s
    exact h.map_units s
  · intro h
    exact isLocalizedModule_id_of_invertibleAction S M h

/-- Restriction of scalars along `R → S⁻¹R` lands in the full subcategory of `R`-modules whose
identity map is a localized module map, i.e. the owner formulation of invertible `S`-action. -/
private theorem localizationModulesToLocalizedIdModules_obj_mem
    (M : ModuleCat (Localization S)) :
    localizedIdProperty S ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj M) := by
  let _ : Module R M := Module.compHom M (algebraMap R (Localization S))
  let _ : IsScalarTower R (Localization S) M := RestrictScalars.isScalarTower R (Localization S) M
  simpa using (isLocalizedModule_id S M (Localization S))

private noncomputable def localizationModulesToLocalizedIdModules :
    ModuleCat (Localization S) ⥤ (localizedIdProperty S).FullSubcategory :=
  (localizedIdProperty S).lift
    (ModuleCat.restrictScalars (algebraMap R (Localization S)))
    (localizationModulesToLocalizedIdModules_obj_mem S)

private noncomputable instance localizationModulesToLocalizedIdModules_faithful :
    (localizationModulesToLocalizedIdModules S).Faithful := by
  dsimp [localizationModulesToLocalizedIdModules]
  infer_instance

private noncomputable instance localizationModulesToLocalizedIdModules_full :
    (localizationModulesToLocalizedIdModules S).Full where
  map_surjective := by
    intro M N f
    let _ : Module R M := Module.compHom M (algebraMap R (Localization S))
    let _ : Module R N := Module.compHom N (algebraMap R (Localization S))
    let _ : IsScalarTower R (Localization S) M := RestrictScalars.isScalarTower R (Localization S) M
    let _ : IsScalarTower R (Localization S) N := RestrictScalars.isScalarTower R (Localization S) N
    refine ⟨ModuleCat.ofHom <|
      (show M →ₗ[R] N from f.hom.hom).extendScalarsOfIsLocalization S (Localization S), ?_⟩
    ext x
    rfl

private noncomputable instance localizationModulesToLocalizedIdModules_essSurj :
    (localizationModulesToLocalizedIdModules S).EssSurj where
  mem_essImage := by
    intro M
    letI : IsLocalizedModule S (LinearMap.id : M.obj →ₗ[R] M.obj) :=
      M.property
    letI : Module (Localization S) M.obj :=
      IsLocalizedModule.module S (LinearMap.id : M.obj →ₗ[R] M.obj)
    letI : IsScalarTower R (Localization S) M.obj :=
      IsLocalizedModule.isScalarTower_module S (LinearMap.id : M.obj →ₗ[R] M.obj)
    let hom :
        ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
          (ModuleCat.of (Localization S) M.obj)) →ₗ[R] M.obj :=
      { toFun := fun x ↦ x
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; simp }
    let inv :
        M.obj →ₗ[R]
          ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
            (ModuleCat.of (Localization S) M.obj)) :=
      { toFun := fun x ↦ x
        map_add' := by intro x y; rfl
        map_smul' := by
          intro r x
          have h := (algebraMap_smul (Localization S) r x).symm
          convert h using 1 }
    refine ⟨ModuleCat.of (Localization S) M.obj, ?_⟩
    refine ⟨(localizedIdProperty S).isoMk ?_⟩
    refine
      { hom := show
            ((localizationModulesToLocalizedIdModules S).obj
              (ModuleCat.of (Localization S) M.obj)).obj ⟶ M.obj from
            ConcreteCategory.ofHom hom
        inv := show
            M.obj ⟶
              ((localizationModulesToLocalizedIdModules S).obj
                (ModuleCat.of (Localization S) M.obj)).obj from
            ConcreteCategory.ofHom inv }

private noncomputable instance :
    (localizationModulesToLocalizedIdModules S).IsEquivalence :=
  {}

private noncomputable def localizationModuleEquivalenceToLocalizedId :
    ModuleCat (Localization S) ≌ (localizedIdProperty S).FullSubcategory :=
  (localizationModulesToLocalizedIdModules S).asEquivalence

private noncomputable def localizedIdEquivInvertibleAction :
    (localizedIdProperty S).FullSubcategory ≌ (invertibleActionProperty S).FullSubcategory where
  functor :=
    (invertibleActionProperty S).lift ((localizedIdProperty S).ι) fun M ↦
      (localizedIdProperty_iff_invertibleAction S M.obj).1 M.property
  inverse :=
    (localizedIdProperty S).lift ((invertibleActionProperty S).ι) fun M ↦
      (localizedIdProperty_iff_invertibleAction S M.obj).2 M.property
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Lemma 10.9.5: the category of `S⁻¹R`-modules is equivalent to the full subcategory of
`R`-modules on which every element of `S` acts as an automorphism. -/
noncomputable def localizationModuleEquivalence :
    ModuleCat (Localization S) ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat R ↦ ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)) :=
  (localizationModuleEquivalenceToLocalizedId S).trans (localizedIdEquivInvertibleAction S)

-- Proof sketch: the forward functor of `localizationModuleEquivalence` lands in the defining full
-- subcategory, so its image object carries the stated invertibility property by construction.
/-- The forward functor of `localizationModuleEquivalence` sends an `S⁻¹R`-module to an `R`-module
on which every element of `S` acts invertibly. -/
theorem localizationModuleEquivalence_functor_obj_isUnit
    (M : ModuleCat (Localization S)) (s : S) :
    IsUnit
      (algebraMap R
        (Module.End R ((localizationModuleEquivalence S).functor.obj M).obj) s) := by
  -- The image object already lies in the defining full subcategory, so evaluate its stored
  -- invertibility property at the chosen element `s : S`.
  exact ((localizationModuleEquivalence S).functor.obj M).property s

/-! ### Definition_10_9_6 (from Chap10) -/
universe u v

section

variable (A : Type u) [CommSemiring A] (S : Submonoid A)
variable (M : Type v) [AddCommMonoid M] [Module A M]

/- Definition 10.9.6: for a commutative semiring `A`, a submonoid `S`, and an `A`-module `M`,
the localized module `S⁻¹M` is the canonical owner object `LocalizedModule S M`. -/
recall LocalizedModule

/- Companion recall: the canonical localization map `M → S⁻¹M` is the linear map
`LocalizedModule.mkLinearMap S M`. -/
recall LocalizedModule.mkLinearMap

/- Companion recall: the canonical owner instance expressing that `LocalizedModule S M` is the
localization of `M` with respect to `S` is `localizedModuleIsLocalizedModule`. -/
recall localizedModuleIsLocalizedModule

/- The canonical localization map sends `m` to the fraction `m / 1`. -/
recall LocalizedModule.mkLinearMap_apply

end

/-! ### Lemma_10_9_7 (from Chap10) -/
universe u v w

noncomputable section

section

open IsLocalizedModule LinearMap LocalizedModule

variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Lemma 10.9.7: if every element of `S` acts invertibly on `N`, then precomposition with the
canonical localization map `mkLinearMap S M : M →ₗ[R] LocalizedModule S M` is a linear
equivalence `Hom_R(LocalizedModule S M, N) ≃ Hom_R(M, N)`. This is the Hom-form of the owner
universal property `IsLocalizedModule.is_universal` for `mkLinearMap S M`. -/
noncomputable def localizedModuleHomLinearEquiv
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)) :
    (LocalizedModule S M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  LinearEquiv.ofBijective
    (lcomp R N (mkLinearMap S M))
    ⟨fun f _ hfg ↦
      (is_universal S (mkLinearMap S M) (f.comp (mkLinearMap S M)) hS).unique rfl hfg.symm,
      fun g ↦ (is_universal S (mkLinearMap S M) g hS).exists⟩

/-- Applying the Hom localization equivalence is precomposition with the canonical localization
map. -/
-- Proof sketch: unfold `localizedModuleHomLinearEquiv`; its underlying map is
-- `LinearMap.lcomp R N (mkLinearMap S M)`, whose value is composition with `mkLinearMap S M`.
theorem localizedModuleHomLinearEquiv_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (f : LocalizedModule S M →ₗ[R] N) :
    localizedModuleHomLinearEquiv S hS f = f.comp (mkLinearMap S M) := by
  -- Unfold the equivalence: its forward map is `LinearMap.lcomp`, so evaluation is composition.
  rfl

end

/-! ### Example_10_9_8 (from Chap10) -/
universe u

section AtPrime

variable {A : Type u} [CommRing A]

/- Example 10.9.8: the localization of a commutative ring `A` at a prime ideal `p` is the
canonical owner construction `Localization.AtPrime`. -/
recall Localization.AtPrime

end AtPrime

section ModuleAtPrime

variable {A : Type u} [CommRing A]

/- The localization of an `A`-module `M` at the prime ideal `p` is
the canonical owner construction `LocalizedModule.AtPrime`. -/
recall LocalizedModule.AtPrime

end ModuleAtPrime

section Away

variable {A : Type u} [CommRing A]

/- The localization of `A` with respect to the multiplicative set `{1, f, f^2, ...}` is
the canonical owner construction `Localization.Away`. -/
recall Localization.Away

/- The localization of an `A`-module `M` with respect to `{1, f, f^2, ...}` is
the canonical owner construction `LocalizedModule.Away`. -/
recall LocalizedModule.Away

/-- Localization away from `f` is the zero ring exactly when `f` is nilpotent. -/
-- Proof sketch: if `f` is nilpotent, then some power of `f` vanishes, so after inverting `f`
-- the localization collapses to the zero ring. Conversely, if `Localization.Away f` is
-- subsingleton, then `0 = 1` there; clearing denominators in that equality shows that a power of
-- `f` is zero in `A`.
theorem localization_away_subsingleton_iff (f : A) :
    Subsingleton (Localization.Away f) ↔ IsNilpotent f := by
  simpa [Localization.Away, isNilpotent_iff_zero_mem_powers] using
    (IsLocalization.subsingleton_iff :
      Subsingleton (Localization (Submonoid.powers f)) ↔ 0 ∈ Submonoid.powers f)

end Away

section FractionRing

variable {A : Type u} [CommRing A]

/- The total quotient ring of `A`, i.e. the localization at all non-zero-divisors, is
the canonical owner construction `FractionRing`. -/
recall FractionRing

section

variable [IsDomain A]

/- If `A` is a domain, then its total quotient ring is its field of fractions, expressed by the
canonical `IsFractionRing` instance on `FractionRing A`. -/
#check (inferInstance : IsFractionRing A (FractionRing A))

end

end FractionRing

/-! ### Lemma_10_9_9 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule

universe u v

noncomputable section

namespace Submonoid

variable {R : Type u} [CommMonoid R]

/-- The elements of a submonoid, viewed as a separate preorder by divisibility. -/
structure Divisibility (S : Submonoid R) where
  val : S

instance (S : Submonoid R) : CoeTC S.Divisibility S := ⟨Divisibility.val⟩

instance (S : Submonoid R) : CoeTC S.Divisibility R := ⟨fun f ↦ (f.val : R)⟩

instance (S : Submonoid R) : CoeTC S S.Divisibility := ⟨Divisibility.mk⟩

@[simp] theorem divisibility_val_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : S) = s := rfl

@[simp] theorem divisibility_coe_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : R) = s := rfl

instance divisibilityLE (S : Submonoid R) : LE S.Divisibility where
  le f g := (f : R) ∣ (g : R)

instance divisibilityPreorder (S : Submonoid R) : Preorder S.Divisibility where
  le := (· ≤ ·)
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans

end Submonoid

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- If `r` divides `x`, then scalar multiplication by `r` is invertible on `M_x`. -/
private theorem away_moduleEnd_isUnit_of_dvd
    (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away x M)) r) := by
  -- First move the unit statement to the ring localization away from `x`.
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  -- Then transport that unit along the scalar action on the localized module.
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (LocalizedModule.Away x M) :=
    Algebra.lsmul R R (LocalizedModule.Away x M)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Every element of `powers f` acts invertibly on `M_g` when `f ∣ g`. -/
private theorem away_moduleEnd_isUnit_of_mem_powers_of_dvd
    {f g : S.Divisibility} (h : f ≤ g) (x : Submonoid.powers (f : R)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away (g : R) M)) x) := by
  -- Reduce to the generator `f`, then take the appropriate power.
  rcases x with ⟨x, ⟨n, rfl⟩⟩
  simpa [map_pow] using
    (away_moduleEnd_isUnit_of_dvd (M := M) (g : R) (f : R) h).pow n

/-- Helper for Lemma 10.9.9: maps out of an away localization are determined by their restriction
to the original module, provided the relevant powers act invertibly on the codomain. -/
private theorem away_linearMap_ext
    {N : Type (max u v)} [AddCommGroup N] [Module R N] (f : S.Divisibility)
    (hN : ∀ x : Submonoid.powers (f : R), IsUnit (algebraMap R (Module.End R N) x))
    {g h : LocalizedModule.Away (f : R) M →ₗ[R] N}
    (hcomp :
      g.comp (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M) =
        h.comp (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)) :
    g = h := by
  -- Apply the localization uniqueness principle for maps out of `M_f`.
  exact IsLocalizedModule.ext
    (S := Submonoid.powers (f : R))
    (f := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
    (M'' := N) hN hcomp

/-- The canonical transition map `M_f → M_g` attached to a divisibility relation `f ≤ g`,
equivalently to a factorization `g = fr`. -/
private noncomputable def away_localization_map {f g : S.Divisibility} (h : f ≤ g) :
    LocalizedModule.Away (f : R) M →ₗ[R] LocalizedModule.Away (g : R) M :=
  LocalizedModule.lift (Submonoid.powers (f : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (g : R)) M)
    (fun x ↦ away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h x)

/-- Identity morphisms in the away-localization diagram act by the identity map. -/
-- Proof sketch: both sides are maps `M_f → M_f` that agree after precomposition with the canonical
-- localization map, so uniqueness in the universal property of `M_f` identifies them.
private theorem away_localization_diagram_map_id (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (𝟙 f))) =
      𝟙 (ModuleCat.of R (LocalizedModule.Away (f : R) M)) := by
  apply ModuleCat.hom_ext
  change away_localization_map S M (leOfHom (𝟙 f)) = LinearMap.id
  -- Both maps are determined by their restriction along the canonical map from `M`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using away_moduleEnd_isUnit_of_mem_powers_of_dvd
        (S := S) (M := M) (leOfHom (𝟙 f)) x)
    (N := LocalizedModule.Away (f : R) M)
    (g := away_localization_map S M (leOfHom (𝟙 f)))
    (h := LinearMap.id) <| by
      -- On generators, both sides are the canonical localization map `M → M_f`.
      simpa [away_localization_map] using
        (LocalizedModule.lift_comp (Submonoid.powers (f : R))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
          (fun x ↦ away_moduleEnd_isUnit_of_mem_powers_of_dvd
            (S := S) (M := M) (leOfHom (𝟙 f)) x)).trans
            (LinearMap.id_comp _).symm

/-- Composition in the away-localization diagram is given by composition of transition maps. -/
-- Proof sketch: both composites are the unique maps extending the same canonical map out of `M_f`,
-- so the universal property of localization gives the equality.
private theorem away_localization_diagram_map_comp
    {f g h : S.Divisibility} (h₁ : f ⟶ g) (h₂ : g ⟶ h) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (h₁ ≫ h₂))) =
      ModuleCat.ofHom (away_localization_map S M (leOfHom h₁)) ≫
        ModuleCat.ofHom (away_localization_map S M (leOfHom h₂)) := by
  apply ModuleCat.hom_ext
  change away_localization_map S M (leOfHom (h₁ ≫ h₂)) =
    (away_localization_map S M (leOfHom h₂)).comp (away_localization_map S M (leOfHom h₁))
  -- Again, it is enough to compare the two maps after precomposition with `M → M_f`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using away_moduleEnd_isUnit_of_mem_powers_of_dvd
        (S := S) (M := M) (leOfHom (h₁ ≫ h₂)) x)
    (N := LocalizedModule.Away (h : R) M)
    (g := away_localization_map S M (leOfHom (h₁ ≫ h₂)))
    (h := (away_localization_map S M (leOfHom h₂)).comp
      (away_localization_map S M (leOfHom h₁))) <| by
      -- Both composites extend the same canonical map `M → M_h`.
      rw [away_localization_map, LinearMap.comp_assoc, away_localization_map, away_localization_map]
      rw [LocalizedModule.lift_comp, LocalizedModule.lift_comp, LocalizedModule.lift_comp]

/-- The diagram `f ↦ M_f` indexed by the divisibility preorder on `S`, where `f ≤ g` means
`f ∣ g`, equivalently `g = fr` for some `r : R`. -/
noncomputable def away_localization_diagram : S.Divisibility ⥤ ModuleCat R :=
  { obj := fun f ↦ ModuleCat.of R (LocalizedModule.Away (f : R) M)
    map := fun {_ _} h ↦
      ModuleCat.ofHom (away_localization_map S M (leOfHom h))
    map_id := fun f ↦ away_localization_diagram_map_id S M f
    map_comp := fun h₁ h₂ ↦ away_localization_diagram_map_comp S M h₁ h₂ }

/-- The canonical map from the away localization `M_f` to the full localization `S⁻¹M`. -/
private noncomputable abbrev away_localization_to_localizedModule (f : S.Divisibility) :
    LocalizedModule.Away (f : R) M →ₗ[R] LocalizedModule S M :=
  LocalizedModule.liftOfLE (Submonoid.powers (f : R)) S
    (Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))

/-- The maps `M_f → S⁻¹M` are compatible with the transition maps of the away-localization diagram. -/
-- Proof sketch: both sides are maps `M_f → S⁻¹M` extending the same map from `M`, so the universal
-- property of `M_f` forces them to agree.
@[reassoc]
private theorem away_localization_to_total_naturality {f g : S.Divisibility} (h : f ⟶ g) :
    (away_localization_diagram S M).map h ≫
        ModuleCat.ofHom (away_localization_to_localizedModule S M g) =
      ModuleCat.ofHom (away_localization_to_localizedModule S M f) := by
  apply ModuleCat.hom_ext
  change (away_localization_to_localizedModule S M g).comp
      (away_localization_map S M (leOfHom h)) =
    away_localization_to_localizedModule S M f
  -- Compare the two maps `M_f → S⁻¹M` on the dense image of `M`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using IsLocalizedModule.map_units
        (S := S)
        (f := LocalizedModule.mkLinearMap S M)
        ⟨x.1, Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) x.2⟩)
    (N := LocalizedModule S M)
    (g := (away_localization_to_localizedModule S M g).comp
      (away_localization_map S M (leOfHom h)))
    (h := away_localization_to_localizedModule S M f) <| by
      -- Both maps restrict to the same canonical localization map from `M`.
      rw [LinearMap.comp_assoc, away_localization_map, LocalizedModule.lift_comp]
      rw [away_localization_to_localizedModule]
      erw [IsLocalizedModule.liftOfLE_comp]
      rw [away_localization_to_localizedModule]
      erw [IsLocalizedModule.liftOfLE_comp]

/-- The cocone on the diagram `f ↦ M_f` with vertex the full localization `S⁻¹M`. -/
noncomputable def away_localization_cocone :
    Cocone (away_localization_diagram S M) where
  pt := ModuleCat.of R (LocalizedModule S M)
  ι :=
    { app := fun f ↦ ModuleCat.ofHom (away_localization_to_localizedModule S M f)
      naturality := fun _ _ h ↦ away_localization_to_total_naturality S M h }

/-- Helper for Lemma 10.9.9: the transition map along a divisibility relation sends the basic
generator `m / f` to the transported basic generator `(r • m) / g` whenever `g = fr`. -/
private theorem away_localization_map_mk_pow_one
    {f g : S.Divisibility} (h : f ≤ g) {r : R} (hr : (g : R) = (f : R) * r) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) =
      LocalizedModule.mk (r • m) (Submonoid.pow (g : R) 1) := by
  -- Evaluate the localization lift on the basic generator `m / f`.
  rw [away_localization_map, LocalizedModule.lift_mk]
  -- Identify the inverse action with the expected transported fraction.
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff
    (R := R)
    (S := R)
    (M := LocalizedModule.Away (g : R) M)
    (x := (((Submonoid.pow (f : R) 1 : Submonoid.powers (f : R)) : R)))
    (away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h
      (Submonoid.pow (f : R) 1))
    _ _).2
  -- Multiplying by `f` turns the target fraction back into `m / 1`.
  simp only [LocalizedModule.mkLinearMap_apply]
  rw [hr]
  simpa [LocalizedModule.smul'_mk, Submonoid.smul_def, mul_smul] using
    (LocalizedModule.mk_cancel (s := Submonoid.pow ((f : R) * r) 1) (m := m)).symm

/-- Helper for Lemma 10.9.9: cocone naturality transports the basic generator `m / f` to the
basic generator `(r • m) / g` in the target component whenever `g = fr`. -/
private theorem cocone_app_mk_pow_one_transport
    (c : Cocone (away_localization_diagram S M)) {f g : S.Divisibility} (h : f ≤ g)
    {r : R} (hr : (g : R) = (f : R) * r) (m : M) :
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) =
      c.ι.app g (LocalizedModule.mk (r • m) (Submonoid.pow (g : R) 1)) := by
  -- Move along the cocone edge, then rewrite the diagram map on the basic generator.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (Submonoid.pow (f : R) 1))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) 1))) =
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) at hw
  rw [away_localization_map_mk_pow_one (S := S) (M := M) h hr] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: transition maps preserve fractions whose denominator is `1`. -/
private theorem away_localization_map_mk_one
    {f g : S.Divisibility} (h : f ≤ g) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
      LocalizedModule.mk m (1 : Submonoid.powers (g : R)) := by
  -- Evaluate the localization lift on the generator `m / 1`.
  rw [away_localization_map, LocalizedModule.lift_mk_one]
  rfl

/-- Helper for Lemma 10.9.9: cocone naturality transports fractions with denominator `1`. -/
private theorem cocone_app_mk_one_transport
    (c : Cocone (away_localization_diagram S M)) {f g : S.Divisibility} (h : f ≤ g) (m : M) :
    c.ι.app f (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
      c.ι.app g (LocalizedModule.mk m (1 : Submonoid.powers (g : R))) := by
  -- Move along the cocone edge, then rewrite the diagram map on the denominator-`1` fraction.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (1 : Submonoid.powers (f : R)))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (1 : Submonoid.powers (f : R)))) =
    c.ι.app f (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) at hw
  rw [away_localization_map_mk_one (S := S) (M := M) h] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: if the target index is the actual denominator `f^(n+1)`, then the
transition map sends `m / f^(n+1)` to the basic generator `m / g`. -/
private theorem away_localization_map_mk_power_denominator
    {f : S.Divisibility} {g : S} (h : f ≤ (g : S.Divisibility))
    {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
      LocalizedModule.mk m (Submonoid.pow (g : R) 1) := by
  -- Evaluate the localization lift on `m / f^(n+1)` and cancel the matching denominator `g`.
  rw [away_localization_map, LocalizedModule.lift_mk]
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff
    (R := R)
    (S := R)
    (M := LocalizedModule.Away (g : R) M)
    (x := (((Submonoid.pow (f : R) (n + 1) : Submonoid.powers (f : R)) : R)))
    (away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h
      (Submonoid.pow (f : R) (n + 1)))
    _ _).2
  simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
  convert (LocalizedModule.mk_cancel (s := Submonoid.pow (g : R) 1) (m := m)).symm using 1
  simp [Submonoid.smul_def, hg]

/-- Helper for Lemma 10.9.9: cocone naturality transports `m / f^(n+1)` to the matching basic
generator in the denominator component. -/
private theorem cocone_app_mk_power_denominator_transport
    (c : Cocone (away_localization_diagram S M)) {f : S.Divisibility} {g : S}
    (h : f ≤ (g : S.Divisibility)) {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
      c.ι.app g (LocalizedModule.mk m (Submonoid.pow (g : R) 1)) := by
  -- Move along the cocone edge, then rewrite the diagram map on the chosen denominator.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))) =
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) at hw
  rw [away_localization_map_mk_power_denominator (S := S) (M := M) h hg] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: fractions in `M_f` with the same denominator `f` add by adding their
numerators. -/
private theorem away_mk_pow_one_add (f : S.Divisibility) (m₁ m₂ : M) :
    LocalizedModule.mk (m₁ + m₂) (Submonoid.pow (f : R) 1) =
      LocalizedModule.mk m₁ (Submonoid.pow (f : R) 1) +
        LocalizedModule.mk m₂ (Submonoid.pow (f : R) 1) := by
  -- Reuse the standard same-denominator addition formula for localized modules.
  simpa [IsLocalizedModule.mk_eq_mk'] using
    (IsLocalizedModule.mk'_add
      (S := Submonoid.powers (f : R))
      (f := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      m₁ m₂ (Submonoid.pow (f : R) 1))

/-- Equivalent representatives in the localization define the same cocone evaluation. -/
private theorem localized_module_desc_wd (c : Cocone (away_localization_diagram S M))
    (p p' : M × S) (h : p ≈ p') :
    c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)) =
      c.ι.app p'.2 (LocalizedModule.mk p'.1 (Submonoid.pow (p'.2 : R) 1)) := by
  -- Route correction: transport both representatives to one common away-localization component.
  rcases h with ⟨u, hu⟩
  let q : S.Divisibility := (p.2 * p'.2 * u : S)
  have hpq : (p.2 : R) ∣ (q : R) := by
    refine ⟨((p'.2 * u : S) : R), ?_⟩
    simpa [q, mul_assoc]
  have hp'q : (p'.2 : R) ∣ (q : R) := by
    refine ⟨((p.2 * u : S) : R), ?_⟩
    simpa [q, mul_assoc, mul_left_comm, mul_comm]
  -- Cocone naturality identifies both sides with basic generators in the `q`-component.
  rw [cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := p.2) (g := q) hpq
      (r := ((p'.2 * u : S) : R))
      (by simpa [q, mul_assoc]),
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := p'.2) (g := q) hp'q
      (r := ((p.2 * u : S) : R))
      (by simp [q, mul_left_comm, mul_comm])]
  -- The original localization relation is exactly the equality of transported numerators.
  exact congrArg
    (fun x ↦ c.ι.app q (LocalizedModule.mk x (Submonoid.pow (q : R) 1)))
    (by simpa [Submonoid.smul_def, mul_smul, mul_assoc, mul_left_comm, mul_comm] using hu)

/-- The universal map from the total localization to the vertex of a cocone on the away
localization diagram, defined on a fraction `m / s` by evaluating the `s`-component of the cocone
on the corresponding element of `M_s`. -/
private noncomputable def localized_module_desc_fun (c : Cocone (away_localization_diagram S M)) :
    LocalizedModule S M → c.pt :=
  fun x ↦
    x.liftOn
      (fun p ↦ c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)))
      (localized_module_desc_wd S M c)

@[simp]
private theorem localized_module_desc_fun_mk (c : Cocone (away_localization_diagram S M))
    (m : M) (s : S) :
    localized_module_desc_fun S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := by
  -- Evaluate the quotient-descended function on the canonical representative `(m, s)`.
  simp [localized_module_desc_fun, LocalizedModule.liftOn_mk]

/-- The cocone-descending map out of `S⁻¹M` preserves addition. -/
private theorem localized_module_desc_fun_map_add
    (c : Cocone (away_localization_diagram S M)) (x y : LocalizedModule S M) :
    localized_module_desc_fun S M c (x + y) =
      localized_module_desc_fun S M c x + localized_module_desc_fun S M c y := by
  -- Reduce to two explicit fractions and transport them to the common component `M_(ss')`.
  refine LocalizedModule.induction_on₂ ?_ x y
  intro m m' s s'
  let q : S.Divisibility := (s * s' : S)
  have hsq : (s : R) ∣ (q : R) := by
    refine ⟨(s' : R), ?_⟩
    simpa [q]
  have hs'q : (s' : R) ∣ (q : R) := by
    refine ⟨(s : R), ?_⟩
    simpa [q, mul_comm]
  have hs :
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) =
        c.ι.app q (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) :=
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := s) (g := q) hsq
      (r := (s' : R)) (by simpa [q]) m
  have hs' :
      c.ι.app s' (LocalizedModule.mk m' (Submonoid.pow (s' : R) 1)) =
        c.ι.app q (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) :=
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := s') (g := q) hs'q
      (r := (s : R)) (by simpa [q, mul_comm]) m'
  rw [LocalizedModule.mk_add_mk, localized_module_desc_fun_mk, localized_module_desc_fun_mk,
    localized_module_desc_fun_mk]
  -- Once both summands live in the same away localization, additivity is ordinary linearity.
  let z1 : ↥c.pt := c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1))
  let z2 : ↥c.pt := c.ι.app s' (LocalizedModule.mk m' (Submonoid.pow (s' : R) 1))
  have hsum :
      c.ι.app q (LocalizedModule.mk ((s' : R) • m + (s : R) • m')
        (Submonoid.pow (q : R) 1)) = z1 + z2 := by
    calc
      c.ι.app q (LocalizedModule.mk ((s' : R) • m + (s : R) • m')
          (Submonoid.pow (q : R) 1)) =
        ModuleCat.Hom.hom (c.ι.app q)
          (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) +
            ModuleCat.Hom.hom (c.ι.app q)
              (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) := by
          rw [away_mk_pow_one_add (S := S) (M := M) q]
          exact (ModuleCat.Hom.hom (c.ι.app q)).map_add
            (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1))
            (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1))
      _ = (ConcreteCategory.hom (c.ι.app q))
            (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) +
          (ConcreteCategory.hom (c.ι.app q))
            (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) := by
          rfl
      _ = z1 + z2 := by
        rw [← hs, ← hs']
        change z1 + z2 = z1 + z2
        rfl
  simpa [q, z1, z2] using hsum

/-- The cocone-descending map out of `S⁻¹M` preserves scalar multiplication. -/
private theorem localized_module_desc_fun_map_smul
    (c : Cocone (away_localization_diagram S M)) (r : R) (x : LocalizedModule S M) :
    localized_module_desc_fun S M c (r • x) =
      r • localized_module_desc_fun S M c x := by
  -- Reduce to one fraction and use linearity in the chosen cocone component.
  refine LocalizedModule.induction_on ?_ x
  intro m s
  rw [LocalizedModule.smul'_mk, localized_module_desc_fun_mk, localized_module_desc_fun_mk]
  simpa [LocalizedModule.smul'_mk] using
    map_smul (ConcreteCategory.hom (c.ι.app s)) r
      (LocalizedModule.mk m (Submonoid.pow (s : R) 1))

/-- The universal morphism from the total localization cocone to an arbitrary cocone on the away
localization diagram. -/
private noncomputable def localized_module_desc (c : Cocone (away_localization_diagram S M)) :
    LocalizedModule S M →ₗ[R] c.pt where
  toFun := localized_module_desc_fun S M c
  map_add' := localized_module_desc_fun_map_add S M c
  map_smul' := localized_module_desc_fun_map_smul S M c

@[simp]
private theorem localized_module_desc_mk (c : Cocone (away_localization_diagram S M))
    (m : M) (s : S) :
    localized_module_desc S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := by
  -- The linear desc map agrees with its underlying function on generators.
  simpa [localized_module_desc] using localized_module_desc_fun_mk (S := S) (M := M) c m s

/-- Helper for Lemma 10.9.9: the canonical map `M_f → S⁻¹M` preserves denominator-`1` fractions. -/
private theorem away_localization_to_localizedModule_mk_one
    (f : S.Divisibility) (m : M) :
    away_localization_to_localizedModule S M f
      (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
    LocalizedModule.mk m (1 : S) := by
  -- Route correction: compute the total-localization map directly on the image of `m : M`.
  change
    IsLocalizedModule.liftOfLE
        (Submonoid.powers (f : R)) S
        (Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
        (LocalizedModule.mkLinearMap S M)
        ((LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M) m) =
      LocalizedModule.mk m (1 : S)
  -- The universal property says that `liftOfLE` agrees with the canonical map on `M`.
  simpa [LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.liftOfLE_apply
      (S₁ := Submonoid.powers (f : R))
      (S₂ := S)
      (h := Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
      (f₁ := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      (f₂ := LocalizedModule.mkLinearMap S M) m)

/-- Helper for Lemma 10.9.9: the canonical map `M_f → S⁻¹M` sends `m / f^(n+1)` to the total
localization fraction with the same denominator index `g = f^(n+1)`. -/
private theorem away_localization_to_localizedModule_mk_power_denominator
    {f : S.Divisibility} {g : S} {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    away_localization_to_localizedModule S M f
      (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
    LocalizedModule.mk m g := by
  -- Rewrite both sides into the `mk'` normal form expected by `liftOfLE_mk'`.
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  -- The lift preserves the numerator and embeds the denominator into `S`.
  let g' : S :=
    ⟨(f : R) ^ (n + 1),
      Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) ⟨n + 1, rfl⟩⟩
  have hg' : g' = g := Subtype.ext <| by simpa [g'] using hg.symm
  -- After identifying the embedded denominator with `g`, the computation is immediate.
  rw [← hg']
  simpa [away_localization_to_localizedModule, g'] using
    (IsLocalizedModule.liftOfLE_mk'
      (S₁ := Submonoid.powers (f : R))
      (S₂ := S)
      (h := Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
      (f₁ := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      (f₂ := LocalizedModule.mkLinearMap S M)
      m (Submonoid.pow (f : R) (n + 1)))

/-- The universal map from `S⁻¹M` to a cocone vertex factors the canonical cocone maps. -/
private theorem localized_module_desc_fac
    (c : Cocone (away_localization_diagram S M)) (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_to_localizedModule S M f) ≫
        ModuleCat.ofHom (localized_module_desc S M c) =
      c.ι.app f := by
  apply ModuleCat.hom_ext
  ext x
  -- Route correction: once the total-localization map is computed on generators, factorization is
  -- a denominator split inside `M_f`.
  refine LocalizedModule.induction_on ?_ x
  intro m s
  rcases s.2 with ⟨n, hn⟩
  have hs : s = Submonoid.pow (f : R) n := by
    apply Subtype.ext
    simpa [hn]
  subst s
  cases n with
  | zero =>
      -- The denominator-`1` branch lands in the `1`-component of the cocone.
      change
        localized_module_desc S M c
            (away_localization_to_localizedModule S M f
              (LocalizedModule.mk m (Submonoid.pow (f : R) 0))) =
          c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 0))
      rw [show Submonoid.pow (f : R) 0 = (1 : Submonoid.powers (f : R)) by
        ext
        simp]
      rw [away_localization_to_localizedModule_mk_one, localized_module_desc_mk]
      rw [show Submonoid.pow ((1 : S) : R) 1 = (1 : Submonoid.powers ((1 : S) : R)) by
        ext
        simp]
      simpa using
        (cocone_app_mk_one_transport (S := S) (M := M) (c := c)
          (f := (1 : S)) (g := f) (show (1 : R) ∣ (f : R) from one_dvd _) m)
  | succ n =>
      -- For a positive power denominator, choose the actual denominator component in `S`.
      let g : S :=
        ⟨(f : R) ^ (n + 1),
          Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) ⟨n + 1, rfl⟩⟩
      have hg : (g : R) = (f : R) ^ (n + 1) := rfl
      have hfg : f ≤ (g : S.Divisibility) := by
        refine ⟨(f : R) ^ n, ?_⟩
        simp [g, pow_succ, mul_comm]
      change
        localized_module_desc S M c
            (away_localization_to_localizedModule S M f
              (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))) =
          c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))
      rw [away_localization_to_localizedModule_mk_power_denominator (S := S) (M := M)
          (f := f) (g := g) (n := n) hg, localized_module_desc_mk]
      simpa [g] using
        (cocone_app_mk_power_denominator_transport (S := S) (M := M) (c := c)
          (f := f) (g := g) hfg (n := n) hg m).symm

/-- Any cocone on the away-localization diagram receives a unique morphism from the canonical
localization cocone. -/
private theorem away_localization_cocone_existsUnique_desc
    (c : Cocone (away_localization_diagram S M)) :
    ∃! t : (away_localization_cocone S M).pt ⟶ c.pt,
      ∀ f : S.Divisibility, (away_localization_cocone S M).ι.app f ≫ t = c.ι.app f := by
  refine ⟨ModuleCat.ofHom (localized_module_desc S M c), ?_, ?_⟩
  · -- The descended map is compatible with every cocone leg by the factorization lemma.
    exact localized_module_desc_fac (S := S) (M := M) c
  · intro t ht
    apply ModuleCat.hom_ext
    ext x
    -- The full localization is generated by basic fractions `m / s`.
    refine LocalizedModule.induction_on ?_ x
    intro m s
    have hs := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (ht s))
      (LocalizedModule.mk m (Submonoid.pow (s : R) 1))
    change
      t
          (away_localization_to_localizedModule S M s
            (LocalizedModule.mk m (Submonoid.pow (s : R) 1))) =
        c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) at hs
    rw [away_localization_to_localizedModule_mk_power_denominator
      (S := S) (M := M) (f := s) (g := s) (n := 0) (by simp)] at hs
    simpa [localized_module_desc_mk] using hs

/-- Lemma 10.9.9: the localization `LocalizedModule S M` is the colimit of the diagram
`f ↦ LocalizedModule.Away f M` indexed by `S`, where `f ≤ g` means `g = fr` for some `r : R` and
the transition map is the canonical map sending `m / f^n` to `r^n m / g^n`. -/
noncomputable def localized_module_is_colimit_away_localization_diagram :
    IsColimit (away_localization_cocone S M) :=
  IsColimit.ofExistsUnique (away_localization_cocone_existsUnique_desc S M)

/-- The universal morphism from the canonical localization cocone restricts to the given cocone
on each away localization. -/
-- Proof sketch: this is the `fac` field of
-- `localized_module_is_colimit_away_localization_diagram`.
@[reassoc, simp]
theorem localized_module_is_colimit_away_localization_diagram_fac
    (s : Cocone (away_localization_diagram S M)) (f : S.Divisibility) :
    (away_localization_cocone S M).ι.app f ≫
      (localized_module_is_colimit_away_localization_diagram S M).desc s =
        s.ι.app f := by
  -- This is the `fac` field of the colimit structure just constructed.
  simpa using (localized_module_is_colimit_away_localization_diagram S M).fac s f

end

/-! ### Proposition_10_9_10 (from Chap10) -/
noncomputable section

open IsLocalization

universe u

variable {A : Type u} [CommRing A]
variable (S S' : Submonoid A)

local notation "Sbar" => Algebra.algebraMapSubmonoid (Localization S') S
local notation "SSupBar" => Algebra.algebraMapSubmonoid (Localization S') (S ⊔ S')
local notation "SSup" => Localization (S ⊔ S')

local instance : Algebra (Localization S') SSup :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization S')
    SSup
    S'
    (S ⊔ S')
    le_sup_right

local instance : IsScalarTower A (Localization S') SSup :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization S')
    SSup
    S'
    (S ⊔ S')
    le_sup_right

local instance : IsLocalization SSupBar SSup :=
  IsLocalization.isLocalization_of_submonoid_le
    (Localization S')
    SSup
    S'
    (S ⊔ S')
    le_sup_right

private theorem sbar_le_sSupBar : Sbar ≤ SSupBar := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, (show S ≤ S ⊔ S' from le_sup_left) hs, rfl⟩

private theorem exists_sbar_dvd_of_mem_sSupBar (x : Localization S') (hx : x ∈ SSupBar) :
    ∃ m ∈ Sbar, x ∣ m := by
  rcases hx with ⟨a, ha, rfl⟩
  rcases Submonoid.mem_sup.mp ha with ⟨s, hs, z, hz, rfl⟩
  refine ⟨algebraMap A (Localization S') s, ⟨s, hs, rfl⟩, ?_⟩
  refine ⟨↑(IsLocalization.map_units (Localization S') ⟨z, hz⟩).unit⁻¹, ?_⟩
  simp [map_mul, mul_comm, mul_assoc]

local instance : IsLocalization Sbar SSup :=
  (IsLocalization.iff_of_le_of_exists_dvd Sbar SSupBar
    (sbar_le_sSupBar S S')
    (exists_sbar_dvd_of_mem_sSupBar S S')).2 inferInstance

/-
Proposition 10.9.10: localizing `A` at the submonoid generated by `S` and `S'` is canonically
isomorphic to localizing `Localization S'` at the image of `S`. This is exactly the canonical
localization equivalence `Localization.algEquiv`, viewed as an `A`-algebra equivalence by
restricting scalars.
-/
#check
  (((Localization.algEquiv Sbar SSup).symm).restrictScalars A :
    SSup ≃ₐ[A] Localization Sbar)

end

/-! ### Proposition_10_9_11 (from Chap10) -/
universe u v

noncomputable section

section

open IsLocalizedModule LocalizedModule

variable {A : Type u} [CommRing A]
variable (S S' : Submonoid A)
variable (M : Type v) [AddCommGroup M] [Module A M]

/- Proposition 10.9.11: viewing `S'⁻¹M` as an `A`-module, localizing it again at `S` is
canonically isomorphic to localizing `M` at the submonoid `S ⊔ S'`, which is the Lean realization
of the textbook multiplicative set `SS'`. This is exactly the specialized canonical equivalence
`IsLocalizedModule.linearEquiv` attached to the two localization maps. -/
#check
  (linearEquiv (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M) (mkLinearMap (S ⊔ S') M) :
    LocalizedModule S (LocalizedModule S' M) ≃ₗ[A] LocalizedModule (S ⊔ S') M)

/- Companion recall: the inverse comparison map carries the iterated localization map `M →
S⁻¹(S'⁻¹M)` back to the direct localization map `M → (S ⊔ S')⁻¹M`. This is the owner theorem
`IsLocalizedModule.iso_symm_comp` specialized to the iterated-localization map. -/
#check
  (iso_symm_comp (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M) :
    (iso (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M)).symm.toLinearMap.comp
        (iteratedLocalizedModuleMkLinearMap S S' M) =
      mkLinearMap (S ⊔ S') M)

end

/-! ### Proposition_10_9_12 (from Chap10) -/
/- Proposition 10.9.12: if `L ⟶ M ⟶ N` is an exact sequence of `R`-modules, then the induced
sequence `LocalizedModule S L ⟶ LocalizedModule S M ⟶ LocalizedModule S N` is exact. This is
exactly the canonical theorem `LocalizedModule.map_exact`. -/
recall LocalizedModule.map_exact

/-! ### Lemma_10_9_13 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (N : Submodule R M)

/- Layering for this item:
* source-facing statement: localization respects quotients.
* core/canonical owner: `localizedQuotientEquiv`.
* bridge/view: its symmetric form gives the textbook orientation.
-/

/- Lemma 10.9.13: localization respects quotients. Mathlib's canonical comparison is
`localizedQuotientEquiv S N`, which identifies the quotient of the localized module by the
localized submodule with the localization of the quotient. -/
recall localizedQuotientEquiv

/- Companion check: the textbook-oriented equivalence
`S⁻¹ (M ⧸ N) ≃ (S⁻¹ M) ⧸ S⁻¹ N` is the inverse of the canonical library comparison. -/
#check (localizedQuotientEquiv S N).symm

end

/-! ### Proposition_10_9_14 (from Chap10) -/
universe u

section

variable {A : Type u} [CommRing A]
variable (S : Submonoid A) (I : Ideal A)

local notation "Sbar" => Algebra.algebraMapSubmonoid (A ⧸ I) S
local notation "IS" => Ideal.map (algebraMap A (Localization S)) I

/- Proposition 10.9.14: the quotient of `Localization S` by the localized ideal
`IS` is canonically isomorphic to the localization of `A ⧸ I` at the image `Sbar` of `S`.
This is exactly the specialization of the owner equivalence `Localization.algEquiv` to the
quotient ring `Localization S ⧸ IS`. -/
#check
  (Localization.algEquiv Sbar (Localization S ⧸ IS) :
    Localization Sbar ≃ₐ[A ⧸ I] Localization S ⧸ IS)

end

/-! ### Lemma_10_9_15 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule

/- Lemma 10.9.15: for the canonical localization map `M → S⁻¹M`, every submodule of `S⁻¹M`
is the localization of its inverse image in `M`. This is exactly the `l_u_eq` theorem of the
owner Galois insertion `localized'gi` for submodule localization. -/
#check (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).l_u_eq

end

/-! ### Lemma_10_9_16 (from Chap10) -/
universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.16: every ideal `I'` of `Localization S` is the localization of its inverse image
in `A`, namely
`Ideal.map (algebraMap A (Localization S)) (Ideal.comap (algebraMap A (Localization S)) I') = I'`.
This is exactly the canonical theorem `IsLocalization.map_comap` specialized to ideals of
`Localization S`. -/
#check (IsLocalization.map_comap S (Localization S))

end
