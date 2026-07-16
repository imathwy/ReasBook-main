import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_2
import stacks_proof.stacks_project.Chap10.Lemma_10_154_7
import stacks_proof.stacks_project.Chap10.Lemma_10_155_1

open CategoryTheory MorphismProperty
open IsLocalRing

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {Rh : Type u} {Sh : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh] [IsScalarTower R S Sh]
variable [IsHenselizationOf S Sh]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and their functoriality under local
  ring maps;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsHenselizationOf.residueFieldEquiv`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `IsLocalRing.local_hom_TFAE`;
- best owner abstraction: this file is a `bridge/view` specialization of the Chapter 10 owner
  theorem `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  with the henselization owners providing the primitive ind-étale and residue-field data;
- primitive data: the local base map `R → S` and the owner hypotheses
  `IsHenselizationOf R Rh`, `IsHenselizationOf S Sh`;
- derived API: the canonical comparison map `Rh →ₐ[R] Sh` and its locality.

Source/core/bridge triage:
- `source-facing`: the uniqueness statement for the comparison map between henselizations;
- `core/canonical`: `IsHenselizationOf`, `IsHenselizationOf.residueFieldEquiv`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the induced comparison `henselizationMap`.
-/
-- Proof sketch: apply the universal property of the henselization `Rh` from Lemma `10.154.6` with
-- target `Sh`, using that `Sh` is henselian local by `IsHenselizationOf S Sh`. The required
-- residue-field map is the composite `ResidueField Rh ≃ ResidueField R → ResidueField S ≃
-- ResidueField Sh`, where the two equivalences come from the henselization structures and the
-- middle map comes from the given local homomorphism `R → S`. The uniqueness part of
-- `Lemma 10.154.6` then gives uniqueness of the local `R`-algebra map.

namespace HenselianLocalRing

/-- Helper for Chap10 Lemma 10 155 6: henselian local rings transport across ring
equivalences, even when the two carriers live in different universes. -/
lemma of_ringEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [HenselianLocalRing A] (e : A ≃+* B) : HenselianLocalRing B := by
  letI : IsLocalRing B := e.isLocalRing
  have hA := ((HenselianLocalRing.TFAE A).out 0 2).mp
    (show HenselianLocalRing A from inferInstance)
  -- Proof comment: use the simple-root lifting clause of the henselian TFAE. When the target
  -- residue field is larger than the source universe, shrink it using the surjection from `A`.
  refine ((HenselianLocalRing.TFAE B).out 2 0).mp ?_
  intro K _ φ hφ f hf a₀ hroot hderiv
  have hφe : Function.Surjective (φ.comp (e : A →+* B)) := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨e.symm x, by simp⟩
  letI : Small.{u} K := small_of_surjective hφe
  let κe : K ≃+* Shrink.{u} K := (Shrink.ringEquiv K).symm
  let ψ : A →+* Shrink.{u} K := κe.toRingHom.comp (φ.comp (e : A →+* B))
  have hψ : Function.Surjective ψ := by
    -- Proof comment: shrink-equivalence preserves the surjectivity of the pulled-back field map.
    intro y
    obtain ⟨x, hx⟩ := hφe (κe.symm y)
    refine ⟨x, ?_⟩
    simpa [ψ, κe, RingHom.comp_apply] using congrArg κe hx
  let g : Polynomial A := f.map (e.symm : B →+* A)
  have hcomp : ((φ.comp (e : A →+* B)).comp (e.symm : B →+* A)) = φ := by
    ext x
    simp
  have hg_monic : g.Monic := hf.map (e.symm : B →+* A)
  have hg_root : g.eval₂ ψ (κe a₀) = 0 := by
    -- Proof comment: evaluation commutes with the shrink equivalence, reducing the root
    -- condition to the original one over `B`.
    rw [show g = f.map (e.symm : B →+* A) by rfl, Polynomial.eval₂_map]
    have hpoly := (Polynomial.hom_eval₂ f φ κe.toRingHom a₀).symm
    rw [hroot] at hpoly
    simpa [ψ, RingHom.comp_assoc, hcomp] using hpoly
  have hg_deriv :
      g.derivative.eval₂ ψ (κe a₀) = κe (f.derivative.eval₂ φ a₀) := by
    -- Proof comment: the same compatibility applies after differentiating the polynomial.
    rw [show g = f.map (e.symm : B →+* A) by rfl, Polynomial.derivative_map,
      Polynomial.eval₂_map]
    have hpoly := (Polynomial.hom_eval₂ f.derivative φ κe.toRingHom a₀).symm
    simpa [ψ, RingHom.comp_assoc, hcomp] using hpoly
  have hg_simple : g.derivative.eval₂ ψ (κe a₀) ≠ 0 := by
    intro hz
    apply hderiv
    apply κe.injective
    simpa [hg_deriv] using hz
  obtain ⟨a, ha_root, ha_map⟩ :=
    hA ψ hψ g hg_monic (κe a₀) hg_root hg_simple
  refine ⟨e a, ?_, ?_⟩
  · -- Proof comment: apply the inverse equivalence to reduce the root equation to the source
    -- henselian lifting result.
    have ha_eval₂ : Polynomial.eval₂ (e.symm : B →+* A) a f = 0 := by
      simpa [g, Polynomial.IsRoot, Polynomial.eval_map] using ha_root
    exact
      Polynomial.isRoot_of_eval₂_map_eq_zero
        (p := f) (f := (e.symm : B →+* A)) e.symm.injective
        (by simpa using ha_eval₂)
  · -- Proof comment: the residue-field point condition is exactly the transported source
    -- condition.
    apply κe.injective
    simpa [ψ, κe, RingHom.comp_apply] using ha_map

end HenselianLocalRing

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: uniqueness of local algebra maps to a lifted target
descends along `ULift.algEquiv`. -/
lemma existsUnique_algHom_localHom_of_uliftTarget
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra R B]
    (h : ∃! g : A →ₐ[R] ULift.{u, v} B, IsLocalHom (g : A →+* ULift.{u, v} B)) :
    ∃! f : A →ₐ[R] B, IsLocalHom (f : A →+* B) := by
  letI : IsLocalRing (ULift.{u, v} B) :=
    RingEquiv.isLocalRing (ULift.ringEquiv.symm : B ≃+* ULift.{u, v} B)
  let e : ULift.{u, v} B ≃ₐ[R] B := ULift.algEquiv (R := R) (A := B)
  obtain ⟨g, hg, huniq⟩ := h
  let f : A →ₐ[R] B := e.toAlgHom.comp g
  have heLocal : IsLocalHom (e.toRingEquiv.toRingHom : ULift.{u, v} B →+* B) :=
    Function.Surjective.isLocalHom _ e.toRingEquiv.surjective
  have hf : IsLocalHom (f : A →+* B) := by
    -- Proof comment: compose the lifted local map with the local equivalence down to `B`.
    exact RingHom.isLocalHom_comp e.toRingEquiv.toRingHom (g : A →+* ULift.{u, v} B)
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  have heSymmLocal :
      IsLocalHom (e.symm.toRingEquiv.toRingHom : B →+* ULift.{u, v} B) :=
    Function.Surjective.isLocalHom _ e.symm.toRingEquiv.surjective
  have hg' : IsLocalHom ((e.symm.toAlgHom.comp f') : A →+* ULift.{u, v} B) := by
    -- Proof comment: lift the competing local map to the `ULift` target, where uniqueness is
    -- available.
    exact RingHom.isLocalHom_comp e.symm.toRingEquiv.toRingHom (f' : A →+* B)
  have hgeq : e.symm.toAlgHom.comp f' = g := huniq (e.symm.toAlgHom.comp f') hg'
  -- Proof comment: descend the equality of lifted maps by applying the algebra equivalence.
  apply AlgHom.ext
  intro x
  have hx := congrFun (congrArg DFunLike.coe hgeq) x
  have hx' := congrArg e hx
  simpa [f, AlgHom.comp_apply, e] using hx'

/-- Helper for Chap10 Lemma 10 155 6: the canonical map from the residue field of a
local ring to itself is bijective. -/
lemma residueField_lift_residue_bijective
    (A : Type w) [CommRing A] [IsLocalRing A] :
    Function.Bijective (ResidueField.lift (residue A)) := by
  -- Proof comment: the lift agrees with the identity after precomposing with the surjective
  -- residue map, so it is the identity on the residue field.
  have h_id :
      ResidueField.lift (residue A) =
        RingHom.id (ResidueField A) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    simp
  rw [h_id]
  exact Function.bijective_id

/-- Helper for Chap10 Lemma 10 155 6: residue-field compatibility with a field map forces a
ring homomorphism of local rings to be local. -/
lemma isLocalHom_of_residue_comp_eq
    {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (φ : ResidueField A →+* ResidueField B)
    (h :
      (residue B).comp f = φ.comp (residue A)) :
    IsLocalHom f := by
  -- Proof comment: use the maximal-ideal characterization and compare membership by vanishing
  -- in the residue fields.
  refine ((local_hom_TFAE f).out 4 0).mp ?_
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    have hresB : residue B (f x) = 0 := IsLocalRing.residue_eq_zero_iff (f x) |>.mpr hx
    have hxφ : φ (residue A x) = 0 := by
      have hxcomp := congrFun (congrArg DFunLike.coe h) x
      simpa [RingHom.comp_apply, hresB] using hxcomp.symm
    have hresA : residue A x = 0 := by
      apply φ.injective
      simpa using hxφ
    exact IsLocalRing.residue_eq_zero_iff x |>.mp hresA
  · intro hx
    have hresA : residue A x = 0 := IsLocalRing.residue_eq_zero_iff x |>.mpr hx
    have hresB : residue B (f x) = 0 := by
      have hxcomp := congrFun (congrArg DFunLike.coe h) x
      simpa [RingHom.comp_apply, hresA] using hxcomp
    exact IsLocalRing.residue_eq_zero_iff (f x) |>.mp hresB

/-- Helper for Chap10 Lemma 10 155 6: a local `R`-algebra map out of a henselization has the
residue-field comparison determined by its values on the base residue field. -/
lemma localAlgHom_residue_comp_of_base
    {T : Type w} [CommRing T] [IsLocalRing T] [Algebra R T] [IsLocalHom (algebraMap R T)]
    (κ : ResidueField Rh →+* ResidueField T)
    (hκ :
      κ.comp (ResidueField.map (algebraMap R Rh)) =
        ResidueField.map (algebraMap R T))
    (g : Rh →ₐ[R] T) (hg : IsLocalHom (g : Rh →+* T)) :
    (residue T).comp (g : Rh →+* T) = κ.comp (residue Rh) := by
  letI : IsLocalHom (g : Rh →+* T) := hg
  -- Proof comment: first compare the induced maps on residue fields. The map
  -- `ResidueField R → ResidueField Rh` is bijective because `Rh` is a henselization.
  have hg_base :
      (g : Rh →+* T).comp (algebraMap R Rh) = algebraMap R T := by
    ext r
    exact g.commutes r
  have hmap_base :
      (ResidueField.map (g : Rh →+* T)).comp
          (ResidueField.map (algebraMap R Rh)) =
        ResidueField.map (algebraMap R T) := by
    apply RingHom.ext
    intro y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    simp [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue, g.commutes r]
  have hmap : ResidueField.map (g : Rh →+* T) = κ := by
    apply RingHom.ext
    intro x
    obtain ⟨y, hy⟩ :=
      (IsHenselizationOf.residueField_bijective (R := R) (S := Rh)).2 x
    rw [← hy]
    have hy_left := congrFun (congrArg DFunLike.coe hmap_base) y
    have hy_right := congrFun (congrArg DFunLike.coe hκ) y
    exact hy_left.trans hy_right.symm
  -- Proof comment: rewrite the ordinary residue map through the induced residue-field map.
  rw [← IsLocalRing.ResidueField.map_comp_residue (g : Rh →+* T), hmap]

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: a bijective ring map is a filtered colimit of étale maps
in the source-facing arbitrary-universe wrapper. -/
lemma isFilteredColimitOfEtale_of_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) :
    RingHom.IsFilteredColimitOfEtale.{u, v, w} f := by
  letI : Algebra A B := f.toAlgebra
  -- Proof comment: unfold the wrapper and insert the single étale stage given by the
  -- bijective map after the canonical `ULift` transport.
  dsimp [RingHom.IsFilteredColimitOfEtale]
  apply CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale)
  dsimp [CommRingCat.etale]
  apply RingHom.Etale.of_bijective
  constructor
  · intro x y hxy
    apply ULift.ext
    apply hf.1
    exact congrArg ULift.down hxy
  · intro y
    obtain ⟨x, hx⟩ := hf.2 y.down
    refine ⟨ULift.up x, ?_⟩
    ext
    exact hx

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: the hidden index universe in the source-facing
ind-étale wrapper can be enlarged. -/
lemma isFilteredColimitOfEtale_index_lift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (h : RingHom.IsFilteredColimitOfEtale.{u, v, w} f) :
    RingHom.IsFilteredColimitOfEtale.{u, v, max w x} f := by
  -- Proof comment: after unfolding, reindex the filtered presentation by an essentially-small
  -- model in the larger universe.
  dsimp [RingHom.IsFilteredColimitOfEtale] at h ⊢
  rw [MorphismProperty.ind_iff_ind_underMk] at h ⊢
  rcases h with ⟨J, _, _, pres, hpres⟩
  exact ObjectProperty.of_essentiallySmall_index (P := CommRingCat.etale.underObj) pres hpres

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: ind-étaleness of `A → B` transports to matching common
`ULift` algebra maps. -/
lemma isFilteredColimitOfEtale_uliftAlgebraMap
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    let _ : Algebra A (ULift.{v, u} B) := ULift.algebra
    let _ : Algebra (ULift.{v, u} A) (ULift.{v, u} B) :=
      ULift.algebra' A (ULift.{v, u} B)
    RingHom.IsFilteredColimitOfEtale.{max u v, max u v, max u v}
      (algebraMap (ULift.{v, u} A) (ULift.{v, u} B)) := by
  -- Proof comment: factor the lifted algebra map as equivalence from the lifted source, the
  -- original ind-étale map, and equivalence to the lifted target.
  letI : Algebra A (ULift.{v, u} B) := ULift.algebra
  letI : Algebra (ULift.{v, u} A) (ULift.{v, u} B) :=
    ULift.algebra' A (ULift.{v, u} B)
  change RingHom.IsFilteredColimitOfEtale.{max u v, max u v, max u v}
    (algebraMap (ULift.{v, u} A) (ULift.{v, u} B))
  let f₁ : ULift.{v, u} A →+* A :=
    (ULift.ringEquiv : ULift.{v, u} A ≃+* A).toRingHom
  let f₂ : A →+* B := algebraMap A B
  let f₃ : B →+* ULift.{v, u} B :=
    (ULift.ringEquiv.symm : B ≃+* ULift.{v, u} B).toRingHom
  have hf₁ : RingHom.IsFilteredColimitOfEtale f₁ :=
    isFilteredColimitOfEtale_of_bijective f₁
      (ULift.ringEquiv : ULift.{v, u} A ≃+* A).bijective
  have hf₂ : RingHom.IsFilteredColimitOfEtale.{u, u, max u v} f₂ :=
    isFilteredColimitOfEtale_index_lift f₂ hAB
  have hf₁₂Small : RingHom.IsFilteredColimitOfEtale (f₂.comp f₁) :=
    RingHom.isFilteredColimitOfEtale_comp f₁ f₂ hf₁ hf₂
  have hf₁₂ : RingHom.IsFilteredColimitOfEtale.{max u v, u, max u v} (f₂.comp f₁) :=
    isFilteredColimitOfEtale_index_lift (f₂.comp f₁) hf₁₂Small
  have hf₃ : RingHom.IsFilteredColimitOfEtale f₃ :=
    isFilteredColimitOfEtale_of_bijective f₃
      (ULift.ringEquiv.symm : B ≃+* ULift.{v, u} B).bijective
  have hcomp : RingHom.IsFilteredColimitOfEtale (f₃.comp (f₂.comp f₁)) :=
    RingHom.isFilteredColimitOfEtale_comp (f₂.comp f₁) f₃ hf₁₂ hf₃
  have hmap : f₃.comp (f₂.comp f₁) =
      algebraMap (ULift.{v, u} A) (ULift.{v, u} B) := by
    ext a
    rfl
  rw [hmap] at hcomp
  have hcomp' :
      RingHom.IsFilteredColimitOfEtale.{max u v, max u v, max u v}
        (algebraMap (ULift.{v, u} A) (ULift.{v, u} B)) :=
    isFilteredColimitOfEtale_index_lift
      (algebraMap (ULift.{v, u} A) (ULift.{v, u} B)) hcomp
  simpa using hcomp'

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: a residue-field comparison over a surjective base residue
map determines every local algebra map on residue fields. -/
lemma localAlgHom_residue_comp_of_base_of_surjective
    {A T R : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [CommRing T] [IsLocalRing T] [Algebra R T] [IsLocalHom (algebraMap R T)]
    (hresA : Function.Surjective (ResidueField.map (algebraMap R A)))
    (κ : ResidueField A →+* ResidueField T)
    (hκ :
      κ.comp (ResidueField.map (algebraMap R A)) =
        ResidueField.map (algebraMap R T))
    (g : A →ₐ[R] T) (hg : IsLocalHom (g : A →+* T)) :
    (residue T).comp (g : A →+* T) = κ.comp (residue A) := by
  letI : IsLocalHom (g : A →+* T) := hg
  -- Proof comment: compare the induced residue maps after precomposition by the surjective
  -- base residue map.
  have hmap_base :
      (ResidueField.map (g : A →+* T)).comp
          (ResidueField.map (algebraMap R A)) =
        ResidueField.map (algebraMap R T) := by
    apply RingHom.ext
    intro y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    simp [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue, g.commutes r]
  have hmap : ResidueField.map (g : A →+* T) = κ := by
    apply RingHom.ext
    intro x
    obtain ⟨y, hy⟩ := hresA x
    rw [← hy]
    have hy_left := congrFun (congrArg DFunLike.coe hmap_base) y
    have hy_right := congrFun (congrArg DFunLike.coe hκ) y
    exact hy_left.trans hy_right.symm
  -- Proof comment: convert equality of induced residue-field maps back to equality after the
  -- ordinary residue map.
  rw [← IsLocalRing.ResidueField.map_comp_residue (g : A →+* T), hmap]

/-- Helper for Chap10 Lemma 10 155 6: an ind-étale local algebra with a surjective base residue
map has the expected unique local map into a henselian local target with compatible residue field. -/
lemma existsUnique_algHom_of_indEtale_residueFieldComparison
    {A T R : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [CommRing T] [IsLocalRing T] [HenselianLocalRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    (hA : (algebraMap R A).IsFilteredColimitOfEtale)
    (hresA : Function.Surjective (ResidueField.map (algebraMap R A)))
    (κ : ResidueField A →+* ResidueField T)
    (hκ :
      κ.comp (ResidueField.map (algebraMap R A)) =
        ResidueField.map (algebraMap R T)) :
    ∃! g : A →ₐ[R] T, IsLocalHom (g : A →+* T) := by
  let K := ResidueField T
  letI : Field K := inferInstance
  -- Proof comment: set the common field to the target residue field and give both algebras their
  -- maps to this common field.
  have hTKLocal : IsLocalHom (algebraMap T K) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  letI : IsLocalHom (algebraMap T K) := hTKLocal
  letI : Algebra A K := RingHom.toAlgebra (κ.comp (residue A))
  have hAKLocal : IsLocalHom (algebraMap A K) := by
    have hκLocal : IsLocalHom (κ.comp (residue A)) := inferInstance
    simpa [RingHom.algebraMap_toAlgebra] using hκLocal
  letI : IsLocalHom (algebraMap A K) := hAKLocal
  have hRAK : algebraMap R K = (algebraMap A K).comp (algebraMap R A) := by
    apply RingHom.ext
    intro r
    have hr := congrFun (congrArg DFunLike.coe hκ) (residue R r)
    simpa [K, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] using hr.symm
  letI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' hRAK
  have hRTK : algebraMap R K = (algebraMap T K).comp (algebraMap R T) := by
    ext r
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  letI : IsScalarTower R T K := IsScalarTower.of_algebraMap_eq' hRTK
  obtain ⟨g, hgK, huniqK⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
      (R := R) (A := A) (T := T) (K := K) hA
        (by
          simpa [K] using residueField_lift_residue_bijective T)
  have hgLocal : IsLocalHom (g : A →+* T) :=
    isLocalHom_of_residue_comp_eq (f := (g : A →+* T)) κ (by
      simpa [K, RingHom.algebraMap_toAlgebra] using hgK)
  refine ⟨g, hgLocal, ?_⟩
  intro g' hg'
  have hg'K : (algebraMap T K).comp (g' : A →+* T) = algebraMap A K := by
    have hres :=
      localAlgHom_residue_comp_of_base_of_surjective hresA κ hκ g' hg'
    simpa [K, RingHom.algebraMap_toAlgebra] using hres
  exact huniqK g' hg'K

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: a local algebra map stays local after lifting only the
target by `ULift`. -/
lemma isLocalHom_algebraMap_ulift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (ULift.{w, v} B)) := by
  letI : IsLocalRing (ULift.{w, v} B) :=
    RingEquiv.isLocalRing (ULift.ringEquiv.symm : B ≃+* ULift.{w, v} B)
  have hEquiv : IsLocalHom ((ULift.ringEquiv.symm : B ≃+* ULift.{w, v} B).toRingHom) :=
    Function.Surjective.isLocalHom _
      (ULift.ringEquiv.symm : B ≃+* ULift.{w, v} B).surjective
  have hcomp :
      IsLocalHom (((ULift.ringEquiv.symm : B ≃+* ULift.{w, v} B).toRingHom).comp
        (algebraMap A B)) :=
    RingHom.isLocalHom_comp
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w, v} B) (algebraMap A B)
  -- Proof comment: the lifted algebra map is the original local map followed by the local
  -- `ULift` equivalence.
  simpa using hcomp

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 155 6: a local algebra map stays local after lifting only the
source by `ULift`. -/
lemma isLocalHom_algebraMap_uliftSource
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    let _ : Algebra (ULift.{w, u} A) B := ULift.algebra' A B
    IsLocalHom (algebraMap (ULift.{w, u} A) B) := by
  letI : Algebra (ULift.{w, u} A) B := ULift.algebra' A B
  letI : IsLocalRing (ULift.{w, u} A) :=
    RingEquiv.isLocalRing (ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A)
  have hdown : IsLocalHom ((ULift.ringEquiv : ULift.{w, u} A ≃+* A).toRingHom) :=
    Function.Surjective.isLocalHom _
      (ULift.ringEquiv : ULift.{w, u} A ≃+* A).surjective
  have hcomp :
      IsLocalHom ((algebraMap A B).comp
        (ULift.ringEquiv : ULift.{w, u} A ≃+* A).toRingHom) :=
    RingHom.isLocalHom_comp (algebraMap A B)
      (ULift.ringEquiv.toRingHom : ULift.{w, u} A →+* A)
  -- Proof comment: the lifted-source algebra map is obtained by first projecting from the
  -- source lift and then using the original local map.
  simpa using hcomp

/-- Helper for Chap10 Lemma 10 155 6: residue-field comparison after lifting source and target
to the common universe `Type (max u v)`. -/
noncomputable abbrev commonLiftResidueComparison
    [IsLocalRing (ULift.{v, u} Rh)] [IsLocalRing (ULift.{u, v} Sh)] :
    ResidueField (ULift.{v, u} Rh) →+* ResidueField (ULift.{u, v} Sh) :=
  let eRhLift : ResidueField (ULift.{v, u} Rh) ≃+* ResidueField Rh :=
    IsLocalRing.ResidueField.mapEquiv (ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh)
  let eRh : ResidueField R ≃+* ResidueField Rh :=
    IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)
  let eSh : ResidueField S ≃+* ResidueField Sh :=
    IsHenselizationOf.residueFieldEquiv (R := S) (S := Sh)
  let eShLift : ResidueField Sh ≃+* ResidueField (ULift.{u, v} Sh) :=
    IsLocalRing.ResidueField.mapEquiv
      (ULift.ringEquiv.symm : Sh ≃+* ULift.{u, v} Sh)
  eShLift.toRingHom.comp <|
    eSh.toRingHom.comp <|
      (ResidueField.map (algebraMap R S)).comp <|
        eRh.symm.toRingHom.comp eRhLift.toRingHom

/-- Chap10 Lemma 10 155 6: let `R → S` be a local map of local rings, and let `Rh` and `Sh` be
henselizations of `R` and `S`. Then there exists a unique `R`-algebra map `Rh → Sh`; equivalently,
there is a unique local ring map `Rh → Sh` fitting into the commutative square over `R → S`. -/
@[stacks 04GS]
lemma existsUnique_algHom_between_henselizations_of_localHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    ∃! f : Rh →ₐ[R] Sh, IsLocalHom (f : Rh →+* Sh) := by
  -- Route correction: target-only `ULift.{u,v} Sh` still lives in `Type (max u v)`, so the
  -- same-universe universal property must be applied after lifting `R`, `Rh`, and `Sh` together.
  have hLifted :
      ∃! g : Rh →ₐ[R] ULift.{u, v} Sh,
        IsLocalHom (g : Rh →+* ULift.{u, v} Sh) := by
    letI : IsLocalRing (ULift.{v, u} R) :=
      RingEquiv.isLocalRing (ULift.ringEquiv.symm : R ≃+* ULift.{v, u} R)
    letI : IsLocalRing (ULift.{v, u} Rh) :=
      RingEquiv.isLocalRing (ULift.ringEquiv.symm : Rh ≃+* ULift.{v, u} Rh)
    letI : IsLocalRing (ULift.{u, v} Sh) :=
      RingEquiv.isLocalRing (ULift.ringEquiv.symm : Sh ≃+* ULift.{u, v} Sh)
    letI : HenselianLocalRing (ULift.{u, v} Sh) :=
      HenselianLocalRing.of_ringEquiv (ULift.ringEquiv.symm : Sh ≃+* ULift.{u, v} Sh)
    letI : Algebra R (ULift.{v, u} Rh) := ULift.algebra
    letI : Algebra (ULift.{v, u} R) (ULift.{v, u} Rh) :=
      ULift.algebra' R (ULift.{v, u} Rh)
    letI : Algebra R (ULift.{u, v} Sh) := ULift.algebra
    letI : Algebra (ULift.{v, u} R) (ULift.{u, v} Sh) :=
      ULift.algebra' R (ULift.{u, v} Sh)
    have hRRhLiftLocal : IsLocalHom (algebraMap R (ULift.{v, u} Rh)) :=
      isLocalHom_algebraMap_ulift (A := R) (B := Rh)
    letI : IsLocalHom (algebraMap R (ULift.{v, u} Rh)) := hRRhLiftLocal
    have hRuRhuLocal :
        IsLocalHom (algebraMap (ULift.{v, u} R) (ULift.{v, u} Rh)) :=
      isLocalHom_algebraMap_uliftSource (A := R) (B := ULift.{v, u} Rh)
    letI : IsLocalHom (algebraMap (ULift.{v, u} R) (ULift.{v, u} Rh)) :=
      hRuRhuLocal
    have hRSh : IsLocalHom (algebraMap R Sh) := by
      -- Proof comment: the structural map `R → Sh` is the composite of the two local maps
      -- `R → S` and `S → Sh`.
      rw [IsScalarTower.algebraMap_eq R S Sh]
      infer_instance
    letI : IsLocalHom (algebraMap R Sh) := hRSh
    have hRShuLocal : IsLocalHom (algebraMap R (ULift.{u, v} Sh)) :=
      isLocalHom_algebraMap_ulift (A := R) (B := Sh)
    letI : IsLocalHom (algebraMap R (ULift.{u, v} Sh)) := hRShuLocal
    have hRuShuLocal :
        IsLocalHom (algebraMap (ULift.{v, u} R) (ULift.{u, v} Sh)) :=
      isLocalHom_algebraMap_uliftSource (A := R) (B := ULift.{u, v} Sh)
    letI : IsLocalHom (algebraMap (ULift.{v, u} R) (ULift.{u, v} Sh)) :=
      hRuShuLocal
    have hEtale :
        RingHom.IsFilteredColimitOfEtale
          (algebraMap (ULift.{v, u} R) (ULift.{v, u} Rh)) := by
      -- Proof comment: transport the ind-étale presentation of `R → Rh` across the matching
      -- common-universe `ULift` equivalences.
      exact isFilteredColimitOfEtale_uliftAlgebraMap
        (A := R) (B := Rh)
        (IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
    have hres :
        Function.Surjective
          (ResidueField.map (algebraMap (ULift.{v, u} R) (ULift.{v, u} Rh))) := by
      -- Proof comment: reduce a lifted residue class to the original residue field of `Rh`,
      -- use the henselization bijection there, then lift the chosen source class back.
      intro z
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
      cases a with
      | up a0 =>
        obtain ⟨y, hy⟩ :=
          (IsHenselizationOf.residueField_bijective (R := R) (S := Rh)).2
            (residue Rh a0)
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
        refine ⟨residue (ULift.{v, u} R) (ULift.up r), ?_⟩
        apply
          (IsLocalRing.ResidueField.mapEquiv
            (ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh)).injective
        simpa [IsLocalRing.ResidueField.mapEquiv, IsLocalRing.ResidueField.map_residue]
          using hy
    have hκ :
        (commonLiftResidueComparison (R := R) (S := S) (Rh := Rh) (Sh := Sh)).comp
            (ResidueField.map (algebraMap (ULift.{v, u} R) (ULift.{v, u} Rh))) =
          ResidueField.map (algebraMap (ULift.{v, u} R) (ULift.{u, v} Sh)) := by
      -- Proof comment: verify the residue-field square on residue classes of lifted elements,
      -- where all maps reduce to the original square `R → S → Sh`.
      apply RingHom.ext
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      cases a with
      | up r =>
        have hAlgRh :
            (ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh)
              ((algebraMap R (ULift.{v, u} Rh)) r) = (algebraMap R Rh) r := by
          rfl
        have hRh :
            (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm
              ((residue Rh) ((algebraMap R Rh) r)) = residue R r := by
          apply
            (RingEquiv.symm_apply_eq
              (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh))).mpr
          simp [IsHenselizationOf.residueFieldEquiv, IsLocalRing.ResidueField.map_residue]
        have hSh :
            (IsHenselizationOf.residueFieldEquiv (R := S) (S := Sh))
              ((residue S) ((algebraMap R S) r)) =
              residue Sh ((algebraMap S Sh) ((algebraMap R S) r)) := by
          simp [IsHenselizationOf.residueFieldEquiv, IsLocalRing.ResidueField.map_residue]
        have hAlg :
            (algebraMap R (ULift.{u, v} Sh)) r =
              (ULift.ringEquiv.symm : Sh ≃+* ULift.{u, v} Sh)
                ((algebraMap S Sh) ((algebraMap R S) r)) := by
          rw [← IsScalarTower.algebraMap_apply R S Sh]
          rfl
        simp [commonLiftResidueComparison, RingHom.comp_apply,
          IsLocalRing.ResidueField.map_residue, hAlgRh, hRh, hSh,
          IsLocalRing.ResidueField.mapEquiv, hAlg]
    have hCommon :
        ∃! G : ULift.{v, u} Rh →ₐ[ULift.{v, u} R] ULift.{u, v} Sh,
          IsLocalHom (G : ULift.{v, u} Rh →+* ULift.{u, v} Sh) := by
      -- Proof comment: apply the already proved same-universe universal property to the
      -- common-universe lifted source, base, and target.
      exact existsUnique_algHom_of_indEtale_residueFieldComparison
        (A := ULift.{v, u} Rh) (T := ULift.{u, v} Sh) (R := ULift.{v, u} R)
        hEtale hres
        (commonLiftResidueComparison (R := R) (S := S) (Rh := Rh) (Sh := Sh)) hκ
    obtain ⟨G, hG, huniq⟩ := hCommon
    let g : Rh →ₐ[R] ULift.{u, v} Sh :=
      { toRingHom := (G : ULift.{v, u} Rh →+* ULift.{u, v} Sh).comp
          (ULift.ringEquiv.symm : Rh ≃+* ULift.{v, u} Rh).toRingHom
        commutes' := by
          intro r
          exact G.commutes (ULift.up r) }
    have hUpLocal :
        IsLocalHom ((ULift.ringEquiv.symm : Rh ≃+* ULift.{v, u} Rh).toRingHom) :=
      Function.Surjective.isLocalHom _
        (ULift.ringEquiv.symm : Rh ≃+* ULift.{v, u} Rh).surjective
    have hg : IsLocalHom (g : Rh →+* ULift.{u, v} Sh) := by
      -- Proof comment: descend locality by precomposing the common-lift map with the local
      -- equivalence `Rh → ULift Rh`.
      exact RingHom.isLocalHom_comp (G : ULift.{v, u} Rh →+* ULift.{u, v} Sh)
        (ULift.ringEquiv.symm.toRingHom : Rh →+* ULift.{v, u} Rh)
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    let G' : ULift.{v, u} Rh →ₐ[ULift.{v, u} R] ULift.{u, v} Sh :=
      { toRingHom := (g' : Rh →+* ULift.{u, v} Sh).comp
          (ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh).toRingHom
        commutes' := by
          intro x
          cases x with
          | up r => exact g'.commutes r }
    have hDownLocal :
        IsLocalHom ((ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh).toRingHom) :=
      Function.Surjective.isLocalHom _
        (ULift.ringEquiv : ULift.{v, u} Rh ≃+* Rh).surjective
    have hG' : IsLocalHom (G' : ULift.{v, u} Rh →+* ULift.{u, v} Sh) := by
      -- Proof comment: lift a competing `R`-algebra map to the common universe and use
      -- uniqueness there.
      exact RingHom.isLocalHom_comp (g' : Rh →+* ULift.{u, v} Sh)
        (ULift.ringEquiv.toRingHom : ULift.{v, u} Rh →+* Rh)
    have hEq : G' = G := huniq G' hG'
    apply AlgHom.ext
    intro x
    have hx := AlgHom.congr_fun hEq (ULift.up x)
    simpa [g, G'] using hx
  -- Proof comment: once the lifted-target uniqueness is known, `ULift.algEquiv` transports it
  -- back to the desired target `Sh`.
  exact existsUnique_algHom_localHom_of_uliftTarget
    (R := R) (A := Rh) (B := Sh) hLifted

/-- The canonical comparison map between henselizations induced by the local map `R → S`. -/
noncomputable abbrev henselizationMap
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    Rh →ₐ[R] Sh :=
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := S) (Rh := Rh) (Sh := Sh)

/-- The ring-hom view of the canonical comparison map between henselizations, with the ambient
`R`-algebra structure on `Sh` derived canonically from `R → S → Sh`. -/
noncomputable abbrev henselizationMapRingHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsHenselizationOf S Sh] :
    Rh →+* Sh :=
  let _ : Algebra R Sh :=
    RingHom.toAlgebra ((algebraMap S Sh).comp (algebraMap R S))
  let _ : IsScalarTower R S Sh :=
    IsScalarTower.of_algebraMap_eq' rfl
  (henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh)).toRingHom

/-- The canonical comparison map between henselizations is local. -/
theorem henselizationMap_isLocalHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    IsLocalHom ((henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh) : Rh →ₐ[R] Sh).toRingHom) :=
  Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := S) (Rh := Rh) (Sh := Sh)

/-- The `Rh`-algebra structure on `Sh` induced by the canonical comparison map between
henselizations. -/
noncomputable abbrev henselizationMapAlgebra
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    Algebra Rh Sh :=
  RingHom.toAlgebra
    (henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh)).toRingHom

end
