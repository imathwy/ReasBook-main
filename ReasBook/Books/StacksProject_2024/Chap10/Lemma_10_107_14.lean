import Mathlib
import StacksProject_2024.Chap10.Lemma_10_107_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct ModuleCat
open Algebra.TensorProduct

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.107.14: over an epic algebra map, the tensors `1 ⊗ (s • x)` and
`s ⊗ x` have the same image under the canonical tensor-collapse equivalence, hence coincide. -/
lemma one_tmul_smul_eq_tmul_of_algebra_isEpi
    (h : Algebra.IsEpi R S) {M : ModuleCat S} [Module R M] [IsScalarTower R S M]
    (s : S) (x : M) :
    (1 : S) ⊗ₜ[R] (s • x) = s ⊗ₜ[R] x := by
  letI : Algebra.IsEpi R S := h
  -- Collapse both tensors to the same element of `M` via `TensorProduct.lid'`.
  apply (TensorProduct.lid' R S M).injective
  simp

/-- Helper for Lemma 10.107.14: if `R → S` is an epimorphism, then every `R`-linear map between
`S`-modules already commutes with the `S`-action. -/
lemma restrictScalars_map_smul_of_algebra_isEpi
    (h : Algebra.IsEpi R S) {M N : ModuleCat S}
    (φ : (ModuleCat.restrictScalars (algebraMap R S)).obj M ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj N)
    (s : S) (x : M) :
    φ (s • x) = s • φ x := by
  letI : Algebra.IsEpi R S := h
  let _ : Module R M := Module.compHom M (algebraMap R S)
  let _ : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S M :=
    { smul_assoc := fun r s x => by
        simpa [Algebra.smul_def] using (mul_smul (algebraMap R S r) s x) }
  letI : IsScalarTower R S N :=
    { smul_assoc := fun r s y => by
        simpa [Algebra.smul_def] using (mul_smul (algebraMap R S r) s y) }
  -- Route correction: replace the raw tensor evaluation map by base change followed by `lid'`.
  have h_tensor :
      φ.hom.baseChange S ((1 : S) ⊗ₜ[R] (s • x)) =
        φ.hom.baseChange S (s ⊗ₜ[R] x) := by
    exact congrArg (φ.hom.baseChange S)
      (one_tmul_smul_eq_tmul_of_algebra_isEpi (R := R) (S := S) (M := M) h s x)
  -- Injectivity of `TensorProduct.lid'` converts the tensor equality back to the desired formula.
  apply (TensorProduct.lid' R S N).symm.injective
  rw [TensorProduct.lid'_symm_apply, TensorProduct.lid'_symm_apply]
  calc
    (1 : S) ⊗ₜ[R] φ (s • x)
        = φ.hom.baseChange S ((1 : S) ⊗ₜ[R] (s • x)) := by
            rw [LinearMap.baseChange_tmul]
    _ = φ.hom.baseChange S (s ⊗ₜ[R] x) := h_tensor
    _ = s ⊗ₜ[R] φ x := by rw [LinearMap.baseChange_tmul]
    _ = (1 : S) ⊗ₜ[R] (s • φ x) := by
          symm
          exact one_tmul_smul_eq_tmul_of_algebra_isEpi (R := R) (S := S) (M := N) h s (φ x)

/-- Helper for Lemma 10.107.14: an epimorphic algebra map makes restriction of scalars full on
module categories. -/
lemma restrictScalars_full_of_algebra_isEpi
    (h : Algebra.IsEpi R S) :
    (ModuleCat.restrictScalars (algebraMap R S)).Full := by
  refine ⟨?_⟩
  intro M N φ
  -- Rebuild the unique `S`-linear map from the underlying `R`-linear map.
  let φS : M →ₗ[S] N :=
    { toFun := φ
      map_add' := φ.hom.map_add
      map_smul' := fun s x => restrictScalars_map_smul_of_algebra_isEpi h φ s x }
  refine ⟨ModuleCat.ofHom φS, ?_⟩
  ext x
  rfl

/-- Helper for Lemma 10.107.14: the identity map from a restricted object to the chosen
`R`-module structure is linear because both actions agree via the scalar tower. -/
lemma restrictScalars_objIso_identity_linear
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (a : A) (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (AddEquiv.refl M).toFun (a • x) = a • (AddEquiv.refl M).toFun x := by
  -- Rewrite the restricted action through `A → B` and then use the scalar-tower compatibility.
  rw [ModuleCat.restrictScalars.smul_def]
  simpa [one_smul, mul_one] using (IsScalarTower.smul_assoc a (1 : B) (x : M)).symm

/-- Helper for Lemma 10.107.14: the restricted object on an `S`-module with a compatible
`R`-module structure is canonically the same underlying `R`-module. -/
noncomputable def restrictScalars_objIso
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
    { __ := AddEquiv.refl M
      map_smul' := restrictScalars_objIso_identity_linear (A := A) (B := B) (M := M) }).toModuleIso

/-- Helper for Lemma 10.107.14: the object-identity bridge on restricted scalars acts by the
identity on elements. -/
@[simp] lemma restrictScalars_objIso_hom_apply
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (restrictScalars_objIso (A := A) (B := B) (M := M)).hom x = x :=
  rfl

/-- Helper for Lemma 10.107.14: the inverse object-identity bridge on restricted scalars also
acts by the identity on elements. -/
@[simp] lemma restrictScalars_objIso_inv_apply
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : M) :
    (restrictScalars_objIso (A := A) (B := B) (M := M)).inv x = x :=
  rfl

/-- Helper for Lemma 10.107.14: this is the restricted-scalars version of the canonical map
`s ↦ 1 ⊗ s` from `S` to `S ⊗[R] S`. -/
noncomputable def restrictScalars_includeRight_hom :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ⟶
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⊗[R] S))) :=
  -- Route correction: conjugate the concrete `includeRight` linear map through identity-carrier
  -- isomorphisms so the reverse implication works on stable `ModuleCat.of R` objects.
  (restrictScalars_objIso (A := R) (B := S) (M := S)).hom ≫
    ModuleCat.ofHom
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap) ≫
    (restrictScalars_objIso (A := R) (B := S) (M := S ⊗[R] S)).inv

/-- Helper for Lemma 10.107.14: the restricted `includeRight` morphism sends `s` to `1 ⊗ s`. -/
@[simp] lemma restrictScalars_includeRight_hom_apply (s : S) :
    restrictScalars_includeRight_hom (R := R) (S := S) s = (1 : S) ⊗ₜ[R] s :=
by
  -- Unfold the transported adapter and collapse the identity-carrier isomorphisms pointwise.
  simp [restrictScalars_includeRight_hom, restrictScalars_objIso]

/-- Helper for Lemma 10.107.14: full faithfulness of restriction of scalars forces the two
canonical maps `S → S ⊗[R] S` to coincide. -/
lemma includeLeft_eq_includeRight_of_restrictScalars_fullyFaithful
    (hff : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful) :
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) := by
  let X : ModuleCat.{u} S := ModuleCat.of.{u} S S
  let Y : ModuleCat.{u} S := ModuleCat.of.{u} S (S ⊗[R] S)
  let hRight :
      ((ModuleCat.restrictScalars (algebraMap R S)).obj X) ⟶
        ((ModuleCat.restrictScalars (algebraMap R S)).obj Y) := by
    simpa [X, Y] using (restrictScalars_includeRight_hom (R := R) (S := S))
  let g : ModuleCat.of.{u} S S ⟶ ModuleCat.of.{u} S (S ⊗[R] S) :=
    hff.homEquiv.symm hRight
  have hg_map :
      (ModuleCat.restrictScalars (algebraMap R S)).map g =
        hRight := by
    simpa [g] using hff.homEquiv.apply_symm_apply hRight
  have hg_right (s : S) : g s = (1 : S) ⊗ₜ[R] s := by
    -- The fully faithful preimage has the same underlying `R`-linear map after restriction.
    have hs :
        ((ModuleCat.restrictScalars (algebraMap R S)).map g) s =
          hRight s := by
      exact congrArg
        (fun f : ((ModuleCat.restrictScalars (algebraMap R S)).obj X) ⟶
            ((ModuleCat.restrictScalars (algebraMap R S)).obj Y) ↦ f s)
        hg_map
    simpa [hRight, X, Y, restrictScalars_includeRight_hom_apply] using hs
  have hg_left (s : S) : g s = s ⊗ₜ[R] (1 : S) := by
    -- The preimage `g` is `S`-linear for the left `S`-action on the tensor product.
    calc
      g s = g (s • (1 : S)) := by simp
      _ = s • g 1 := by simpa using g.hom.map_smul s (1 : S)
      _ = s • ((1 : S) ⊗ₜ[R] (1 : S)) := by rw [hg_right 1]
      _ = s ⊗ₜ[R] (1 : S) := by
            simpa using (TensorProduct.smul_tmul' s (1 : S) (1 : S))
  -- Compare both canonical tensor-factor maps with the same `S`-linear preimage `g`.
  ext s
  calc
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) s = g s := by
      simpa using (hg_left s).symm
    _ = (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) s := by
      simpa using hg_right s

/-- The canonical `core/canonical` bridge for Lemma 10.107.14: for a commutative `R`-algebra `S`,
the algebra map is epic exactly when restriction of scalars on module categories is fully
faithful. This refines the source-text equality
`Hom_S(N₁, N₂) = Hom_R(N₁, N₂)` to the owner abstraction `Algebra.IsEpi R S`. -/
-- Proof sketch: if `R → S` is epic, `TensorProduct.lid'` upgrades every `R`-linear map of
-- `S`-modules canonically to an `S`-linear map, so restriction of scalars is fully faithful.
-- Conversely, full faithfulness forces the `R`-linear map `s ↦ 1 ⊗ s : S → S ⊗[R] S` to come
-- from an `S`-linear map for the left `S`-module structure, hence `1 ⊗ s = s ⊗ 1` for all `s`,
-- which is exactly `Algebra.IsEpi R S`.
theorem algebra_isEpi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsEpi R S ↔
      Nonempty ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful) := by
  constructor
  · intro h
    -- The forward direction is the source argument: tensor-collapse upgrades every underlying
    -- `R`-linear map to an `S`-linear one, so restriction of scalars is fully faithful.
    letI : (ModuleCat.restrictScalars (algebraMap R S)).Full :=
      restrictScalars_full_of_algebra_isEpi h
    exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  · rintro ⟨hff : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).FullyFaithful⟩
    -- The reverse direction recovers `1 ⊗ s = s ⊗ 1` from the fully faithful preimage of
    -- `includeRight`, then invokes the epimorphism criterion from Lemma 10.107.1.
    exact (algebra_isEpi_iff_includeLeft_eq_includeRight).mpr
      (includeLeft_eq_includeRight_of_restrictScalars_fullyFaithful hff)

end

/-- Lemma 10.107.14: a ring homomorphism `f : R →+* S` is an epimorphism of commutative rings if
and only if the restriction-of-scalars functor `ModuleCat.restrictScalars f : ModuleCat S ⥤
ModuleCat R` is fully faithful. This is the canonical category-theoretic form of the equivalence
between ring epimorphisms, equality of `S`-linear and `R`-linear maps between `S`-modules, and
full faithfulness of restriction of scalars. -/
-- Proof sketch: equip `S` with the `R`-algebra structure induced by `f`. The core bridge above
-- gives `Algebra.IsEpi R S ↔` full faithfulness of `ModuleCat.restrictScalars f`, and
-- `CommRingCat.epi_iff_epi` identifies `Algebra.IsEpi R S` with `Epi (CommRingCat.ofHom f)`.
theorem ringHom_epi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔ Nonempty ((ModuleCat.restrictScalars.{u, u, u} f).FullyFaithful) := by
  letI : Algebra R S := f.toAlgebra
  have hf : Epi (CommRingCat.ofHom f) ↔ Algebra.IsEpi R S := by
    simpa [RingHom.algebraMap_toAlgebra] using CommRingCat.epi_iff_epi
  exact hf.trans <| by
    simpa [RingHom.algebraMap_toAlgebra] using
      (algebra_isEpi_iff_restrictScalars_fullyFaithful (R := R) (S := S))

/-- Restriction of scalars along an epimorphism of commutative rings is fully faithful. This is
the canonical instance-level companion to `ringHom_epi_iff_restrictScalars_fullyFaithful`. -/
noncomputable instance restrictScalars_fullyFaithful_of_epi
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [Epi (CommRingCat.ofHom f)] :
    (ModuleCat.restrictScalars.{u, u, u} f).FullyFaithful :=
  ((ringHom_epi_iff_restrictScalars_fullyFaithful f).mp inferInstance).some
