import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {k : Type u} {R : Type v} {S : Type w} [Field k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S]

variable (S' : Subalgebra k S) (f : S' ⊗[k] R)

/- Domain-style sampling:
- primary domain: prime spectra of tensor-product algebras over a field, localized at basic
  opens and detected on residue-field fibers;
- sampled owner API: `PrimeSpectrum.localization_away_comap_range`,
  `PrimeSpectrum.mem_image_comap_basicOpen`, `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`,
  and `Algebra.TensorProduct.map`;
- `source-facing`: equality of the images of
  `Spec ((S ⊗[k] R)₍fₛ₎) → Spec R` and `Spec ((S' ⊗[k] R)₍f₎) → Spec R`;
- `core/canonical`: the owner criterion `PrimeSpectrum.mem_image_comap_basicOpen`;
- `bridge/view`: the fiber comparison map induced by the subalgebra inclusion `S'.val`.

Primitive data are only the subalgebra inclusion `S'.val`, the tensor element `f`, and the
residue-field fiber over `p : Spec R`; the fiber injectivity argument is derived API. -/

local notation "fₛ" =>
  Algebra.TensorProduct.map S'.val (AlgHom.id k R) f

private noncomputable def tensorSubalgebraFiberMap (S' : Subalgebra k S) (p : PrimeSpectrum R) :
    ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) →ₐ[R]
      ((S ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) := by
  let K := p.asIdeal.ResidueField
  let ι : K ⊗[k] S' →ₐ[R] K ⊗[k] S :=
    { __ := (Algebra.TensorProduct.map (AlgHom.id k K) S'.val).toRingHom
      commutes' := by
        intro r
        change (Algebra.TensorProduct.map (AlgHom.id k K) S'.val)
            ((includeLeft : K →ₐ[k] K ⊗[k] S') ((algebraMap R K) r)) =
          (includeLeft : K →ₐ[k] K ⊗[k] S) ((algebraMap R K) r)
        simp }
  let e₁ := (Algebra.TensorProduct.comm R (S' ⊗[k] R) K).toAlgHom
  let e₂ :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R] K)
      ((Algebra.TensorProduct.commRight k R S').symm)).toAlgHom
  let e₃ := (Algebra.TensorProduct.cancelBaseChange k R R K S').toAlgHom
  let e₄ := (Algebra.TensorProduct.cancelBaseChange k R R K S).symm.toAlgHom
  let e₅ :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R] K)
      (Algebra.TensorProduct.commRight k R S)).toAlgHom
  let e₆ := (Algebra.TensorProduct.comm R K (S ⊗[k] R)).toAlgHom
  exact e₆.comp <| e₅.comp <| e₄.comp <| ι.comp <| e₃.comp <| e₂.comp e₁

private theorem tensorSubalgebraFiberMap_injective (S' : Subalgebra k S) (p : PrimeSpectrum R) :
    Function.Injective (tensorSubalgebraFiberMap S' p) := by
  let K := p.asIdeal.ResidueField
  let ι : K ⊗[k] S' →ₐ[R] K ⊗[k] S :=
    { __ := (Algebra.TensorProduct.map (AlgHom.id k K) S'.val).toRingHom
      commutes' := by
        intro r
        change (Algebra.TensorProduct.map (AlgHom.id k K) S'.val)
            ((includeLeft : K →ₐ[k] K ⊗[k] S') ((algebraMap R K) r)) =
          (includeLeft : K →ₐ[k] K ⊗[k] S) ((algebraMap R K) r)
        simp }
  have hι :=
    TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : K →ₗ[k] K)
      S'.val.toLinearMap (fun _ _ h ↦ h) Subtype.val_injective
  dsimp [tensorSubalgebraFiberMap]
  exact (Algebra.TensorProduct.comm R K (S ⊗[k] R)).injective.comp <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R] K)
      (Algebra.TensorProduct.commRight k R S)).injective.comp <|
    (Algebra.TensorProduct.cancelBaseChange k R R K S).symm.injective.comp <|
    (show Function.Injective ι by simpa [ι] using hι).comp <|
    (Algebra.TensorProduct.cancelBaseChange k R R K S').injective.comp <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R] K)
      ((Algebra.TensorProduct.commRight k R S').symm)).injective.comp <|
    (Algebra.TensorProduct.comm R (S' ⊗[k] R) K).injective

private theorem tensorSubalgebraFiberMap_comp_algebraMap (S' : Subalgebra k S)
    (p : PrimeSpectrum R) :
    (tensorSubalgebraFiberMap S' p).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          (S' ⊗[k] R) →+* ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField)) =
      (Algebra.TensorProduct.includeLeftRingHom :
        (S ⊗[k] R) →+* ((S ⊗[k] R) ⊗[R] p.asIdeal.ResidueField)).comp
        (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom := by
  let K := p.asIdeal.ResidueField
  let ι' : (S' ⊗[k] R) →+* ((S' ⊗[k] R) ⊗[R] K) :=
    Algebra.TensorProduct.includeLeftRingHom
  let ι : (S ⊗[k] R) →+* ((S ⊗[k] R) ⊗[R] K) :=
    Algebra.TensorProduct.includeLeftRingHom
  change (tensorSubalgebraFiberMap S' p).toRingHom.comp ι' =
    ι.comp (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom
  apply RingHom.ext
  intro f
  refine TensorProduct.induction_on f ?_ ?_ ?_
  · simp [tensorSubalgebraFiberMap]
  · intro a b
    simp only [tensorSubalgebraFiberMap, ι, ι', AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, map_tmul, Subalgebra.coe_val, AlgHom.coe_id, id_eq]
    simpa using congrArg
      (fun z : S ⊗[k] R ↦ z ⊗ₜ[R] (1 : K))
      (show b • (Algebra.TensorProduct.commRight k R S (1 ⊗ₜ[k] (a : S))) =
          (a : S) ⊗ₜ[k] b by
        simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply])
  · intro x y hx hy
    calc
      ((tensorSubalgebraFiberMap S' p).toRingHom.comp ι') (x + y) =
          ((tensorSubalgebraFiberMap S' p).toRingHom.comp ι') x +
            ((tensorSubalgebraFiberMap S' p).toRingHom.comp ι') y := by
              exact RingHom.map_add ((tensorSubalgebraFiberMap S' p).toRingHom.comp ι') x y
      _ = (ι.comp (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom) x +
          (ι.comp (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom) y := by
            rw [hx, hy]
      _ = (ι.comp (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom) (x + y) := by
            symm
            exact RingHom.map_add
              (ι.comp (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom) x y

/-- Lemma 10.41.9: for a field `k`, a `k`-subalgebra `S' ⊆ S`, and `f ∈ S' ⊗[k] R`, the images of
the canonical maps `Spec((S ⊗[k] R)_{f}) → Spec(R)` and `Spec((S' ⊗[k] R)_{f}) → Spec(R)` are the
same. -/
-- Proof sketch: by Lemma 10.18.6, membership of `p : Spec R` in either image is equivalent to
-- nontriviality of the corresponding fiber over `κ(p)`. The map
-- `S' ⊗[k] κ(p) → S ⊗[k] κ(p)` induced by the subalgebra inclusion is injective, so if the image
-- of `f` is not nilpotent in the smaller fiber ring then it is not nilpotent in the larger one.
-- This gives one inclusion; the reverse inclusion is immediate because the smaller ring maps into
-- the larger one through the same localization element. Internally, we rewrite both ranges via
-- `PrimeSpectrum.localization_away_comap_range` and reduce to the owner criterion
-- `PrimeSpectrum.mem_image_comap_basicOpen`.
theorem range_comap_localized_tensor_subalgebra_eq :
    Set.range
        (PrimeSpectrum.comap (algebraMap R (Localization.Away fₛ)) :
          PrimeSpectrum (Localization.Away fₛ) → PrimeSpectrum R) =
      Set.range
        (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) :
          PrimeSpectrum (Localization.Away f) → PrimeSpectrum R) := by
  rw [show Set.range
      (PrimeSpectrum.comap (algebraMap R (Localization.Away fₛ)) :
        PrimeSpectrum (Localization.Away fₛ) → PrimeSpectrum R) =
        PrimeSpectrum.comap (algebraMap R (S ⊗[k] R)) '' PrimeSpectrum.basicOpen fₛ by
        rw [show (PrimeSpectrum.comap (algebraMap R (Localization.Away fₛ)) :
            PrimeSpectrum (Localization.Away fₛ) → PrimeSpectrum R) =
              PrimeSpectrum.comap (algebraMap R (S ⊗[k] R)) ∘
                PrimeSpectrum.comap (algebraMap (S ⊗[k] R) (Localization.Away fₛ)) by
              ext x
              rfl,
          Set.range_comp, PrimeSpectrum.localization_away_comap_range (Localization.Away fₛ) fₛ],
    show Set.range
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) :
        PrimeSpectrum (Localization.Away f) → PrimeSpectrum R) =
        PrimeSpectrum.comap (algebraMap R (S' ⊗[k] R)) '' PrimeSpectrum.basicOpen f by
        rw [show (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) :
            PrimeSpectrum (Localization.Away f) → PrimeSpectrum R) =
              PrimeSpectrum.comap (algebraMap R (S' ⊗[k] R)) ∘
                PrimeSpectrum.comap (algebraMap (S' ⊗[k] R) (Localization.Away f)) by
              ext x
              rfl,
          Set.range_comp, PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]]
  ext p
  rw [PrimeSpectrum.mem_image_comap_basicOpen, PrimeSpectrum.mem_image_comap_basicOpen]
  let K := p.asIdeal.ResidueField
  let ψ := tensorSubalgebraFiberMap S' p
  have hψ : Function.Injective ψ :=
    tensorSubalgebraFiberMap_injective S' p
  have hmap :
      ψ (algebraMap (S' ⊗[k] R) ((S' ⊗[k] R) ⊗[R] K) f) =
        algebraMap (S ⊗[k] R) ((S ⊗[k] R) ⊗[R] K) fₛ := by
    exact congrArg
      (fun φ : (S' ⊗[k] R) →+* ((S ⊗[k] R) ⊗[R] K) ↦ φ f)
      (tensorSubalgebraFiberMap_comp_algebraMap S' p)
  rw [← hmap]
  change ¬ IsNilpotent
      (ψ.toRingHom
        (algebraMap (S' ⊗[k] R) ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) f)) ↔
    ¬ IsNilpotent
      (algebraMap (S' ⊗[k] R) ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) f)
  exact not_congr (show IsNilpotent
      (ψ.toRingHom
        (algebraMap (S' ⊗[k] R) ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) f)) ↔
    IsNilpotent
      (algebraMap (S' ⊗[k] R) ((S' ⊗[k] R) ⊗[R] p.asIdeal.ResidueField) f) from
      IsNilpotent.map_iff hψ)

end
