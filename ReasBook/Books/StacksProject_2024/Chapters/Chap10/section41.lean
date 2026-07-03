import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_41_1 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)

open PrimeSpectrum

/- Definition 10.41.1 (1): a ring map `φ : R →+* S` satisfies going up exactly when the induced
map `Spec(S) → Spec(R)` is a specializing map. -/
#check (SpecializingMap (comap φ))

/- Definition 10.41.1 (2): after installing the canonical algebra structure from `φ`, the
going-down property is the owner predicate `Algebra.HasGoingDown R S`. -/
#check
  (let _ : Algebra R S := φ.toAlgebra
   Algebra.HasGoingDown R S)

end

/-! ### Lemma_10_41_2 (from Chap10) -/
universe u v

section

open PrimeSpectrum
open Algebra.HasGoingDown
open Topology

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: going down for commutative algebras, expressed through the induced map on prime
  spectra;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`,
  `primeSpectrum_comap_isSpectralMap`,
  `exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology`;
* best owner abstraction: `Algebra.HasGoingDown R S`, with the prime-spectrum
  `GeneralizingMap (comap (algebraMap R S))` formulation as derived API;
* layer: `source-facing`, since Lemma 10.41.2 adds the textbook open-map criterion for going down
  rather than merely recalling an existing equivalence.

Primitive-vs-derived split:
* primitive data: the ambient `R`-algebra structure on `S` and the open-map hypothesis on
  `PrimeSpectrum.comap (algebraMap R S)`;
* derived API: the reformulation of going down as
  `GeneralizingMap (comap (algebraMap R S))`, plus the constructible-topology closedness of
  singleton fibers obtained from the spectral-map owner.
-/
/-- Lemma 10.41.2: if the canonical map `Spec(S) → Spec(R)` is open, then the `R`-algebra `S`
has the canonical going-down property `Algebra.HasGoingDown R S`. -/
-- Proof sketch: this is the Stacks proof. Let `p ⊆ p'` in `R` and let `q'` lie over `p'`. For
-- every `g ∉ q'`, the basic open `D(g)` contains `q'`, so its image in `Spec(R)` is an open
-- neighborhood of `p'`; since opens in `Spec(R)` are stable under generalization, it also contains
-- `p`. By Lemma `10.18.6`, this says `S_g ⊗[R] κ(p)` is nontrivial for every `g ∉ q'`. Passing to
-- the directed colimit over `g ∉ q'` shows `S_{q'} ⊗[R] κ(p)` is nontrivial, so `p` lies in the
-- image of `Spec(S_{q'}) → Spec(R)` by Lemma `10.18.6` again. Unwinding this gives a prime of `S`
-- below `q'` lying over `p`.
@[stacks 0407]
theorem hasGoingDown_of_isOpenMap_primeSpectrum_comap
    (hopen : IsOpenMap (comap (algebraMap R S))) :
    Algebra.HasGoingDown R S := by
  rw [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  intro q p hpq
  let f : PrimeSpectrum S → PrimeSpectrum R := comap (algebraMap R S)
  have hcompact : IsSpectralMap f := primeSpectrum_comap_isSpectralMap (algebraMap R S)
  have hfiber_closed : IsClosed[constructibleTopology (PrimeSpectrum S)] (f ⁻¹' ({p} : Set _)) := by
    have hp_closed : @IsClosed (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R))
        ({p} : Set (PrimeSpectrum R)) := by
      letI : @T2Space (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R)) :=
        constructibleTopology_t2Space_of_spectralSpace
      exact @isClosed_singleton (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R)) _ p
    exact
      @IsClosed.preimage (PrimeSpectrum S) (PrimeSpectrum R)
        (constructibleTopology (PrimeSpectrum S)) (constructibleTopology (PrimeSpectrum R))
        f hcompact.continuous_constructibleTopology ({p} : Set (PrimeSpectrum R)) hp_closed
  have hq_mem : q ∈ closure (f ⁻¹' ({p} : Set _)) := by
    rw [← hopen.preimage_closure_eq_closure_preimage (continuous_comap (algebraMap R S))
      ({p} : Set _)]
    simpa [f, specializes_iff_mem_closure] using hpq
  obtain ⟨q', hq', hq'q⟩ :=
    exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology hfiber_closed hq_mem
  exact ⟨q', hq'q, by simpa [f] using hq'⟩

end

/-! ### Lemma_10_41_3 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: going up / going down for the induced map on prime spectra;
* owner abstraction: `Algebra.HasGoingDown R S`;
* sampled canonical declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`,
  `PrimeSpectrum.comap`,
  and the chapter recall shape `SpecializingMap (comap (algebraMap R S))` from
  `Definition_10_41_1`;
* layer: `bridge/view`, since this item only recalls owner-side spectrum-map characterizations and
  adds no new source-facing data.

Primitive-vs-derived split:
* primitive data: none beyond the ambient `R`-algebra structure on `S`.
* derived API: the geometric reformulations `GeneralizingMap (comap (algebraMap R S))` and
  `SpecializingMap (comap (algebraMap R S))`.
-/
/- Lemma 10.41.3 (1): an `R`-algebra `S` satisfies going down if and only if generalizations lift
along the canonical map `Spec S → Spec R`. This is exactly the canonical mathlib theorem
`Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`. -/
recall Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap

/- Lemma 10.41.3 (2): Definition 10.41.1 (1) already uses the canonical specializing-map
formulation of going up for the spectrum map `Spec S → Spec R`. -/
#check (SpecializingMap (comap (algebraMap R S)))

end

/-! ### Lemma_10_41_4 (from Chap10) -/
universe u v w

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/- Lemma 10.41.4 (1): if `R → S` and `S → T` satisfy going down, then `R → T` satisfies going
down. This is exactly the canonical mathlib theorem `Algebra.HasGoingDown.trans`. -/
recall Algebra.HasGoingDown.trans

/- Lemma 10.41.4 (2): by Definition 10.41.1, going up for `R → S` is the specializing-map
property of `PrimeSpectrum.comap (algebraMap R S)`. Since `PrimeSpectrum.comap (algebraMap R T)` is
the composite of `PrimeSpectrum.comap (algebraMap S T)` and `PrimeSpectrum.comap (algebraMap R S)`,
the source-facing stability statement is the specialization of the canonical theorem
`SpecializingMap.comp` to these spectrum maps. -/
#check
  (show SpecializingMap (comap (algebraMap R S)) →
      SpecializingMap (comap (algebraMap S T)) →
      SpecializingMap (comap (algebraMap R T)) from
    fun hRS hST ↦ by
      simpa [Function.comp, comap_comp, IsScalarTower.algebraMap_eq R S T] using
        SpecializingMap.comp hST hRS)

end

/-! ### Lemma_10_41_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Lemma 10.41.5 (00HY): if the image of `Spec(S) → Spec(R)` is stable under specialization, then
it is closed. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`. -/
recall PrimeSpectrum.isClosed_range_of_stableUnderSpecialization

end

/-! ### Lemma_10_41_6 (from Chap10) -/
universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

open AlgebraicGeometry
open PrimeSpectrum

/- Lemma 10.41.6: for the canonical map `Spec(S) → Spec(R)`, the source-facing equivalence is the
affine-spectrum bridge to the canonical owner theorem
`AlgebraicGeometry.isClosedMap_iff_specializingMap`. -/
#check
  (show SpecializingMap (comap (algebraMap R S)) ↔ IsClosedMap (comap (algebraMap R S)) from
    (isClosedMap_iff_specializingMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))).symm)

end

/-! ### Lemma_10_41_7 (from Chap10) -/
/- Lemma 10.41.7 (00I0) (1): if a constructible subset of `Spec(R)` is stable under
specialization, then it is closed. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`. -/
recall PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible

/- Lemma 10.41.7 (00I0) (2): if a constructible subset of `Spec(R)` is stable under
generalization, then it is open. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`. -/
recall PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible

/-! ### Proposition_10_41_8 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Proposition 10.41.8: if `R → S` is of finite presentation and satisfies going down, then the
induced map `Spec(S) → Spec(R)` is open. The source's flat finite-presentation case is the
immediate specialization obtained from the canonical instance `Algebra.HasGoingDown.of_flat`.
This is exactly the canonical mathlib theorem
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`. -/
recall PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end

/-! ### Lemma_10_41_9 (from Chap10) -/
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

/-! ### Lemma_10_41_10 (from Chap10) -/
open PrimeSpectrum Algebra.TensorProduct
open scoped TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Lemma 10.41.10: for a field `k` and `k`-algebras `R` and `S`, the canonical map
`Spec(S ⊗[k] R) → Spec(R)` induced by the right-factor inclusion
`TensorProduct.includeRight : R →ₐ[k] S ⊗[k] R` is open. -/
theorem isOpenMap_primeSpectrum_comap_algebraMap_tensorProduct_of_field :
    IsOpenMap (comap ((includeRight : R →ₐ[k] S ⊗[k] R).toRingHom)) := by
  let e : R ⊗[k] S ≃ₐ[k] S ⊗[k] R := Algebra.TensorProduct.comm k R S
  rw [show ((includeRight : R →ₐ[k] S ⊗[k] R).toRingHom) =
      e.toRingHom.comp (algebraMap R (R ⊗[k] S)) by
        ext r
        simp [e],
    comap_comp]
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field.comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenMap

end

/-! ### Lemma_10_41_11 (from Chap10) -/
open Ideal

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]

local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
local notation "T" => Algebra.algebraMapSubmonoid S p.primeCompl

/- Domain triage:
* primary domain: localization at primes in a commutative-algebra extension, with prime fibers
  controlled by going up / going down;
* owner abstractions: `IsLocalization.AtPrime` for the target local ring structure, together with
  `Ideal.LiesOver`, `Ideal.primesOver`, `SpecializingMap (PrimeSpectrum.comap (algebraMap R S))`,
  and `Algebra.HasGoingDown R S` for the prime-lifting hypotheses;
* sampled canonical declarations:
  `Definition_10_41_1`'s recall shape for going up,
  `Ideal.exists_ideal_le_liesOver_of_le`,
  `IsLocalization.of_le_of_exists_dvd`,
  and `Ideal.primesOver`;
* layer: `bridge/view`, since this item proves that the localization of `S` away from `p`
  coincides with the canonical owner object `IsLocalization.AtPrime ... q` under unique lifting
  hypotheses, without introducing new source-facing data.

Primitive-vs-derived split:
* primitive data: the ambient algebra `R → S`, the chosen primes `p` and `q`, and the localization
  ring `Sₚ`;
* derived API: the comparison lemmas showing `Sₚ` is the localization of `S` at `q` under the
  going-up or going-down uniqueness hypotheses.
-/

omit [p.IsPrime] in
private theorem eq_of_subsingleton_primesOver
    (hunique : Subsingleton (p.primesOver S)) {Q Q' : Ideal S} [Q.IsPrime] [Q'.IsPrime]
    [Q.LiesOver p] [Q'.LiesOver p] :
    Q = Q' := by
  exact congrArg Subtype.val <|
    show (primesOver.mk p Q : p.primesOver S) = primesOver.mk p Q' from
      Subsingleton.elim _ _

private theorem le_of_under_le_of_unique_liesOver_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (hunique : Subsingleton (p.primesOver S)) {Q : Ideal S} [Q.IsPrime] (hQp : Q.under R ≤ p) :
    Q ≤ q := by
  have hspec :
      PrimeSpectrum.comap (algebraMap R S) ⟨Q, inferInstance⟩ ⤳
        (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    rw [← PrimeSpectrum.le_iff_specializes]
    simpa [Ideal.under_def] using hQp
  obtain ⟨Q', hQQ', hQ'p⟩ := hgu hspec
  letI : Q'.asIdeal.LiesOver p := (Ideal.liesOver_iff _ _).2 <| by
    simpa [Ideal.under_def] using (congrArg PrimeSpectrum.asIdeal hQ'p).symm
  have hQ'q : Q'.asIdeal = q := eq_of_subsingleton_primesOver hunique
  have hQle : Q ≤ Q'.asIdeal := by
    simpa using (PrimeSpectrum.le_iff_specializes _ _).mpr hQQ'
  simpa [hQ'q] using hQle

private theorem le_of_under_le_of_unique_liesOver_of_goingDown
    [Algebra.HasGoingDown R S]
    (hunique : ∀ p' : Ideal R, p'.IsPrime → Subsingleton (p'.primesOver S))
    {Q : Ideal S} [Q.IsPrime] (hQp : Q.under R ≤ p) :
    Q ≤ q := by
  let p' : Ideal R := Q.under R
  letI : p'.IsPrime := inferInstance
  obtain ⟨Q', hQ'q, hQ'⟩ := Ideal.exists_ideal_le_liesOver_of_le q hQp
  rcases hQ' with ⟨hQ'prime, hQ'p'⟩
  letI : Q'.IsPrime := hQ'prime
  letI : Q'.LiesOver p' := hQ'p'
  letI : Q.LiesOver p' := Ideal.over_under Q
  have hQ'Q : Q' = Q := eq_of_subsingleton_primesOver (hunique p' inferInstance)
  simpa [hQ'Q] using hQ'q

omit [q.IsPrime] [q.LiesOver p] in
private theorem exists_mem_T_dvd_of_notMem_of_under_le
    (hle : ∀ {Q : Ideal S}, Q.IsPrime → Q.under R ≤ p → Q ≤ q) {x : S} (hx : x ∉ q) :
    ∃ t ∈ T, x ∣ t := by
  by_contra! h
  have hdisj : Disjoint ((Ideal.span {x} : Ideal S) : Set S) T := by
    rw [Set.disjoint_left]
    intro y hyx hyT
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hyx
    exact h _ hyT ⟨c, mul_comm _ _⟩
  obtain ⟨Q, hQprime, hxQ, hQdisj⟩ :=
    Ideal.exists_le_prime_disjoint (.span {x}) T hdisj
  letI : Q.IsPrime := hQprime
  have hQp : Q.under R ≤ p := by
    intro r hrQ
    by_contra hrp
    exact Set.subset_compl_iff_disjoint_right.mpr hQdisj hrQ ⟨r, hrp, rfl⟩
  exact hx <| hle hQprime hQp <| hxQ (Ideal.mem_span_singleton_self x)

private theorem isLocalization_primeCompl_of_under_le
    (hle : ∀ {Q : Ideal S}, Q.IsPrime → Q.under R ≤ p → Q ≤ q) :
    IsLocalization.AtPrime Sₚ q := by
  have hTq : T ≤ q.primeCompl := by
    intro y hy hyq
    exact (Set.disjoint_left.mp <| Ideal.disjoint_primeCompl_of_liesOver q p) hy hyq
  refine IsLocalization.of_le_of_exists_dvd T q.primeCompl hTq ?_
  intro y hy
  exact exists_mem_T_dvd_of_notMem_of_under_le hle hy

/-- Lemma 10.41.11 (1): if the fiber `p.primesOver S` is a subsingleton and `R → S` satisfies
going up, then localizing `S` away from `p` is the localization of `S` at `q`. -/
-- Proof sketch: every prime of `Sₚ` contracts to a prime below `p`; apply going up to lift it to
-- a prime of `S` over `p`, then use uniqueness of the prime above `p` to identify that lift with
-- `q`. This forces every prime of `Sₚ` to lie under `q`, which is the criterion for localizing at
-- `q.primeCompl`.
theorem isLocalization_primeCompl_of_unique_liesOver_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (hunique : Subsingleton (p.primesOver S)) :
    IsLocalization.AtPrime Sₚ q := by
  refine isLocalization_primeCompl_of_under_le ?_
  intro Q hQprime hQp
  letI : Q.IsPrime := hQprime
  exact le_of_under_le_of_unique_liesOver_of_goingUp hgu hunique hQp

/-- Lemma 10.41.11 (2): if `q` lies over `p`, `R → S` satisfies going down, and every prime of
`R` has at most one prime of `S` lying over it, then localizing `S` away from `p` is the
localization of `S` at `q`. -/
-- Proof sketch: for a prime of `Sₚ`, view its corresponding prime of `S` and contract it to
-- `R`. Use going down from `q` to produce a prime of `S` over that contraction contained in `q`;
-- fiberwise uniqueness then identifies this descended prime with the given one, so the latter lies
-- under `q`. Hence `Sₚ` localizes `S` at `q.primeCompl`.
theorem isLocalization_primeCompl_of_unique_liesOver_of_goingDown
    [Algebra.HasGoingDown R S]
    (hunique : ∀ p' : Ideal R, p'.IsPrime → Subsingleton (p'.primesOver S)) :
    IsLocalization.AtPrime Sₚ q := by
  refine isLocalization_primeCompl_of_under_le ?_
  intro Q hQprime hQp
  letI : Q.IsPrime := hQprime
  exact le_of_under_le_of_unique_liesOver_of_goingDown hunique hQp

end

/-! ### Lemma_10_41_12 (from Chap10) -/
universe u v w

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

namespace Module

/-- Helper for Lemma 10.41.12: a nonzero module over a local `B` remains supported at the closed
point after contracting along a local ring map `A → B`. -/
lemma closedPoint_mem_support_of_nontrivial_of_local_map
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Nontrivial M] :
    IsLocalRing.closedPoint A ∈ Module.support A M := by
  -- The closed point of `B` lies in the support of any nonzero `B`-module, and support contracts
  -- along the local map.
  have hclosedB : IsLocalRing.closedPoint B ∈ Module.support B M := by
    simpa using IsLocalRing.closedPoint_mem_support B M
  have hpre :=
    Module.support_subset_preimage_comap
      (R := A) (A := B) (M := M) hclosedB
  simpa [IsLocalRing.comap_closedPoint (algebraMap A B)] using hpre

/-- Helper for Lemma 10.41.12: support of a localized module descends to support of the original
module after contracting the prime along the localization map. -/
lemma mem_support_comap_of_mem_support_localized_atPrime
    (q' : PrimeSpectrum S) {Q : PrimeSpectrum (Localization.AtPrime q'.asIdeal)}
    (hQ : Q ∈ Module.support (Localization.AtPrime q'.asIdeal)
      (LocalizedModule.AtPrime q'.asIdeal N)) :
    PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.asIdeal)) Q ∈
      Module.support S N := by
  -- Rewrite support through the localized tensor-product model, then descend support by the
  -- canonical base-change theorem for finite modules.
  let e :=
    LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl N
  have hsupp :
      Module.support (Localization.AtPrime q'.asIdeal) (LocalizedModule.AtPrime q'.asIdeal N) =
        Module.support (Localization.AtPrime q'.asIdeal)
          ((Localization.AtPrime q'.asIdeal) ⊗[S] N) :=
    LinearEquiv.support_eq (R := Localization.AtPrime q'.asIdeal) e
  have hQ' : Q ∈ Module.support (Localization.AtPrime q'.asIdeal)
      ((Localization.AtPrime q'.asIdeal) ⊗[S] N) := by
    exact hsupp ▸ hQ
  have hbase :
      Q ∈ PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.asIdeal)) ⁻¹'
        Module.support S N := by
    simpa [Module.Lemma_10_40_6 (R := S) (R' := Localization.AtPrime q'.asIdeal) (M := N)]
      using hQ'
  exact hbase

section

omit [Module R N] [IsScalarTower R S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: after localizing at `q' ∈ Supp(N)`, quotienting by the maximal
ideal of the localized base ring `R_(q' ∩ R)` stays nontrivial. -/
lemma localized_target_quotient_nontrivial
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let B := Localization.AtPrime q'.1.asIdeal
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  letI : IsLocalHom (algebraMap A B) := by
    -- The localized map `R_(q' ∩ R) → S_q'` is local, so maximal ideals contract correctly.
    simpa [f] using
      Localization.isLocalHom_localRingHom
        ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal) q'.1.asIdeal
        (algebraMap R S) rfl
  have hnontrivialM : Nontrivial M := by
    -- Support membership says exactly that the localization `N_q'` is nonzero.
    simpa [M] using (Module.mem_support_iff.mp q'.2)
  letI : Nontrivial M := hnontrivialM
  let PB : Submodule B M := IsLocalRing.maximalIdeal B • (⊤ : Submodule B M)
  have hquotB : Nontrivial (M ⧸ PB) := by
    -- Nakayama over the local ring `B = S_q'` rules out `maximalIdeal B • M = M`.
    have hPB : PB ≠ ⊤ := by
      dsimp [PB]
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator B M)))
    exact Submodule.Quotient.nontrivial_iff.2 hPB
  have hquotB_A : Nontrivial (M ⧸ PB.restrictScalars A) := by
    -- Restrict scalars on the quotient so the later factor map lives over `A`.
    exact (Submodule.Quotient.restrictScalarsEquiv A PB).surjective.nontrivial
  have hsmulA_le :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≤ PB.restrictScalars A := by
    -- Route correction: instead of comparing mixed-base tensors, contract the maximal ideal of `A`
    -- into the maximal ideal of `B` and compare the two quotient modules.
    refine Submodule.smul_le.2 fun a ha m hm ↦ ?_
    change a • m ∈ PB.restrictScalars A
    change a • m ∈ PB
    dsimp [PB]
    rw [← IsScalarTower.algebraMap_smul B a m]
    have hmem_map :
        algebraMap A B a ∈ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) :=
      Ideal.mem_map_of_mem _ ha
    have hmem :
        algebraMap A B a ∈ IsLocalRing.maximalIdeal B :=
      (IsLocalRing.map_maximalIdeal_le (algebraMap A B)) hmem_map
    exact Submodule.smul_mem_smul hmem (by simpa using hm)
  -- The quotient by `maximalIdeal A` surjects onto the already nontrivial quotient by
  -- `maximalIdeal B`, so the source quotient is nontrivial as well.
  exact (Submodule.factor_surjective hsmulA_le).nontrivial

/-- Helper for Lemma 10.41.12: the canonical fiber module over a prime is the residue-field
tensor of the module. -/
private noncomputable def fiber_module_linearEquiv
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (p : PrimeSpectrum A) :
    (p.asIdeal.Fiber B) ⊗[B] M ≃ₗ[B] M ⊗[A] p.asIdeal.ResidueField :=
  TensorProduct.comm B (p.asIdeal.Fiber B) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B M)
      (Algebra.TensorProduct.commRight A B p.asIdeal.ResidueField).symm.toLinearEquiv
      ≪≫ₗ
    cancelBaseChange A B B M p.asIdeal.ResidueField

/-- Helper for Lemma 10.41.12: nontriviality of the `κ(p)`-fiber of a localized module yields a
nontrivial module over the corresponding fiber ring. -/
lemma nontrivial_fiber_ring_tensor_of_nontrivial_prime_residue_tensor
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (p : PrimeSpectrum A)
    (h : Nontrivial (p.asIdeal.ResidueField ⊗[A] M)) :
    Nontrivial ((p.asIdeal.Fiber B) ⊗[B] M) := by
  let K := p.asIdeal.ResidueField
  -- First rewrite the given fiber in the tensor order used by the canonical fiber-module model.
  have hcomm : Nontrivial (M ⊗[A] K) := by
    exact (TensorProduct.comm A K M).nontrivial_congr.mp h
  -- Then transport nontriviality through the standard fiber-module comparison.
  let e := fiber_module_linearEquiv (A := A) (B := B) (M := M) p
  exact e.nontrivial_congr.mpr hcomm

/-- Helper for Lemma 10.41.12: after localizing at `q' ∈ Supp(N)`, the closed fiber over
`R_(q' ∩ R)` is nontrivial, expressed as the quotient by the maximal ideal. -/
lemma nontrivial_closed_fiber_at_localized_target
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let B := Localization.AtPrime q'.1.asIdeal
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  -- The previous helper already proves the needed closed-fiber quotient is nonzero.
  simpa using localized_target_quotient_nontrivial (R := R) (S := S) (N := N) q'

end

/-- Helper for Lemma 10.41.12: the localized module at `q'` is faithfully flat over
`R_(q' ∩ R)`. -/
lemma faithfullyFlat_localized_target
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let B := Localization.AtPrime q'.1.asIdeal
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Module.FaithfullyFlat A M := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let B := Localization.AtPrime q'.1.asIdeal
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  have hflat : Module.Flat A M := by
    -- Flatness localizes from `N` over `R` to `N_q'` over `R_(q' ∩ R)`.
    simpa [A, M] using
      flat_localizedModule_atPrime_over_under_of_flat
        (R := R) (A := S) (M := N) inferInstance q'.1
  letI : Module.Flat A M := hflat
  have hclosed :
      Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
    simpa [A, B, M] using nontrivial_closed_fiber_at_localized_target (R := R) (S := S) (N := N) q'
  have hmax_ne :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
    exact Submodule.Quotient.nontrivial_iff.mp hclosed
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal A M).2 ⟨hflat, ?_⟩
  intro I hI hItop
  have hImax : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hI
  apply hmax_ne
  exact eq_top_iff.2 <| by
    calc
      ⊤ = I • (⊤ : Submodule A M) := hItop.symm
      _ ≤ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) :=
        Submodule.smul_mono hImax le_rfl

/-- Helper for Lemma 10.41.12: a support point of the fiber-ring module contracts to a support
point of the localized module, and its contraction to the localized base is the chosen prime. -/
lemma support_point_contraction_of_fiber_ring_support
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (p : PrimeSpectrum A) (r : PrimeSpectrum (p.asIdeal.Fiber B))
    (hr : r ∈ Module.support (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M)) :
    let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
    let Q : PrimeSpectrum B := Qover.1
    Q ∈ Module.support B M ∧ PrimeSpectrum.comap (algebraMap A B) Q = p := by
  let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
  let Q : PrimeSpectrum B := Qover.1
  constructor
  · -- Rewrite support on the fiber ring as inverse image of support on `B`.
    change PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) r ∈ Module.support B M
    simpa [Module.Lemma_10_40_6 (R := B) (R' := p.asIdeal.Fiber B) (M := M)] using hr
  · -- The fiber equivalence remembers exactly that this contracted prime lies over `p`.
    simpa [Q, Qover] using Qover.2

/-- Helper for Lemma 10.41.12: a support point of the localization at `q'` descends to a support
point of the original module below `q'`. -/
lemma localized_support_point_descends
    (q' : Module.support S N)
    (Q : PrimeSpectrum (Localization.AtPrime q'.1.asIdeal))
    (hQ : Q ∈ Module.support (Localization.AtPrime q'.1.asIdeal)
      (LocalizedModule.AtPrime q'.1.asIdeal N)) :
    PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q ∈
        Module.support S N ∧
      PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q ≤ q'.1 := by
  constructor
  · -- Support contracts along the localization map by the earlier localized-support bridge.
    exact mem_support_comap_of_mem_support_localized_atPrime (N := N) q'.1 hQ
  · -- The localization spectrum is exactly the interval of primes below `q'`.
    exact
      (IsLocalization.AtPrime.primeSpectrumOrderIso
        (Localization.AtPrime q'.1.asIdeal) q'.1.asIdeal Q).2

section

omit [Module R N] [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: once a localized prime `Q` contracts to `pLoc`, its descended
prime in `Spec S` contracts further to the original prime `p`. -/
lemma comap_of_descended_prime_eq
    (q' : Module.support S N) (p : PrimeSpectrum R)
    (hpq : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1)
    (Q : PrimeSpectrum (Localization.AtPrime q'.1.asIdeal))
    (hQ :
      let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      let B := Localization.AtPrime q'.1.asIdeal
      let _ : Algebra A B :=
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
      let pLoc : PrimeSpectrum A :=
        (IsLocalization.AtPrime.primeSpectrumOrderIso A
          ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
      PrimeSpectrum.comap (algebraMap A B) Q = pLoc) :
    PrimeSpectrum.comap (algebraMap R S)
      (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q) = p := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
  have hQ' : PrimeSpectrum.comap (algebraMap A B) Q = pLoc := by
    simpa [A, B, pLoc] using hQ
  let eA := IsLocalization.AtPrime.primeSpectrumOrderIso A
    ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  have hpLoc_eq : PrimeSpectrum.comap (algebraMap R A) pLoc = p := by
    -- Unpack the defining equation of `pLoc` from the localization order isomorphism on `A`.
    simpa [pLoc, eA] using congrArg Subtype.val (eA.apply_symm_apply ⟨p, hpq⟩)
  have hcompSB :
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) =
        PrimeSpectrum.comap (algebraMap R B) Q := by
    -- Rewrite contraction through the composite `R → S → B`.
    simpa [IsScalarTower.algebraMap_eq R S B] using
      (PrimeSpectrum.comap_comp_apply (algebraMap R S) (algebraMap S B) Q).symm
  have hcompAB :
      PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap (algebraMap A B) Q) =
        PrimeSpectrum.comap (algebraMap R B) Q := by
    -- Rewrite contraction through the composite `R → A → B`.
    simpa [IsScalarTower.algebraMap_eq R A B] using
      (PrimeSpectrum.comap_comp_apply (algebraMap R A) (algebraMap A B) Q).symm
  -- Route correction: isolate the final contraction calculation from the support descent.
  calc
    PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap (algebraMap S B) Q)
      = PrimeSpectrum.comap (algebraMap R B) Q := hcompSB
    _ = PrimeSpectrum.comap (algebraMap R A)
          (PrimeSpectrum.comap (algebraMap A B) Q) := hcompAB.symm
    _ = PrimeSpectrum.comap (algebraMap R A) pLoc := by rw [hQ']
    _ = p := hpLoc_eq

end

section

omit [Module R N] [IsScalarTower R S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: a nontrivial fiber ring module over the localized target produces
a support point below `q'` lying over the original prime `p`. -/
lemma exists_support_prime_below_of_nontrivial_fiber_ring_tensor
    (q' : Module.support S N) (p : PrimeSpectrum R)
    (hpq : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1)
    (hfiber :
      let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      let B := Localization.AtPrime q'.1.asIdeal
      let M := LocalizedModule.AtPrime q'.1.asIdeal N
      let _ : Algebra A B :=
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
      let _ : Module A M :=
        Module.compHom M
          (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
            q'.1.asIdeal (algebraMap R S) rfl)
      let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
      let pLoc : PrimeSpectrum A :=
        (IsLocalization.AtPrime.primeSpectrumOrderIso A
          ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
      Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M)) :
      ∃ q : PrimeSpectrum S,
        q ∈ Module.support S N ∧
          q ≤ q'.1 ∧
            PrimeSpectrum.comap (algebraMap R S) q = p := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
  have hfiber' : Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M) := by
    simpa [A, B, M, pLoc] using hfiber
  -- Choose a support point of the nonzero fiber module exactly as in the source proof.
  obtain ⟨r, hr⟩ :
      (Module.support (pLoc.asIdeal.Fiber B) ((pLoc.asIdeal.Fiber B) ⊗[B] M)).Nonempty := by
    exact Module.nonempty_support_iff.mpr hfiber'
  let Qover := (PrimeSpectrum.preimageEquivFiber A B pLoc).symm r
  let Q : PrimeSpectrum B := Qover.1
  have hQ :
      Q ∈ Module.support B M ∧ PrimeSpectrum.comap (algebraMap A B) Q = pLoc := by
    -- Contract the support point of the fiber back to `Spec(B)`.
    simpa [Q, Qover] using
      support_point_contraction_of_fiber_ring_support
        (A := A) (B := B) (M := M) pLoc r hr
  have hq :
      PrimeSpectrum.comap (algebraMap S B) Q ∈ Module.support S N ∧
        PrimeSpectrum.comap (algebraMap S B) Q ≤ q'.1 := by
    -- Descend the localized support point to a point of `Spec(S)` below `q'`.
    simpa [B] using localized_support_point_descends (N := N) q' Q hQ.1
  refine ⟨PrimeSpectrum.comap (algebraMap S B) Q, hq.1, hq.2, ?_⟩
  -- Finish by identifying the contraction of the descended prime with the original `p`.
  exact comap_of_descended_prime_eq (R := R) (S := S) (N := N) q' p hpq Q hQ.2

end

/- Domain triage:
* primary domain: support of finite modules on prime spectra, together with lifting of
  generalizations along the induced support map;
* core/canonical owners: `Module.support S N` for the subset of `Spec S` and `GeneralizingMap`
  for the topological lifting property;
* sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`,
  `Module.support_subset_preimage_comap`,
  and `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`;
* layer: `bridge/view`, since the source theorem is about the canonical map from the support of
  `N` to `Spec R`, not about introducing a new owner object.

Primitive-vs-derived split:
* primitive data: the finite `S`-module `N`, its `R`-flatness, and the canonical subset
  `Module.support S N`;
* derived API: the induced map `Module.support S N → PrimeSpectrum R`, written canonically as the
  composite of the subtype inclusion with `PrimeSpectrum.comap (algebraMap R S)`.
-/
/-- Lemma 10.41.12: if `N` is a finite `S`-module that is flat over `R`, then generalizations
lift along the support map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. Equivalently, if `p ⤳ p'` in `Spec R` and
`q' ∈ support S N` lies over `p'`, then there exists `q ∈ support S N` with `q ⤳ q'`
lying over `p`. -/
theorem generalizingMap_support_comap_of_flat :
    GeneralizingMap (comap (algebraMap R S) ∘ ((↑) : support S N → PrimeSpectrum S)) := by
  intro q' p hpq
  have hpq_le : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1 := by
    simpa using (PrimeSpectrum.le_iff_specializes p (PrimeSpectrum.comap (algebraMap R S) q'.1)).mpr hpq
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm
      ⟨p, hpq_le⟩
  have hff : Module.FaithfullyFlat A M := by
    -- Localize at `q'` and use the closed-fiber criterion proved above.
    simpa [A, B, M] using faithfullyFlat_localized_target (R := R) (S := S) (N := N) q'
  have hpLoc_nontrivial : Nontrivial (M ⊗[A] pLoc.asIdeal.ResidueField) := by
    exact (faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField.1 hff) pLoc
  have hpLoc_nontrivial' : Nontrivial (pLoc.asIdeal.ResidueField ⊗[A] M) := by
    -- Commute the tensor factors to match the fiber-ring helper.
    exact (TensorProduct.comm A pLoc.asIdeal.ResidueField M).nontrivial_congr.mpr hpLoc_nontrivial
  have hfiber :
      Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M) := by
    exact nontrivial_fiber_ring_tensor_of_nontrivial_prime_residue_tensor
      (A := A) (B := B) (M := M) pLoc hpLoc_nontrivial'
  obtain ⟨q, hqsupport, hq_le, hq_comap⟩ :=
    exists_support_prime_below_of_nontrivial_fiber_ring_tensor
      (R := R) (S := S) (N := N) q' p hpq_le hfiber
  refine ⟨⟨q, hqsupport⟩, ?_, hq_comap⟩
  -- The support is stable under specialization, so the order relation downstairs lifts to the
  -- subtype `Module.support S N`.
  exact (subtype_specializes_iff ⟨q, hqsupport⟩ q').2 <|
    (PrimeSpectrum.le_iff_specializes _ _).1 hq_le

end Module

end
