import Mathlib
import StacksProject_2024.Chap10.Lemma_10_163_8
import StacksProject_2024.Chap10.Lemma_10_165_3
import StacksProject_2024.Chap10.Lemma_10_165_1
import StacksProject_2024.Chap10.Lemma_10_164_3
import StacksProject_2024.Chap10.Lemma_10_165_6
import StacksProject_2024.Chap10.Lemma_10_166_1
import StacksProject_2024.Chap10.Lemma_10_37_13
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- Helper for Lemma 15.51.10: a property of commutative algebras over fields, used to package the
formal-fiber axioms in Chapter 15. -/
abbrev FieldAlgebraProperty : Type (u + 1) :=
  ∀ (k A : Type u), [Field k] → [CommRing A] → [Algebra k A] → Prop

namespace FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)

/-- Helper for Lemma 15.51.10: a field-algebra property satisfies `(A)` if it is preserved by base
change along finitely generated extensions of the ground field. -/
class HasPropertyA : Prop where
  /-- Base change of a Noetherian `k`-algebra along a finitely generated field extension preserves
  the property `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- Helper for Lemma 15.51.10: a field-algebra property satisfies `(B)` if for every ground field
`k`, the induced ring property on Noetherian `k`-algebras can be checked on prime localizations. -/
class HasPropertyB : Prop where
  /-- The prime-local criterion for `P` over the fixed base field `k`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

/-- A field-algebra property has property `(E)` if it is preserved when the ground field is
replaced by a separable algebraic extension. -/
class HasPropertyE : Prop where
  /-- Base change of the ground field along a separable algebraic extension preserves `P`. -/
  separableBaseChange (k k' A : Type u) [Field k] [Field k'] [CommRing A]
      [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
      [Algebra.IsSeparable k k'] (hA : P k A) :
      P k' A

/-- Helper for Lemma 15.51.10: a field-algebra property has property `(C)` if it ascends along
regular morphisms on fibers of flat maps of Noetherian rings. -/
class HasPropertyC : Prop where
  /-- Property `(C)` ascends from the fibers of `A → B` to the fibers of `A → C` when `A → B` is
  flat and `B → C` is regular. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- Helper for Lemma 15.51.10: a field-algebra property has property `(D)` if it descends along
faithfully flat local extensions on closed fibers of Noetherian local rings. -/
class HasPropertyD : Prop where
  /-- Property `(D)` descends from the closed fiber over `A → C` to the closed fiber over `A → B`
  along a faithfully flat local extension `B → C`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`;
- best owner abstraction: the chapter package extending `(A)` and `(B)` by the canonical upstream
  `(C)` and `(D)` owners from `Lemma_15_51_4`, together with the named bridge
  `IsGeometricallyNormalProperty`; this file adds only the genuinely new separable-base-field
  clause `(E)`.

Source/core/bridge triage:
- `P.HasPropertyE` is source-facing;
- `P.HasPropertiesABCDE` is the core/canonical owner wrapper;
- `IsGeometricallyNormalProperty` and the instance below are the thin bridge/view from
  `IsGeometricallyNormal` to that owner.
-/

/-- The five formal-fiber axioms `(A)` through `(E)` for a property of Noetherian algebras over
fields. -/
class HasPropertiesABCDE : Prop
    extends P.HasPropertyA, P.HasPropertyB, P.HasPropertyC, P.HasPropertyD, P.HasPropertyE

end

end FieldAlgebraProperty

namespace Algebra

section

/-- Helper for Lemma 15.51.10: every fiber of a regular ring map is a normal ring. -/
lemma regularRingMap_fiber_normal
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsNormalRing R] (f : R →+* S) [f.IsRegularRingMap] (p : PrimeSpectrum R) :
    let _ : Algebra R S := f.toAlgebra
    IsNormalRing (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
  exact isNormalRing_of_isRegularRing

/-- Helper for Lemma 15.51.10: a regular ring map with Noetherian normal source has normal target. -/
theorem isNormalRing_of_regularRingMap
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsNormalRing R] (f : R →+* S) [f.IsRegularRingMap] :
    IsNormalRing S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  exact isNormalRing_of_flat_of_fiber fun p ↦ regularRingMap_fiber_normal f p

/-- The canonical `FieldAlgebraProperty` bridge for geometric normality. -/
abbrev IsGeometricallyNormalProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsGeometricallyNormal.{u, u} k A

section

variable {k k' A : Type u}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]

-- Proof sketch: this is exactly the separable-base-field invariance theorem for geometric
-- normality from Lemma `10.165.6`, repackaged as Chapter 15 property `(E)` for the canonical
-- bridge `IsGeometricallyNormalProperty`.
/-- Lemma 15.51.10 (5), owner-form: geometric normality has property `(E)` in the Chapter 15
formal-fiber package. -/
@[stacks 0BIX]
instance isGeometricallyNormal_hasPropertyE :
    IsGeometricallyNormalProperty.HasPropertyE where
  separableBaseChange k k' A := by
    intro _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

section

variable {k K A : Type u}
variable [Field k] [Field K] [CommRing A]
variable [Algebra k K] [Algebra k A] [Algebra.EssFiniteType k K]
variable [IsNoetherianRing A]

-- Proof sketch: test geometric normality of `K ⊗[k] A` against an arbitrary further field
-- extension `L / K`, then cancel the intermediate base change `K` so the resulting ring is the
-- already-known normal base change `L ⊗[k] A`.
omit [Algebra.EssFiniteType k K] [IsNoetherianRing A] in
/-- Helper for Lemma 15.51.10: geometric normality is preserved by base change along a finitely
generated extension of the ground field. -/
theorem isGeometricallyNormal_baseChange_of_finitelyGeneratedFieldExtension
    (hA : IsGeometricallyNormal k A) :
    IsGeometricallyNormal K (K ⊗[k] A) := by
  letI : IsGeometricallyNormal k A := hA
  refine ⟨?_⟩
  intro L _ _
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let e : L ⊗[K] (K ⊗[k] A) ≃ₐ[K] L ⊗[k] A :=
    Algebra.TensorProduct.cancelBaseChange k K K L A
  -- The cancelled tensor product is normal by the original geometric-normality hypothesis.
  letI : IsNormalRing (L ⊗[k] A) :=
    IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A) L
  exact isNormalRing_of_ringEquiv e.toRingEquiv.symm

end

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Helper for Lemma 15.51.10: faithful flatness of `B → C` induces a faithfully flat map on the
fiber over any prime of `A`. -/
lemma fiber_faithfullyFlat
    (p : PrimeSpectrum A) (hBC_ff : (algebraMap B C).FaithfullyFlat) :
    let _ : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
    ∃ (_ : Algebra (p.asIdeal.Fiber B) (p.asIdeal.Fiber C)),
      Module.FaithfullyFlat (p.asIdeal.Fiber B) (p.asIdeal.Fiber C) := by
  let S := p.asIdeal.Fiber B
  let D := S ⊗[B] C
  let T := p.asIdeal.Fiber C
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  letI : CommRing D := inferInstance
  letI : Algebra S D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC_ff
  let f : S →+* D := algebraMap S D
  have hf : f.FaithfullyFlat := by
    letI : Module.FaithfullyFlat S D := inferInstance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃+* T :=
    (Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B S C).toRingEquiv
  let g : D →+* T := e.toRingHom
  have hg : g.FaithfullyFlat := by
    simpa [g] using
      (RingHom.FaithfullyFlat.of_bijective e.bijective : g.FaithfullyFlat)
  have hff : (g.comp f).FaithfullyFlat := by
    change (RingHom.comp g f).FaithfullyFlat
    exact RingHom.FaithfullyFlat.stableUnderComposition f g hf hg
  letI : Algebra S T := RingHom.toAlgebra (g.comp f)
  refine ⟨inferInstance, ?_⟩
  exact RingHom.faithfullyFlat_algebraMap_iff.mp (by simpa [f, g] using hff)

end

section

variable {k A : Type u}
variable [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]

-- Route correction: property `(B)` is proved by first replacing `K ⊗[k] A_p` with the canonical
-- localization of `K ⊗[k] A`, then comparing prime localizations on that intermediate ring.
-- Proof sketch: the forward implication is localization stability from Lemma `10.165.3`. For
-- the converse, the remaining missing step is the source-faithful comparison between a prime
-- localization of `K ⊗[k] A` and a localization of `K ⊗[k] A_p`.
omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.51.10: geometric normality can be checked on all prime localizations. -/
theorem isGeometricallyNormal_iff_forall_localization_atPrime :
    IsGeometricallyNormal k A ↔
      ∀ p : PrimeSpectrum A, IsGeometricallyNormal k (Localization.AtPrime p.asIdeal) := by
  constructor
  · intro hA p
    letI : IsGeometricallyNormal k A := hA
    -- Localization preserves geometric normality directly.
    exact Algebra.IsGeometricallyNormal.of_isLocalization p.asIdeal.primeCompl
  · intro hlocal
    refine ⟨?_⟩
    intro K _ _
    let T := K ⊗[k] A
    letI : CommRing T := inferInstance
    refine ⟨fun q ↦ ?_⟩
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A T) q
    let U := K ⊗[k] Localization.AtPrime p.asIdeal
    letI : CommRing U := inferInstance
    letI : Algebra A T := Algebra.TensorProduct.rightAlgebra
    let D := T ⊗[A] Localization.AtPrime p.asIdeal
    letI : CommRing D := inferInstance
    letI : Algebra T D := Algebra.TensorProduct.leftAlgebra
    letI : Algebra (Localization.AtPrime p.asIdeal) D := Algebra.TensorProduct.rightAlgebra
    letI : IsLocalization (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl) D := by
      infer_instance
    -- Replace the actual tensor with the explicit localization model.
    let e : D ≃ₐ[K] U :=
      Algebra.IsPushout.cancelBaseChangeAlg k K A T (Localization.AtPrime p.asIdeal)
    have hdisj :
        Disjoint
            ((Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl :
              Submonoid T) : Set T) q.asIdeal := by
      refine Set.disjoint_left.mpr ?_
      intro x hxM hxq
      rcases hxM with ⟨a, ha, rfl⟩
      exact ha (by simpa [p, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hxq)
    have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap T D)) := by
      rwa [PrimeSpectrum.localization_comap_range D
        (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl)]
    rcases hqrange with ⟨qD, hqD_comap⟩
    letI : IsGeometricallyNormal k (Localization.AtPrime p.asIdeal) := hlocal p
    letI : IsNormalRing U :=
      IsGeometricallyNormal.isNormalRing_baseChange (k := k)
        (R := Localization.AtPrime p.asIdeal) K
    have hD : IsNormalRing D := by
      exact isNormalRing_of_faithfullyFlat e.toRingHom
        (RingHom.FaithfullyFlat.of_bijective e.bijective)
    letI : IsNormalRing D := hD
    have hqD_asIdeal :
        Ideal.comap (algebraMap T D) qD.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqD_comap
    letI : IsLocalization.AtPrime (Localization.AtPrime qD.asIdeal) q.asIdeal := by
      simpa [hqD_asIdeal] using
        (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
          (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl)
          (Localization.AtPrime qD.asIdeal) qD.asIdeal)
    let eLoc : Localization.AtPrime q.asIdeal ≃ₐ[T] Localization.AtPrime qD.asIdeal :=
      IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime qD.asIdeal)
    -- The target localization is normal because it agrees with a prime localization of `D`.
    exact
      ⟨Function.Injective.isDomain eLoc.toRingHom eLoc.injective,
        (isIntegrallyClosed_localizationAtPrime qD).of_equiv eLoc.toRingEquiv.symm⟩

end

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.51.10: fibers of a Noetherian algebra over a prime are Noetherian. -/
private theorem fiber_isNoetherianRing {D : Type u} [CommRing D] [Algebra A D]
    [IsNoetherianRing D] (p : PrimeSpectrum A) :
    IsNoetherianRing (p.asIdeal.Fiber D) := by
  -- Commute the tensor factors so the fiber is viewed as an essentially finite type `C`-algebra.
  let _ : Algebra.EssFiniteType D (D ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (D ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing D (D ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (D ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField D).toRingEquiv.symm

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: for a prime of an essentially finite type algebra, the residue
field extension over the contracted prime is again essentially finite type. -/
lemma residueField_extension_essFiniteType [Algebra.EssFiniteType A B] (p' : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) p'
    Algebra.EssFiniteType p.asIdeal.ResidueField p'.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) p'
  -- First pass to the residue field as an essentially finite type `B`-algebra.
  let _ : Algebra.EssFiniteType B p'.asIdeal.ResidueField := inferInstance
  let _ : Algebra.EssFiniteType A p'.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp A B p'.asIdeal.ResidueField
  -- Then descend along the contracted residue-field map.
  exact
    Algebra.EssFiniteType.of_comp A p.asIdeal.ResidueField p'.asIdeal.ResidueField

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: the target fiber test ring over `p'` identifies with the ambient
base change `K ⊗[R] Λ`. -/
noncomputable abbrev fiber_baseChange_ringEquiv
    {R : Type u} {R' : Type u} {Λ : Type u}
    [CommRing R] [CommRing R'] [CommRing Λ]
    [Algebra R Λ] [Algebra R R']
    [Algebra.EssFiniteType R R']
    (p' : PrimeSpectrum R') (K : Type u) [Field K] [Algebra p'.asIdeal.ResidueField K] :
    let _ : Algebra R' K :=
      RingHom.toAlgebra
        ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
    let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
    let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
    K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) ≃+* K ⊗[R] Λ :=
  let _ : Algebra R' K :=
    RingHom.toAlgebra
      ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
  let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
  let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
  -- First cancel the `p'`-fiber, then cancel the remaining base change along `R → R'`.
  ((Algebra.TensorProduct.cancelBaseChange R' p'.asIdeal.ResidueField
      p'.asIdeal.ResidueField K (R' ⊗[R] Λ)).toRingEquiv).trans
    ((Algebra.TensorProduct.cancelBaseChange R R' K K Λ).toRingEquiv)

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: an equality of `R'`-algebra structures on `R' ⊗[R] Λ` transports
regularity of the target test ring. -/
lemma target_tensor_isRegular_of_algebra_eq
    {R : Type u} {R' : Type u} {Λ : Type u}
    [CommRing R] [CommRing R'] [CommRing Λ]
    [Algebra R Λ] [Algebra R R']
    [Algebra.EssFiniteType R R']
    (p' : PrimeSpectrum R') (K : Type u) [Field K] [Algebra p'.asIdeal.ResidueField K]
    {A₁ A₂ : Algebra R' (R' ⊗[R] Λ)} (hA : A₁ = A₂) :
    (let _ : Algebra R' (R' ⊗[R] Λ) := A₁;
      let _ : CommRing (p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
      let _ : CommRing
          (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
      IsRegularRing
        (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ))) →
    (let _ : Algebra R' (R' ⊗[R] Λ) := A₂;
      let _ : CommRing (p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
      let _ : CommRing
          (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
      IsRegularRing
        (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ))) := by
  subst hA
  intro hReg
  exact hReg

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: an equality of `R`-algebra structures on `Λ` transports geometric
regularity of the source fiber. -/
lemma source_fiber_isGeometricallyRegular_of_algebra_eq
    {R : Type u} {Λ : Type u}
    [CommRing R] [CommRing Λ] [Algebra R Λ]
    (p : PrimeSpectrum R) {A₁ A₂ : Algebra R Λ} (hA : A₁ = A₂) :
    (let _ : Algebra R Λ := A₁;
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)) →
    (let _ : Algebra R Λ := A₂;
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)) := by
  subst hA
  intro hGeom
  exact hGeom

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: base change of a regular ring map along an essentially finite type
algebra remains regular. -/
theorem regularRingMap_baseChange_of_essFiniteType
    {R : Type u} {R' : Type u} {Λ : Type u}
    [CommRing R] [CommRing R'] [CommRing Λ]
    [Algebra R Λ] [Algebra R R']
    [Algebra.EssFiniteType R R']
    (h : (algebraMap R Λ).IsRegularRingMap) :
    (algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap := by
  refine
    (RingHom.isRegularRingMap_iff_flat_and_geometricallyRegular_fiber
      (f := algebraMap R' (R' ⊗[R] Λ))).mpr ?_
  constructor
  · let _ : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp <| by
      simpa using h.toFlat
    let _ : Module.Flat R' (R' ⊗[R] Λ) := Module.Flat.baseChange R R' Λ
    -- Flatness survives the tensor base change along `R → R'`.
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · intro p'
    let A₁ : Algebra R' (R' ⊗[R] Λ) := (algebraMap R' (R' ⊗[R] Λ)).toAlgebra
    let A₂ : Algebra R' (R' ⊗[R] Λ) := Algebra.TensorProduct.leftAlgebra
    have hAlgTensor : A₁ = A₂ := by
      apply Algebra.algebra_ext
      intro x
      rfl
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    let φ : p.asIdeal.ResidueField →+* p'.asIdeal.ResidueField :=
      algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
    let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField := inferInstance
    let _ : Algebra.EssFiniteType p.asIdeal.ResidueField p'.asIdeal.ResidueField := by
      simpa [p] using
        residueField_extension_essFiniteType (A := R) (B := R') p'
    -- Route correction: follow the original fiberwise base-change proof, comparing both source
    -- and target test rings with the common ambient tensor product `K ⊗[R] Λ`.
    rw [Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing]
    intro K _ _ _
    let _ : Algebra p.asIdeal.ResidueField K :=
      RingHom.toAlgebra ((algebraMap p'.asIdeal.ResidueField K).comp φ)
    let _ : Algebra R' K :=
      RingHom.toAlgebra
        ((algebraMap p'.asIdeal.ResidueField K).comp (algebraMap R' p'.asIdeal.ResidueField))
    let _ : Algebra R K := RingHom.toAlgebra ((algebraMap R' K).comp (algebraMap R R'))
    let _ : IsScalarTower p.asIdeal.ResidueField p'.asIdeal.ResidueField K :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R' p'.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra.EssFiniteType p.asIdeal.ResidueField K :=
      Algebra.EssFiniteType.comp p.asIdeal.ResidueField p'.asIdeal.ResidueField K
    let _ : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun x ↦ by
        have hmap :
            algebraMap R' p'.asIdeal.ResidueField (algebraMap R R' x) =
              algebraMap p.asIdeal.ResidueField p'.asIdeal.ResidueField
                (algebraMap R p.asIdeal.ResidueField x) := by
          simpa [p] using
            (Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal (algebraMap R R') rfl x).symm
        exact congrArg (algebraMap p'.asIdeal.ResidueField K) hmap
    let hsourceExplicit :
        let _ : Algebra R Λ := (algebraMap R Λ).toAlgebra;
        Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ) :=
      h.isGeometricallyRegular_fiber p
    let hAlgSource : (algebraMap R Λ).toAlgebra = (inferInstance : Algebra R Λ) := by
      apply Algebra.algebra_ext
      intro x
      rfl
    have hsource :
        Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber Λ) :=
      source_fiber_isGeometricallyRegular_of_algebra_eq
        (R := R) (Λ := Λ) (p := p) hAlgSource hsourceExplicit
    have hsourceReg :
        IsRegularRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) :=
      (Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing.mp
        hsource) K
    let eSource :
        K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ ≃+* K ⊗[R] Λ := by
      simpa using
        (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField
          p.asIdeal.ResidueField K Λ).toRingEquiv
    let _ : IsRegularRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) := hsourceReg
    have hKR : IsRegularRing (K ⊗[R] Λ) := by
      -- Cancel the source fiber to reach the common ambient tensor-product model.
      let _ : CommRing (K ⊗[R] Λ) := inferInstance
      let _ : CommRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ) := inferInstance
      let fSource : K ⊗[R] Λ →+* K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber Λ :=
        eSource.symm.toRingHom
      have hfSource : fSource.FaithfullyFlat := by
        exact RingHom.FaithfullyFlat.of_bijective eSource.symm.bijective
      exact isRegularRing_of_faithfullyFlat fSource hfSource
    let _ : IsRegularRing (K ⊗[R] Λ) := hKR
    have htargetA₂ :
        let _ : Algebra R' (R' ⊗[R] Λ) := A₂;
        let _ : CommRing (p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
        let _ : CommRing
            (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance;
        IsRegularRing
          (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := by
      let _ : Algebra R' (R' ⊗[R] Λ) := A₂
      let _ : CommRing (p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance
      let _ : CommRing (K ⊗[R] Λ) := inferInstance
      let _ : CommRing
          (K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ)) := inferInstance
      let eTarget :
          K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) ≃+* K ⊗[R] Λ := by
        simpa [Ideal.Fiber] using
          fiber_baseChange_ringEquiv (R := R) (R' := R') (Λ := Λ) p' (K := K)
      -- Descend regularity from the ambient tensor-product model to the target fiber.
      let fTarget :
          K ⊗[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] Λ) →+* K ⊗[R] Λ :=
        eTarget.toRingHom
      have hfTarget : fTarget.FaithfullyFlat := by
        exact RingHom.FaithfullyFlat.of_bijective eTarget.bijective
      exact isRegularRing_of_faithfullyFlat fTarget hfTarget
    exact
      target_tensor_isRegular_of_algebra_eq
        (R := R) (R' := R') (Λ := Λ) (p' := p') (K := K)
        (A₁ := A₂) (A₂ := A₁) hAlgTensor.symm htargetA₂

/-- Helper for Lemma 15.51.10: the explicit source tensor model `B ⊗[A] κ(p)` identifies with the
actual fiber of `B` as a ring. -/
noncomputable abbrev explicit_fiber_model_algEquiv (p : PrimeSpectrum A) :
    let κ := p.asIdeal.ResidueField
    let _ : Algebra κ (B ⊗[A] κ) := Algebra.TensorProduct.rightAlgebra
    (B ⊗[A] κ) ≃ₐ[κ] p.asIdeal.Fiber B := by
  let κ := p.asIdeal.ResidueField
  -- Use the right-ordered tensor equivalence so the `κ(p)`-algebra structure stays explicit.
  simpa [Ideal.Fiber] using (Algebra.TensorProduct.commRight A κ B).symm

/-- Helper for Lemma 15.51.10: the explicit source tensor model `B ⊗[A] κ(p)` identifies with the
actual fiber of `B` as a ring. -/
noncomputable abbrev explicit_fiber_model_ringEquiv (p : PrimeSpectrum A) :
    let κ := p.asIdeal.ResidueField
    (B ⊗[A] κ) ≃+* p.asIdeal.Fiber B := by
  exact (explicit_fiber_model_algEquiv (A := A) (B := B) p).toRingEquiv

/-- Helper for Lemma 15.51.10: tensoring the explicit source fiber model with `K` in the
`K ⊗[κ(p)] -` orientation identifies it with the tensor product of the actual fiber as a ring. -/
noncomputable abbrev explicit_fiber_tensor_source_algEquiv (p : PrimeSpectrum A)
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K] :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let _ : CommRing S₀ := inferInstance
    let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
    (K ⊗[κ] S₀) ≃+* K ⊗[κ] p.asIdeal.Fiber B := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let _ : CommRing S₀ := inferInstance
  let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  -- Keep both tensor products in the same `K ⊗[κ] -` orientation before any factor swap.
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[κ] K)
      (explicit_fiber_model_algEquiv (A := A) (B := B) p)).toRingEquiv

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Helper for Lemma 15.51.10: geometric normality of the actual fiber transports to the explicit
tensor model `(B ⊗[A] κ(p)) ⊗[κ(p)] K`. -/
lemma explicit_fiber_tensor_normal_of_geometricNormal (p : PrimeSpectrum A)
    (hfiber : IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let _ : CommRing S₀ := inferInstance
    let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
    let U₀ := S₀ ⊗[κ] K
    IsNormalRing U₀ := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let _ : CommRing S₀ := inferInstance
  let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  let U₁ := K ⊗[κ] S₀
  letI : IsGeometricallyNormal κ (p.asIdeal.Fiber B) := hfiber
  have hfiberTensor : IsNormalRing (K ⊗[κ] p.asIdeal.Fiber B) :=
    IsGeometricallyNormal.isNormalRing_baseChange (k := κ) (R := p.asIdeal.Fiber B) K
  letI : IsNormalRing (K ⊗[κ] p.asIdeal.Fiber B) := hfiberTensor
  have hsourceTensor : IsNormalRing U₁ := by
    -- First transport normality from the actual fiber to the explicit source tensor model.
    exact
      isNormalRing_of_ringEquiv
        ((explicit_fiber_tensor_source_algEquiv (A := A) (B := B) (p := p) (K := K)).symm)
  letI : IsNormalRing U₁ := hsourceTensor
  -- Route correction: commute the tensor factors only after the same-orientation comparison has
  -- moved normality onto `K ⊗[κ(p)] (B ⊗[A] κ(p))`.
  exact isNormalRing_of_ringEquiv (Algebra.TensorProduct.commRight κ K S₀).toRingEquiv

omit [Algebra A C] [IsScalarTower A B C] [IsNoetherianRing A] [IsNoetherianRing B]
  [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: base changing the regular map `B → C` to the explicit fiber model
`B ⊗[A] κ(p)` stays regular. -/
lemma fiber_regularRingMap [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A) :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let D₀ := S₀ ⊗[B] C
    let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
    let _ : CommRing S₀ := inferInstance
    let _ : CommRing D₀ := inferInstance
    let _ : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
    (algebraMap S₀ D₀).IsRegularRingMap := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  -- Route correction: the source proof proves regularity on the explicit model `S₀`, where the
  -- essentially-finite-type base change theorem applies without any transport search.
  simpa [κ, S₀, D₀] using
    regularRingMap_baseChange_of_essFiniteType
      (R := B) (R' := S₀) (Λ := C) (inferInstance : (algebraMap B C).IsRegularRingMap)

omit [Algebra A C] [IsScalarTower A B C] [IsNoetherianRing A] [IsNoetherianRing B]
  [IsNoetherianRing C] in
/-- Helper for Lemma 15.51.10: after a finite purely inseparable residue-field extension, the
explicit regular fiber map remains regular on the base-changed tensor model. -/
lemma fiber_base_changed_regularRingMap [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A)
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    let κ := p.asIdeal.ResidueField
    let S₀ := B ⊗[A] κ
    let D₀ := S₀ ⊗[B] C
    let U₀ := S₀ ⊗[κ] K
    let _ : CommRing S₀ := inferInstance
    let _ : CommRing D₀ := inferInstance
    let _ : CommRing U₀ := inferInstance
    let _ : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra U₀ (U₀ ⊗[S₀] D₀) := Algebra.TensorProduct.leftAlgebra
    (algebraMap U₀ (U₀ ⊗[S₀] D₀)).IsRegularRingMap := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  let U₀ := S₀ ⊗[κ] K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra U₀ (U₀ ⊗[S₀] D₀) := Algebra.TensorProduct.leftAlgebra
  have hSD : (algebraMap S₀ D₀).IsRegularRingMap :=
    fiber_regularRingMap (A := A) (B := B) (C := C) p
  -- After fixing the fiber model `S`, clause `(C)` only needs one more base change along
  -- `κ(p) → K`.
  simpa [κ, S₀, D₀, U₀] using
    regularRingMap_baseChange_of_essFiniteType
      (R := S₀) (R' := U₀) (Λ := D₀) hSD

/-- Helper for Lemma 15.51.10: the explicit target fiber model `(B ⊗[A] κ(p)) ⊗[B] C` identifies
with the actual fiber of `C` over `p`. -/
noncomputable abbrev explicit_target_fiber_algEquiv
    (p : PrimeSpectrum A) := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  -- This is the second pushout cancellation in the source proof.
  simpa [Ideal.Fiber] using
    (Algebra.IsPushout.cancelBaseChangeAlg A κ B S₀ C)

/-- Helper for Lemma 15.51.10: the explicit tensor base change of a fiber ring agrees with the
actual tensor base change of the fiber after the standard pushout cancellations. -/
noncomputable abbrev tensor_fiber_baseChange_cancel
    (p : PrimeSpectrum A) (K : Type u) [Field K] [Algebra p.asIdeal.ResidueField K] := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  let U₀ := S₀ ⊗[κ] K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  let e₁ : (U₀ ⊗[S₀] D₀) ≃+* K ⊗[κ] D₀ :=
    (Algebra.IsPushout.cancelBaseChangeAlg κ K S₀ U₀ D₀).toRingEquiv
  let e₂κ : D₀ ≃ₐ[κ] p.asIdeal.Fiber C :=
    explicit_target_fiber_algEquiv (A := A) (B := B) (C := C) p
  let e₂ : K ⊗[κ] D₀ ≃+* K ⊗[κ] p.asIdeal.Fiber C :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[κ] K)
      e₂κ).toRingEquiv
  -- Compare first with the explicit pushout model, then cancel the fiber itself.
  exact e₁.trans e₂

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.51.10: after a finite purely inseparable residue-field extension, the
target fiber tensor ring is normal if the source fiber is geometrically normal. -/
lemma target_fiber_tensor_normal_of_geometricallyNormal
    [(algebraMap B C).IsRegularRingMap] (p : PrimeSpectrum A)
    (hfiber : IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    {K : Type u} [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] [IsPurelyInseparable p.asIdeal.ResidueField K] :
    IsNormalRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber C) := by
  let κ := p.asIdeal.ResidueField
  let S₀ := B ⊗[A] κ
  let D₀ := S₀ ⊗[B] C
  let U₀ := S₀ ⊗[κ] K
  letI : CommRing S₀ := inferInstance
  letI : CommRing D₀ := inferInstance
  letI : CommRing U₀ := inferInstance
  letI : Algebra B S₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra κ S₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S₀ U₀ := Algebra.TensorProduct.leftAlgebra
  letI : IsNoetherianRing S₀ := Algebra.EssFiniteType.isNoetherianRing B S₀
  letI : IsNoetherianRing U₀ := Algebra.EssFiniteType.isNoetherianRing S₀ U₀
  let T₀ := p.asIdeal.Fiber C ⊗[κ] K
  letI : CommRing T₀ := inferInstance
  letI : IsNoetherianRing (p.asIdeal.Fiber C) := fiber_isNoetherianRing (A := A) (D := C) p
  letI : IsNoetherianRing T₀ := Algebra.EssFiniteType.isNoetherianRing (p.asIdeal.Fiber C) T₀
  let eTargetNoeth : T₀ ≃+* (K ⊗[κ] p.asIdeal.Fiber C) :=
    (Algebra.TensorProduct.commRight κ K (p.asIdeal.Fiber C)).symm.toRingEquiv
  letI : IsNoetherianRing (K ⊗[κ] p.asIdeal.Fiber C) :=
    isNoetherianRing_of_ringEquiv T₀ eTargetNoeth
  letI : IsNormalRing U₀ :=
    explicit_fiber_tensor_normal_of_geometricNormal
      (A := A) (B := B) p hfiber (K := K)
  have hbase : (algebraMap U₀ (U₀ ⊗[S₀] D₀)).IsRegularRingMap := by
    -- Base change the explicit regular fiber map `S₀ → D₀` along `κ(p) → K`.
    simpa [κ, S₀, D₀, U₀] using
      fiber_base_changed_regularRingMap (A := A) (B := B) (C := C) (p := p) (K := K)
  letI : (algebraMap U₀ (U₀ ⊗[S₀] D₀)).IsRegularRingMap := hbase
  let e : (U₀ ⊗[S₀] D₀) ≃+* (K ⊗[κ] p.asIdeal.Fiber C) :=
    tensor_fiber_baseChange_cancel (A := A) (B := B) (C := C) p K
  letI : IsNoetherianRing (U₀ ⊗[S₀] D₀) :=
    isNoetherianRing_of_ringEquiv (K ⊗[κ] p.asIdeal.Fiber C) e.symm
  have hExplicit : IsNormalRing (U₀ ⊗[S₀] D₀) := by
    -- Ascend normality along the regular base-changed fiber map.
    exact isNormalRing_of_regularRingMap (algebraMap U₀ (U₀ ⊗[S₀] D₀))
  letI : IsNormalRing (U₀ ⊗[S₀] D₀) := hExplicit
  -- Transport the explicit tensor-model result to the actual tensor product of the target fiber.
  exact isNormalRing_of_ringEquiv e

-- Proof sketch: for `p : Spec(A)`, reduce geometric normality of the fiber of `A → C` to
-- normality after finite purely inseparable residue-field extension, base change the regular map
-- on fibers, and apply `Lemma 15.42.2` to that regular base-changed map.
omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.51.10: geometric normality ascends from the fibers of `A → B` to those of
`A → C` along a regular map `B → C`. -/
theorem fibers_areGeometricallyNormal_of_flat_of_regular [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hfiber : ∀ p : PrimeSpectrum A, IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber C) := by
  intro p
  refine ⟨?_⟩
  -- Route correction: clause `(C)` is reduced to the finite purely inseparable test for
  -- geometric normality, so only tensor-normality on the target fiber remains.
  exact
    (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable
      (k := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber C)).2 <| by
        intro K _ _ _ _
        -- The tensor-level normality statement is the regular-ascent step on the fiber model.
        exact
          target_fiber_tensor_normal_of_geometricallyNormal
            (A := A) (B := B) (C := C) p (hfiber p)

end

section

variable {κ R S : Type u}
variable [Field κ] [CommRing R] [CommRing S]
variable [Algebra κ R] [Algebra κ S] [Algebra R S]
variable [Module.FaithfullyFlat R S]

/-- Helper for Lemma 15.51.10: after tensoring a faithfully flat `κ`-algebra map by `K`,
normality descends from `K ⊗[κ] S` to `K ⊗[κ] R`. -/
theorem tensor_product_normal_of_faithfullyFlat
    (hcomm : ∀ x : κ, algebraMap κ S x = (algebraMap R S) ((algebraMap κ R) x))
    (K : Type u) [Field K] [Algebra κ K]
    (hKS : IsNormalRing (K ⊗[κ] S)) :
    IsNormalRing (K ⊗[κ] R) := by
  letI : IsScalarTower κ R S := IsScalarTower.of_algebraMap_eq hcomm
  letI : Algebra R (K ⊗[κ] R) := Algebra.TensorProduct.rightAlgebra
  letI : IsNormalRing (K ⊗[κ] S) := hKS
  let D := (K ⊗[κ] R) ⊗[R] S
  letI : CommRing D := inferInstance
  letI : Algebra (K ⊗[κ] R) D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  let f : (K ⊗[κ] R) →+* D := algebraMap (K ⊗[κ] R) D
  have hf : f.FaithfullyFlat := by
    letI : Module.FaithfullyFlat (K ⊗[κ] R) D := inferInstance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃ₐ[K] (K ⊗[κ] S) :=
    Algebra.IsPushout.cancelBaseChangeAlg κ K R (K ⊗[κ] R) S
  have hD : IsNormalRing D := by
    -- The tensor square is the pushout model of `K ⊗[κ] S`.
    exact isNormalRing_of_ringEquiv e.toRingEquiv.symm
  letI : IsNormalRing D := hD
  -- Descend normality along the faithfully flat tensor extension.
  exact isNormalRing_of_faithfullyFlat f hf

end

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]

-- Proof sketch: first descend faithful flatness from `B → C` to the induced map on the closed
-- fibers, then tensor that map by the finite purely inseparable extension `ResidueField A → K`.
-- The resulting tensor square is the source-faithful closed-fiber pushout, so
-- `Algebra.IsPushout.cancelBaseChangeAlg` identifies it with
-- `K ⊗[ResidueField A] ((maximalIdeal A).Fiber C)`, and ordinary normality descends along the
-- faithfully flat composite.
omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [IsLocalRing B] [IsLocalRing C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] in
/-- Helper for Lemma 15.51.10: after tensoring the closed fiber with a finite purely inseparable
residue-field extension, normality descends along the induced faithfully flat map on closed
fibers. -/
theorem closedFiber_tensor_normal_of_faithfullyFlat
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (K : Type u) [Field K] [Algebra (ResidueField A) K]
    [FiniteDimensional (ResidueField A) K] [IsPurelyInseparable (ResidueField A) K]
    (hK : IsNormalRing (K ⊗[ResidueField A] ((maximalIdeal A).Fiber C))) :
    IsNormalRing (K ⊗[ResidueField A] ((maximalIdeal A).Fiber B)) := by
  letI : Algebra B ((maximalIdeal A).Fiber B) := Algebra.TensorProduct.rightAlgebra
  -- First descend faithful flatness from `B → C` to the induced map on the closed fibers.
  let D₀ := ((maximalIdeal A).Fiber B) ⊗[B] C
  letI : CommRing D₀ := inferInstance
  letI : Algebra ((maximalIdeal A).Fiber B) D₀ := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (ResidueField A) D₀ :=
    RingHom.toAlgebra
      ((algebraMap ((maximalIdeal A).Fiber B) D₀).comp
        (algebraMap (ResidueField A) ((maximalIdeal A).Fiber B)))
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
  let f₀ : ((maximalIdeal A).Fiber B) →+* D₀ := algebraMap ((maximalIdeal A).Fiber B) D₀
  have hf₀ : f₀.FaithfullyFlat := by
    letI : Module.FaithfullyFlat ((maximalIdeal A).Fiber B) D₀ := inferInstance
    simpa [f₀] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f₀.FaithfullyFlat)
  let e₀ :=
    Algebra.IsPushout.cancelBaseChangeAlg A ((maximalIdeal A).ResidueField)
      B ((maximalIdeal A).Fiber B) C
  let g₀ : D₀ →+* ((maximalIdeal A).Fiber C) := e₀.toRingHom
  have hg₀ : g₀.FaithfullyFlat := by
    simpa [g₀] using
      (RingHom.FaithfullyFlat.of_bijective e₀.bijective : g₀.FaithfullyFlat)
  have hff₀ : (g₀.comp f₀).FaithfullyFlat := by
    -- The closed-fiber comparison map is a base change of `B → C` followed by a pushout isomorphism.
    change (RingHom.comp g₀ f₀).FaithfullyFlat
    exact RingHom.FaithfullyFlat.stableUnderComposition f₀ g₀ hf₀ hg₀
  letI : Algebra ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C) :=
    RingHom.toAlgebra (g₀.comp f₀)
  letI : Module.FaithfullyFlat ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp (by simpa [f₀, g₀] using hff₀)
  -- The closed fiber is the maximal-ideal fiber, so apply the generic tensor descent helper.
  have hcomm : ∀ x : ResidueField A,
      algebraMap (ResidueField A) ((maximalIdeal A).Fiber C) x =
        (algebraMap ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C))
          ((algebraMap (ResidueField A) ((maximalIdeal A).Fiber B)) x) := by
    intro x
    let y : (maximalIdeal A).ResidueField :=
      algebraMap (ResidueField A) ((maximalIdeal A).ResidueField) x
    change algebraMap (ResidueField A) ((maximalIdeal A).Fiber C) x =
      e₀ ((algebraMap (ResidueField A) D₀) x)
    simpa [y] using (e₀.commutes y).symm
  exact
    tensor_product_normal_of_faithfullyFlat
      (κ := ResidueField A) (R := ((maximalIdeal A).Fiber B))
      (S := ((maximalIdeal A).Fiber C)) hcomm K hK

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [IsLocalRing B] [IsLocalRing C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] in
/-- Helper for Lemma 15.51.10: geometric normality descends on the closed fiber along a
faithfully flat local extension. -/
theorem isGeometricallyNormal_closedFiberDescent
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC : IsGeometricallyNormal (ResidueField A) ((maximalIdeal A).Fiber C)) :
    IsGeometricallyNormal (ResidueField A) ((maximalIdeal A).Fiber B) := by
  letI : IsGeometricallyNormal (ResidueField A) ((maximalIdeal A).Fiber C) := hC
  refine ⟨?_⟩
  -- Route correction: use the finite purely inseparable criterion for geometric normality, so the
  -- closed-fiber descent theorem only has to handle the tensor-normality test rings.
  exact
    (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable
      (k := ResidueField A) (A := ((maximalIdeal A).Fiber B))).2 <| by
        intro K _ _ _ _
        -- Evaluate geometric normality of the target closed fiber on the chosen finite purely
        -- inseparable residue-field extension, then descend ordinary normality.
        have hKC : IsNormalRing (K ⊗[ResidueField A] ((maximalIdeal A).Fiber C)) :=
          IsGeometricallyNormal.isNormalRing_baseChange
            (k := ResidueField A) (R := ((maximalIdeal A).Fiber C)) K
        exact
          closedFiber_tensor_normal_of_faithfullyFlat
            (A := A) (B := B) (C := C) hBC K hKC

end

-- Proof sketch: property `(A)` is immediate from the definition of geometric normality under
-- finitely generated base change. Property `(B)` is the local criterion for normality. Property
-- `(C)` is ascent of normality along regular maps on each fiber, using `Lemma 15.42.2`. Property
-- `(D)` is faithfully flat descent of normality on fibers, using `Lemma 10.164.3`. Property `(E)`
-- is invariance of geometric normality under separable algebraic extension of the ground field,
-- using `Lemma 10.165.6`.
/-- Lemma 15.51.10: the field-algebra property `IsGeometricallyNormal` satisfies the formal-fiber
axioms `(A)`, `(B)`, `(C)`, `(D)`, and `(E)`. -/
@[stacks 0BIX]
instance isGeometricallyNormal_hasPropertiesABCDE :
    IsGeometricallyNormalProperty.HasPropertiesABCDE where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_baseChange_of_finitelyGeneratedFieldExtension hA
  localizationCriterion := by
    intro k A _ _ _ _
    exact isGeometricallyNormal_iff_forall_localization_atPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hB q
    exact fibers_areGeometricallyNormal_of_flat_of_regular hB q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact isGeometricallyNormal_closedFiberDescent hBC hC
  separableBaseChange := by
    intro k k' A _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

end Algebra
