import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_83_1 (from Chap15) -/
open CategoryTheory

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/- Domain-style sampling:
* primary domain: commutative algebra of pseudo-coherent and perfect ring maps;
* sampled owner declarations:
  `RingHom.FiniteType`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `ModuleHasFiniteTorDimension`,
  `RingHom.IsRegularRingMap`;
* best owner abstraction: this file is the `source-facing` owner for predicates on an actual ring
  hom `f : A →+* B`, matching the chapter owner style of `RingHom.IsRegularRingMap`; the
  module-level owners above provide the canonical primitive data;
* primitive vs. derived:
  primitive data are finite type, relative pseudo-coherence of the target ring over the base, and
  finite tor dimension of the target as a base module;
  derived API is any later polynomial-presentation or perfect-module characterization.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsPseudoCoherentRingMap` and `RingHom.IsPerfectRingMap`;
* `core/canonical`: `RingHom.FiniteType`, `ModuleCat.IsPseudoCoherentRelativeTo`, and
  `ModuleHasFiniteTorDimension`;
* `bridge/view`: for `f = algebraMap A B`, the target ring regarded as the canonical module
  objects `ModuleCat.of B B` and `ModuleCat.of A B`.
-/

/-- Definition 15.83.1 (1): a ring map `f : A →+* B` is pseudo-coherent if it is of finite type
and `B`, viewed as a `B`-module, is pseudo-coherent relative to `A`. -/
@[mk_iff isPseudoCoherentRingMap_iff_finiteType_and_isPseudoCoherentRelativeTo]
class IsPseudoCoherentRingMap : Prop where
  /-- A pseudo-coherent ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target ring, viewed as a module over itself, is pseudo-coherent relative to the base. -/
  isPseudoCoherentRelativeTo :
    let _ := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

/-- Definition 15.83.1 (2): a ring map `f : A →+* B` is perfect if it is pseudo-coherent and `B`,
viewed as an `A`-module, has finite tor dimension. -/
@[mk_iff isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension]
class IsPerfectRingMap : Prop extends IsPseudoCoherentRingMap f where
  /-- The target ring has finite tor dimension as a module over the base ring. -/
  hasFiniteTorDimension :
    let _ := f.toAlgebra
    ModuleHasFiniteTorDimension (ModuleCat.of A B)

attribute [instance] IsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
attribute [instance] IsPerfectRingMap.hasFiniteTorDimension

section

variable (A : Type u) [CommRing A]

/-- The identity map of a commutative ring is pseudo-coherent. -/
instance : (RingHom.id A).IsPseudoCoherentRingMap where
  finiteType := RingHom.FiniteType.id A
  isPseudoCoherentRelativeTo := by
    sorry

/-- The identity map of a commutative ring is perfect. -/
instance : (RingHom.id A).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := inferInstance
  hasFiniteTorDimension := by
    sorry

end

end RingHom

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

instance finiteType_of_isPseudoCoherentRingMap : Algebra.FiniteType A B := by
  exact
    RingHom.finiteType_algebraMap.mp
      (inferInstance : (algebraMap A B).IsPseudoCoherentRingMap).finiteType

attribute [instance 100] finiteType_of_isPseudoCoherentRingMap

end

end Algebra

/-! ### Lemma_15_83_2 (from Chap15) -/
universe u

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling for Lemma 15.83.2:
- primary domain: commutative algebra of perfect ring maps, compared with perfect modules over a
  surjective polynomial presentation;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `ModuleCat.IsPerfect`,
  `Module.FinitePresentationRelativeTo`,
  `ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms`;
- best owner abstraction: the source-facing theorem belongs on the ring-map owner
  `(algebraMap A B).IsPerfectRingMap`, while the polynomial-presentation side should speak
  directly in the canonical module owner `ModuleCat.IsPerfect`, not via the restriction functor as
  public data;
- primitive vs. derived:
  primitive data are a surjective polynomial presentation `α : A[x₁, ..., xₙ] → B` and the
  induced `A[x₁, ..., xₙ]`-module structure on `B`;
  derived API is the finite projective resolution reformulation from Lemma `15.75.3`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `RingHom.IsPerfectRingMap` and `ModuleCat.IsPerfect`;
- `bridge/view`: restriction of scalars along a polynomial presentation.

The statement should therefore keep the source-facing equivalence while using the induced module
structure on `B` as the public owner-level formulation, rather than the functorial bridge term.
-/

-- Proof sketch: if `A → B` is perfect, then it is finite type, so choose a surjective polynomial
-- presentation `MvPolynomial (Fin n) A →ₐ[A] B`. The pseudo-coherence and finite tor dimension
-- hypotheses then show that `B`, viewed through this presentation, is a perfect module over the
-- polynomial ring. Conversely, if such a presentation makes the restricted
-- `MvPolynomial (Fin n) A`-module `B` perfect, then `A → B` is pseudo-coherent and `B` has
-- finite tor dimension over `A`, hence the ring map is perfect.
/-- Lemma 15.83.2: a ring map `A → B` is perfect if and only if there exists a surjective
polynomial presentation `MvPolynomial (Fin n) A →ₐ[A] B` such that `B`, viewed as a module over
`MvPolynomial (Fin n) A`, is perfect. By Lemma `15.75.3`, this is equivalent to requiring a
finite resolution by finite projective `MvPolynomial (Fin n) A`-modules. -/
theorem isPerfectRingMap_iff_exists_polynomialPresentation_with_perfect_restrictedModule :
    (algebraMap A B).IsPerfectRingMap ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B),
        Function.Surjective α ∧
          let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
          (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := sorry

end

end Algebra

/-! ### Lemma_15_83_3 (from Chap15) -/
universe u

namespace Algebra

section

variable {R : Type u} {A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

/- Domain-style sampling for Lemma 15.83.3:
- primary domain: pseudo-coherent ring maps and relative pseudo-coherent modules over finite type
  algebras above a Noetherian base;
- sampled owner declarations:
  `RingHom.IsPseudoCoherentRingMap`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `Module.isPseudoCoherentRelativeTo_iff_finite`;
- best owner abstraction: `RingHom.IsPseudoCoherentRingMap` on the structure map `algebraMap R A`;
- primitive vs. derived:
  primitive data are the finite type map `R → A` and the owner field
  `(ModuleCat.of A A).IsPseudoCoherentRelativeTo R`;
  the derived API is the Noetherian finite-type criterion
  `Module.isPseudoCoherentRelativeTo_iff_finite`, specialized to the regular module `A`;
- source/core/bridge triage:
  `source-facing`: the numbered lemma asserting the Noetherian finite-type criterion;
  `core/canonical`: `RingHom.IsPseudoCoherentRingMap` and
    `Module.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the bundled/unbundled module identification for `A` viewed as an `A`-module.
-/
/-- Lemma 15.83.3: a finite type ring map out of a Noetherian ring is pseudo-coherent. -/
instance isPseudoCoherentRingMap_of_finiteType_of_isNoetherianRing :
    (algebraMap R A).IsPseudoCoherentRingMap where
  finiteType := RingHom.finiteType_algebraMap.mpr inferInstance
  isPseudoCoherentRelativeTo := by
    have hfiniteType : (algebraMap R A).FiniteType :=
      RingHom.finiteType_algebraMap.mpr inferInstance
    let _ : Algebra R A := (algebraMap R A).toAlgebra
    let _ : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hfiniteType
    simpa [Module.IsPseudoCoherentRelativeTo] using
      (Module.isPseudoCoherentRelativeTo_iff_finite : Module.IsPseudoCoherentRelativeTo R A A ↔
        Module.Finite A A).2 (Module.Finite.self A)

end

end Algebra

/-! ### Lemma_15_83_4 (from Chap15) -/
universe u

open CategoryTheory

namespace Algebra

/- Domain-style sampling for Lemma 15.83.4:
- primary domain: perfect ring maps for flat finitely presented algebras;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `CategoryTheory.ModuleHasFiniteTorDimension`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`;
- best owner abstraction: the source-facing conclusion belongs on the ring-map owner
  `(algebraMap A B).IsPerfectRingMap`; pseudo-coherence and finite Tor dimension should be derived
  from the canonical chapter owners rather than by a local wrapper;
- primitive vs. derived:
  primitive public data are the flatness and finite-presentation instances on `A → B`;
  derived API is the perfectness instance, whose fields come from the chapter owner
  `RingHom.IsPseudoCoherentRingMap` and the zero-step Tor-dimension bridge
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`.

Source/core/bridge triage:
- `source-facing`: the instance below;
- `core/canonical`: `RingHom.IsPerfectRingMap`, `RingHom.IsPseudoCoherentRingMap`,
  `ModuleHasFiniteTorDimension`;
- `bridge/view`: the zero-step equivalence between module flatness and tor dimension at most `0`.
-/
/- Proof sketch: the pseudo-coherence field is the substantive part of the source argument,
obtained by descending the flat finitely presented map to a flat finite type model over a finite
type `ℤ`-algebra and applying the pseudo-coherence ascent/descent results from `15.82`. The finite
Tor-dimension field is the flat-implies-tor-dimension-`0` clause for the canonical module
`ModuleCat.of A B`. -/
/-- Lemma 15.83.4: a ring map `A → B` which is flat and of finite presentation is perfect. -/
instance isPerfectRingMap_of_flat_of_finitePresentation
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] : (algebraMap A B).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := by
    sorry
  hasFiniteTorDimension := by
    sorry

end Algebra

/-! ### Lemma_15_83_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

namespace Algebra

/- Domain-style sampling for Lemma 15.83.5:
- primary domain: perfect ring maps out of regular rings of finite Krull dimension;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `Ring.KrullDimLE`,
  `RingHom.IsPseudoCoherentRingMap`,
  `IsRegularRing`,
  `IsFiniteGlobalDimensionRing`,
  `globalDimension`;
- best owner abstraction: `RingHom.IsPerfectRingMap` on `algebraMap A B` is the owner of the
  conclusion, while `IsRegularRing`, `Ring.KrullDimLE`, `IsFiniteGlobalDimensionRing`, and
  `globalDimension` are the chapter owners for the finite-dimensional regularity input and its
  finite-global-dimension consequence;
- primitive vs. derived:
  the source-facing input is `[IsRegularRing A]` together with the canonical finite-dimensional
  bridge `∃ d : ℕ, Ring.KrullDimLE d A`;
  the derived API is pseudo-coherence from Lemma `15.83.3` and finite tor dimension from
  finite global dimension via Lemma `15.67.19`;
- source/core/bridge triage:
  `source-facing`: the theorem below with the canonical finite-dimension bridge;
  `core/canonical`: `RingHom.IsPerfectRingMap`, `Ring.KrullDimLE`, `IsRegularRing`,
    `IsFiniteGlobalDimensionRing`, `globalDimension`;
  `bridge/view`: the private proof-only passage from a finite Krull-dimension bound to the exact
    dimension witness required by `finiteGlobalDimension_regularRing_localizations_tfae`.
-/
private theorem isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE
    (A : Type u) [CommRing A] [IsRegularRing A] [Nontrivial A]
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    IsFiniteGlobalDimensionRing A := by
  obtain ⟨d, hd⟩ := hfinite
  have hneTop : ringKrullDim A ≠ ⊤ := by
    exact ne_of_lt
      (lt_of_le_of_lt (Ring.krullDimLE_iff.mp hd)
        (lt_top_iff_ne_top.mpr (by
          intro htop
          exact ENat.coe_ne_top d (WithBot.coe_eq_top.mp htop))))
  have hbot : ringKrullDim A ≠ ⊥ := by
    exact bot_lt_iff_ne_bot.mp (lt_of_lt_of_le (by simp) ringKrullDim_nonneg_of_nontrivial)
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hnneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop
    exact hneTop (by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop)
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hnneTop).symm
  have hdim : ringKrullDim A = n := by
    calc
      ringKrullDim A = (ringKrullDim A).unbot hbot := (WithBot.coe_unbot (ringKrullDim A) hbot).symm
      _ = n := hdim'
  have hregular : IsRegularRing A ∧ ringKrullDim A = n := ⟨inferInstance, hdim⟩
  rcases (((finiteGlobalDimension_regularRing_localizations_tfae n).out 1 0).mp
      hregular) with ⟨hA, _⟩
  exact hA

-- Proof sketch: by Lemma `10.110.8`, a regular ring of finite dimension has finite global
-- dimension. Hence the canonical instance chain
-- `HasGlobalDimensionLE A d ⟹ HasWeakDimensionLE A d ⟹ ModuleHasTorDimensionLE (ModuleCat.of A B) d`
-- gives finite tor dimension for `B`, while Lemma `15.83.3` gives pseudo-coherence for the
-- finite type map `A → B`.
/-- Lemma 15.83.5: a finite type ring map `A → B` with `A` regular of finite Krull dimension is a
perfect ring map. The finite-dimensional hypothesis is carried by the canonical bridge
`∃ d : ℕ, Ring.KrullDimLE d A`. -/
theorem isPerfectRingMap_of_finiteType_of_isRegularRing_of_finiteDimension
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B] (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    (algebraMap A B).IsPerfectRingMap := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hA =>
      letI : Subsingleton A := hA
      letI : Subsingleton B := Algebra.subsingleton A B
      haveI : HasGlobalDimensionLE A 0 := {
        hasProjectiveDimensionLE M := by
          letI : Subsingleton M := Module.subsingleton A M
          have hM : Limits.IsZero M := ModuleCat.isZero_of_subsingleton M
          letI : HasProjectiveDimensionLT M 0 := hM.hasProjectiveDimensionLT_zero
          exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance }
      refine
        { toIsPseudoCoherentRingMap := inferInstance
          hasFiniteTorDimension := by
            let _ : Algebra A B := (algebraMap A B).toAlgebra
            have hwd : HasWeakDimensionLE A 0 := inferInstance
            have htor : ModuleHasTorDimensionLE (ModuleCat.of A B) 0 :=
              hwd.hasTorDimensionLE (ModuleCat.of A B)
            refine ⟨0, 0, ?_⟩
            simpa [ModuleHasTorDimensionLE] using htor }
  | inr hA =>
      letI : Nontrivial A := hA
      letI : IsFiniteGlobalDimensionRing A :=
        isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE A hfinite
      refine
        { toIsPseudoCoherentRingMap := inferInstance
          hasFiniteTorDimension := by
            let _ : Algebra A B := (algebraMap A B).toAlgebra
            have hwd : HasWeakDimensionLE A (globalDimension A) := inferInstance
            have htor : ModuleHasTorDimensionLE (ModuleCat.of A B) (globalDimension A) :=
              hwd.hasTorDimensionLE (ModuleCat.of A B)
            refine ⟨-(globalDimension A : ℤ), 0, ?_⟩
            simpa [ModuleHasTorDimensionLE] using htor }

end Algebra

/-! ### Lemma_15_83_6 (from Chap15) -/
universe u

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

/- Domain-style sampling for Lemma 15.83.6:
- primary domain: commutative algebra of local complete intersection and perfect ring maps;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `Algebra.isPerfectRingMap_of_flat_of_finitePresentation`;
- best owner abstraction: both the source hypothesis and the target conclusion live on the
  canonical ring-map owners `RingHom.IsLocalCompleteIntersection` and
  `RingHom.IsPerfectRingMap` for `algebraMap A B`; a polynomial presentation from Definition
  `15.33.2` is bridge data only and should not appear in the public API here;
- primitive vs. derived:
  the primitive public datum is only the owner hypothesis
  `[RingHom.IsLocalCompleteIntersection (algebraMap A B)]`;
  the derived API is the perfectness instance and its downstream pseudo-coherence and finite Tor
  dimension consequences.

Source/core/bridge triage:
- `source-facing`: the implication below that a local complete intersection ring map is perfect;
- `core/canonical`: `RingHom.IsLocalCompleteIntersection` and `RingHom.IsPerfectRingMap`;
- `bridge/view`: any chosen finite polynomial presentation witnessing the local complete
  intersection condition, used only in the proof.
-/

-- Proof sketch: apply Definition `15.33.2` to choose a finite polynomial presentation
-- `A[x₁, …, xₙ] ↠ B` whose kernel ideal is Koszul-regular. By Lemma `15.83.2`, it is enough to
-- show that `B` is a perfect module over the polynomial ring. Lemma `15.75.12` reduces this to a
-- local statement on the source polynomial ring, where Definition `15.32.1` lets one replace the
-- kernel ideal by a Koszul-regular generating sequence. Such a sequence gives a finite free, hence
-- finite projective, resolution of the quotient module, so Lemma `15.75.3` yields perfection.
/-- Lemma 15.83.6: a local complete intersection ring map is perfect. -/
instance isPerfectRingMap_of_isLocalCompleteIntersection :
    (algebraMap A B).IsPerfectRingMap := sorry

end

end Algebra

/-! ### Lemma_15_83_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [(algebraMap R A).IsPseudoCoherentRingMap]

/- Domain-style sampling for Lemma 15.83.7:
- primary domain: comparison between relative pseudo-coherence over `R` and absolute
  pseudo-coherence in `D(A)` under a pseudo-coherent ring map `R → A`;
- sampled owner declarations:
  `RingHom.IsPseudoCoherentRingMap`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_forall_isMPseudoCoherent`;
- best owner abstraction: this file stays `source-facing`, while the chapter owner for changing the
  base along an intermediate algebra is
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`;
- primitive vs. derived: primitive data are the ring-map class field asserting relative
  pseudo-coherence of the regular `A`-module over `R`; derived API is the resulting equivalence
  between relative and absolute pseudo-coherence on derived `A`-complexes, with the self-base
  comparison kept internal as bridge data.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems
  `isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap` and
  `isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap`;
- `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherent`, and `DerivedCategory.IsMPseudoCoherent`;
- `bridge/view`: the internal self-base comparison together with
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`.
 -/

private theorem regularModule_restrictScalars_isPseudoCoherent
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] A) (hα : Function.Surjective α) :
    ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)).IsPseudoCoherent := by
  let P : Type u := MvPolynomial (Fin n) A
  let M : ModuleCat P := (ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)
  let hId : (RingHom.id A).IsPseudoCoherentRingMap := inferInstance
  have hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo A := hId.isPseudoCoherentRelativeTo
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent]
  intro m
  let F : ModuleCat A ⥤ ModuleCat P := ModuleCat.restrictScalars α.toRingHom
  let e₀ :
      (((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A A)).polynomialPresentationRestriction α) ≅
        (CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M :=
    (Functor.mapCochainComplexSingleFunctor F (0 : ℤ)).app (ModuleCat.of A A)
  let e :
      (ModuleCat.single0Functor : ModuleCat P ⥤ DerivedCategory (ModuleCat P)).obj M ≅
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat P) (0 : ℤ)).app M
  let Qprop : ObjectProperty (DerivedCategory (ModuleCat P)) := fun K ↦ K.IsMPseudoCoherent m
  have hsource :
      DerivedCategory.IsMPseudoCoherent
        (DerivedCategory.Q.obj
          ((((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
            (ModuleCat.of A A)).polynomialPresentationRestriction α))) m := by
    simpa [CochainComplex.IsMPseudoCoherent] using hA m n α hα
  have htarget :
      Qprop (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M)) :=
    Qprop.prop_of_iso (DerivedCategory.Q.mapIso e₀) hsource
  exact
    Qprop.prop_of_iso e.symm htarget

omit [Algebra R A] [(algebraMap R A).IsPseudoCoherentRingMap] in
private theorem moduleCat_isPseudoCoherentRelativeTo_congr_algebra
    (M : ModuleCat A)
    {alg₁ alg₂ : Algebra R A}
    {ft₁ : @Algebra.FiniteType R A _ _ alg₁}
    {ft₂ : @Algebra.FiniteType R A _ _ alg₂}
    (h : alg₁ = alg₂) :
    @ModuleCat.IsPseudoCoherentRelativeTo R _ A _ alg₁ ft₁ M ↔
      @ModuleCat.IsPseudoCoherentRelativeTo R _ A _ alg₂ ft₂ M := by
  subst h
  have hft : ft₁ = ft₂ := Subsingleton.elim _ _
  subst hft
  rfl

private theorem regularModule_isPseudoCoherentRelativeTo_base :
    (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := by
  let hRing : (algebraMap R A).IsPseudoCoherentRingMap := inferInstance
  let hAlg : (algebraMap R A).toAlgebra = (inferInstance : Algebra R A) := by
    ext r x
    change @SMul.smul R A ((algebraMap R A).toAlgebra).toSMul r x = r • x
    rw [show @SMul.smul R A ((algebraMap R A).toAlgebra).toSMul r x =
        (algebraMap R A) r * x by
      rfl]
    rw [Algebra.smul_def]
  letI : Algebra R A := (algebraMap R A).toAlgebra
  letI : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hRing.finiteType
  have hbase : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := hRing.isPseudoCoherentRelativeTo
  exact (moduleCat_isPseudoCoherentRelativeTo_congr_algebra (ModuleCat.of A A) hAlg).1 hbase

private theorem isMPseudoCoherentRelativeTo_self_iff
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherent m := by
  constructor
  · intro hK
    rcases
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType A A)
      with ⟨n, α, hα⟩
    exact
      (isMPseudoCoherent_iff_restrictScalars α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent α hα)).2 (hK n α hα)
  · intro hK n α hα
    exact
      (isMPseudoCoherent_iff_restrictScalars α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent α hα)).1 hK

-- Proof sketch: first compare relative pseudo-coherence over `R` with relative pseudo-coherence
-- over the intermediate algebra `A` by Lemma `15.82.15`, using the pseudo-coherent ring map
-- hypothesis to supply pseudo-coherence of the regular `A`-module relative to `R`. Then identify
-- relative pseudo-coherence over `A` with the absolute notion by the previous theorem.
/-- Lemma 15.83.7 (1): if `R → A` is a pseudo-coherent ring map, then a derived `A`-complex is
`m`-pseudo-coherent relative to `R` if and only if it is `m`-pseudo-coherent in `D(A)`. -/
theorem isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherent m := by
  calc
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherentRelativeTo A m := by
      simpa using
        (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo K m
          regularModule_isPseudoCoherentRelativeTo_base).symm
    _ ↔ K.IsMPseudoCoherent m := isMPseudoCoherentRelativeTo_self_iff K m

-- Proof sketch: combine Lemma `15.82.15 (2)` with the self-base comparison above.
/-- Lemma 15.83.7 (2): if `R → A` is a pseudo-coherent ring map, then a derived `A`-complex is
pseudo-coherent relative to `R` if and only if it is pseudo-coherent in `D(A)`. -/
theorem isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) :
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherent := by
  calc
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherentRelativeTo A := by
      simpa using
        (isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo K
          regularModule_isPseudoCoherentRelativeTo_base).symm
    _ ↔ K.IsPseudoCoherent := by
      rw [DerivedCategory.IsPseudoCoherentRelativeTo, isPseudoCoherent_iff_forall_isMPseudoCoherent]
      constructor
      · intro hK m
        exact (isMPseudoCoherentRelativeTo_self_iff K m).1 (hK m)
      · intro hK m
        exact (isMPseudoCoherentRelativeTo_self_iff K m).2 (hK m)

end

end CategoryTheory

/-! ### Lemma_15_83_8 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {B : Type u} {A : Type u}
variable [CommRing R] [CommRing B] [CommRing A]
variable [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
variable [Module.Flat R B] [Algebra.FinitePresentation R B]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

-- Proof sketch: first use flat finite presentation to regard `R → B` and `R → A` as perfect, hence
-- pseudo-coherent, ring maps. Then apply Lemma `15.83.7` to identify absolute and relative
-- pseudo-coherence over `R` for both `A` and `B`, Lemma `15.82.15` to compare relative
-- pseudo-coherence over `R` and over `A`, and Lemma `15.65.11` together with surjectivity of
-- `B → A` to compare `K` with its restriction of scalars.
/-- Lemma 15.83.8: let `R → B → A` be ring maps with `B → A` surjective and with `R → B` and
`R → A` flat and of finite presentation. For `K ∈ D(A)`, the following are equivalent:
`K` is pseudo-coherent, `K` is pseudo-coherent relative to `R`, `K` is pseudo-coherent relative
to `A`, its restriction of scalars to `D(B)` is pseudo-coherent, and that restriction is
pseudo-coherent relative to `R`. -/
theorem isPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsPseudoCoherent,
      K.IsPseudoCoherentRelativeTo R,
      K.IsPseudoCoherentRelativeTo A,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherent,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherentRelativeTo R
    ] := sorry

-- Proof sketch: repeat the same comparison chain as in the pseudo-coherent case, now using the
-- `m`-pseudo-coherent variants of Lemmas `15.83.7`, `15.82.15`, and `15.65.11`.
/-- Under the same hypotheses, the analogous five-way equivalence also holds for
`m`-pseudo-coherence. -/
theorem isMPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (m : ℤ) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsMPseudoCoherent m,
      K.IsMPseudoCoherentRelativeTo R m,
      K.IsMPseudoCoherentRelativeTo A m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherent m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherentRelativeTo R m
    ] := sorry

end

end CategoryTheory
