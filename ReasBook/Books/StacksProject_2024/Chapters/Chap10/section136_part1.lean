import Mathlib
import Mathlib.RingTheory.Extension.Cotangent.Basis
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_136_1 (from Chap10) -/
universe u v

section

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open PrimeSpectrum

/- Source/core/bridge triage:
* source-facing: `RingHom.Syntomic`, the textbook property of a ring map being flat, finitely
  presented, and having local-complete-intersection fibers;
* core/canonical: the owner predicate on the ring homomorphism itself, with the three defining
  ingredients as primitive fields;
* bridge/view: the separate fiberwise predicate `HasLocalCompleteIntersectionFibers`.

The primitive data for syntomicity are exactly those three ingredients. Flatness and finite
presentation are not separate wrapper declarations here; they are projections of the owner
abstraction, matching the surrounding chapter style and mathlib's `Smooth`/`Etale` owners.
-/

/-- A ring homomorphism has local complete intersection fibers if each fiber over a prime of the
source is a local complete intersection over the corresponding residue field. -/
def HasLocalCompleteIntersectionFibers (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R, IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S)

/-- Definition 10.136.1: a ring homomorphism is syntomic if it is flat, of finite presentation,
and all of its fibers are local complete intersections. -/
def Syntomic (f : R →+* S) : Prop :=
  f.Flat ∧ f.FinitePresentation ∧ f.HasLocalCompleteIntersectionFibers

namespace Syntomic

theorem flat {f : R →+* S} (hf : f.Syntomic) : f.Flat :=
  hf.1

theorem finitePresentation {f : R →+* S} (hf : f.Syntomic) : f.FinitePresentation :=
  hf.2.1

theorem hasLocalCompleteIntersectionFibers {f : R →+* S} (hf : f.Syntomic) :
    f.HasLocalCompleteIntersectionFibers :=
  hf.2.2

end Syntomic

end RingHom

end

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

-- Proof sketch: over a field every module is flat, and a local complete intersection `k`-algebra
-- is finite type by definition, hence finite presentation over the Noetherian base field `k`. The
-- only fiber of `Spec A → Spec k` is the fiber over `(0)`, which is canonically `A` itself.
/-- A local complete intersection algebra over a field is syntomic. -/
theorem syntomic_of_isLocalCompleteIntersection [IsLocalCompleteIntersection k A] :
    (algebraMap k A).Syntomic := sorry

end

end Algebra

/-! ### Lemma_10_136_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: faithfully flat descent and base change for syntomic ring maps in commutative
  algebra;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `flat_iff_flat_baseChange_of_faithfullyFlat`,
  `finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat`,
  `isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension`;
- best owner abstraction: the public statement belongs on the ring-hom owner
  `RingHom.Syntomic`, with flatness, finite presentation, and local-complete-intersection fibers
  kept as derived component API rather than repackaged local data;
- primitive vs. derived:
  the primitive inputs are only the rings, algebra structures, and the faithfully flat base change
  `R → R'`;
  the forward base-change theorem `syntomic_baseChange`, the flat/finitely-presented descent
  theorems, the choice of a prime `p'` over `p`, and the fiber comparison over residue fields are
  all canonical derived API.

Source/core/bridge triage:
* `source-facing`: the textbook `iff` for syntomicity under faithfully flat base change;
* `core/canonical`: `RingHom.Syntomic`;
* `bridge/view`: `syntomic_baseChange`, the component descent theorems, and the prime-lifting step
  along `PrimeSpectrum.comap`.
-/

-- Proof sketch: unpack `RingHom.Syntomic` into flatness, finite presentation, and local complete
-- intersection fibers. The first two conditions descend and ascend along faithfully flat base
-- change by Lemmas `10.39.9` and `10.126.2`. Since `Spec R' → Spec R` is surjective by Lemma
-- `10.39.16`, the fiberwise condition reduces to comparing `S ⊗[R] κ(p)` with
-- `(R' ⊗[R] S) ⊗[R'] κ(p')`, and Lemma `10.135.11` identifies local complete intersections across
-- that residue-field extension.
/-- Lemma 10.136.2: for a faithfully flat base change `R → R'`, the ring map `R → S` is syntomic
if and only if the base-changed map `R' → R' ⊗[R] S` is syntomic. -/
theorem syntomic_iff_syntomic_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).Syntomic ↔ (algebraMap R' (R' ⊗[R] S)).Syntomic := by
  constructor
  · intro h
    simpa using h.baseChange
  · intro hbase
    letI : Module.FaithfullyFlat R R' :=
      (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
        Module.FaithfullyFlat R R').mp hff
    letI : Module.Flat R R' := (RingHom.flat_algebraMap_iff).mp hff.flat
    refine ⟨?_, ?_, ?_⟩
    · rw [RingHom.flat_algebraMap_iff]
      letI : Module.Flat R' (R' ⊗[R] S) := (RingHom.flat_algebraMap_iff).mp hbase.flat
      have hflatBase : Module.Flat R (R' ⊗[R] S) := Module.Flat.trans R R' (R' ⊗[R] S)
      exact (flat_iff_flat_baseChange_of_faithfullyFlat).mpr hflatBase
    · have hfpBase : Algebra.FinitePresentation R' (R' ⊗[R] S) := by
        simpa [RingHom.finitePresentation_algebraMap] using hbase.finitePresentation
      rw [RingHom.finitePresentation_algebraMap]
      exact
        (finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat hff).mpr hfpBase
    · intro p
      have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R R')) :=
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
      obtain ⟨p', hp'⟩ := hsurj p
      letI : p'.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hp').symm⟩
      -- The remaining step is the canonical fiber identification
      -- `p'.asIdeal.Fiber (R' ⊗[R] S) ≃ κ(p') ⊗[κ(p)] p.asIdeal.Fiber S`, after which
      -- Lemma `10.135.11` gives the desired descent of the local-complete-intersection fiber
      -- condition.
      sorry

end RingHom

end

/-! ### Lemma_10_136_3 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: syntomic ring maps under tensor-product base change in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.Smooth.baseChange`;
- best owner abstraction:
  `RingHom.Syntomic` is the owner predicate, while the tensor-product base change
  `R' → R' ⊗[R] S` is the canonical bridge/view on which the stability theorem should live;
- primitive vs. derived:
  flatness, finite presentation, and local-complete-intersection fibers are derived projections of
  `RingHom.Syntomic`, so this file should expose only the owner-namespace base-change theorem
  rather than a parallel freestanding wrapper.
-/

namespace Syntomic

-- Proof sketch: unpack `hf` into flatness, finite presentation, and local complete-intersection
-- fibers. The first two properties are preserved by base change by the canonical base-change
-- results, and each fiber of `R' → R' ⊗[R] S` is a residue-field extension of a fiber of
-- `R → S`, so Lemma `10.135.11` transports the local complete-intersection condition.
/-- Lemma 10.136.3: any base change of a syntomic ring map is syntomic. -/
theorem baseChange (hf : (algebraMap R S).Syntomic) :
    (algebraMap R' (R' ⊗[R] S)).Syntomic := sorry

end Syntomic

end RingHom

end

/-! ### Lemma_10_136_4 (from Chap10) -/
open scoped TensorProduct

universe u v w

section AlgebraHelpers

namespace Algebra

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {B : Type w} [CommRing B] [Algebra k B]

namespace IsLocalCompleteIntersection

/-- Helper for Lemma 10.136.4: local complete intersections are invariant under `k`-algebra
equivalence. -/
theorem of_algEquiv (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image e, ?_, ?_⟩
  · -- Transport the unit-ideal condition along the algebra equivalence.
    calc
      Ideal.span ((s.image e : Finset B) : Set B)
          = Ideal.map (e : A →+* B) (Ideal.span (s : Set A)) := by
              simp [Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (e : A →+* B) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- Rewrite the localized chart along the induced equivalence of away localizations.
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal a ha) <|
      IsLocalization.algEquivOfAlgEquiv
        (A := k)
        (S := Localization.Away a)
        (Q := Localization.Away (e a))
        e
        (Submonoid.map_powers e a)

/-- Helper for Lemma 10.136.4: if a finite principal-open cover of `Spec A` consists of local
complete intersections, then `A` is a local complete intersection. -/
theorem of_span_eq_top_target (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤)
    (hloc : ∀ g : s, IsLocalCompleteIntersection k (Localization.Away (g : A))) :
    IsLocalCompleteIntersection k A := by
  classical
  choose t htone ht using fun g : s => (hloc g).exists_basicOpen_cover
  let u : Finset A :=
    (Finset.univ.sigma fun g ↦ (t g).attach).image
      (fun x ↦ (x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
  refine ⟨u, ?_, ?_⟩
  · -- Clear denominators in the localized covers to obtain a finite cover of `Spec A`.
    have hu :
        (u : Set A) =
          Set.range
            (IsLocalization.Away.mulNumerator
              (s : Set A)
              (fun g : (s : Set A) ↦ (t ⟨g.1, g.2⟩ : Set (Localization.Away g.1)))) := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
        exact ⟨⟨⟨(x.1 : A), x.1.2⟩, ⟨x.2.1, by simpa using x.2.2⟩⟩, rfl⟩
      · rintro ⟨⟨g, y⟩, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨⟨g.1, g.2⟩, ⟨y.1, by simpa using y.2⟩⟩, ?_, rfl⟩
        simp
    rw [hu]
    exact IsLocalization.Away.span_range_mulNumerator_eq_top
      (s := (s : Set A))
      hs
      (fun g ↦ by simpa using htone ⟨g.1, g.2⟩)
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
    have hsec :
        Associated x.2.1
          (algebraMap A (Localization.Away (x.1 : A))
            (IsLocalization.Away.sec (x.1 : A) x.2.1).1) := by
      simpa using (IsLocalization.Away.associated_sec_fst (x.1 : A) x.2.1).symm
    letI :
        IsLocalization.Away
          (algebraMap A (Localization.Away (x.1 : A))
            (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
          (Localization.Away x.2.1) :=
      IsLocalization.Away.of_associated hsec
    letI :
        IsLocalization.Away
          ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
          (Localization.Away x.2.1) :=
      IsLocalization.Away.mul'
        (Localization.Away (x.1 : A))
        (Localization.Away x.2.1)
        (x.1 : A)
        (IsLocalization.Away.sec (x.1 : A) x.2.1).1
    -- View the final chart directly as an away localization of `A`.
    exact IsGlobalCompleteIntersection.of_algEquiv (ht x.1 x.2.1 x.2.2) <|
      (IsLocalization.algEquiv
        (Submonoid.powers ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1))
        (Localization.Away x.2.1)
        (Localization.Away ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1))).restrictScalars k

end IsLocalCompleteIntersection

end Algebra

end AlgebraHelpers

section

namespace RingHom

open Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Source/core/bridge triage:
* source-facing: syntomicity is local on the target for a finite principal-open cover;
* core/canonical: `RingHom.OfLocalizationSpanTarget` for the owner predicate `RingHom.Syntomic`;
* bridge/view: any explicit finite family `g : Fin n → S` generating the unit ideal.

The primitive data are already in `RingHom.Syntomic` from Definition `10.136.1`. This file adds
only the canonical locality theorem for that owner predicate rather than a parallel free-standing
restatement specialized to one chosen cover.
-/

/-- Helper for Lemma 10.136.4: the fiber of `R → S_g` identifies with the localization of the
fiber ring of `R → S` away from the image of `g`. -/
noncomputable def fiber_localizationAway_algEquiv
    [Algebra R S] (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S)
    [Algebra R (Localization.Away g)] [IsScalarTower R S (Localization.Away g)]
    [Algebra S (p.asIdeal.Fiber S)] [IsScalarTower R S (p.asIdeal.Fiber S)] :
    p.asIdeal.Fiber (Localization.Away g) ≃ₐ[p.asIdeal.ResidueField]
      Localization.Away (algebraMap S (p.asIdeal.Fiber S) g) :=
  -- TODO: compare `κ(p) ⊗[R] S_g` with `(κ(p) ⊗[R] S)_{ḡ}` by composing
  -- `Algebra.IsPushout.cancelBaseChangeAlg`, tensor symmetry over `S`, and
  -- `IsLocalization.Away.tensorRightEquiv`, then upgrade the resulting ring equivalence to an
  -- algebra equivalence over `p.asIdeal.ResidueField`.
  sorry

/-- Helper for Lemma 10.136.4: syntomicity of `R → S_g` yields a local complete intersection
chart on every fiber over `R`. -/
theorem fiber_localizationAway_isLocalCompleteIntersection_of_syntomic
    [Algebra R S] {f : R →+* S} (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S)
    [Algebra S (p.asIdeal.Fiber S)] [IsScalarTower R S (p.asIdeal.Fiber S)]
    (hg : ((algebraMap S (Localization.Away g)).comp f).HasLocalCompleteIntersectionFibers) :
    IsLocalCompleteIntersection p.asIdeal.ResidueField
      (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := by
  -- Route correction: the source-faithful fiber argument closes once the fiber of `S_g` is
  -- rewritten as the localization of the fiber of `S`; no new global locality argument is needed.
  let _ : Algebra R (Localization.Away g) := ((algebraMap S (Localization.Away g)).comp f).toAlgebra
  have hfiber :
      IsLocalCompleteIntersection p.asIdeal.ResidueField
        (p.asIdeal.Fiber (Localization.Away g)) := hg p
  -- Transport the localized fiber property across the canonical fiber/localization equivalence.
  exact Algebra.IsLocalCompleteIntersection.of_algEquiv hfiber <|
    fiber_localizationAway_algEquiv (R := R) (S := S) p g

/-- Helper for Lemma 10.136.4: the local-complete-intersection fiber condition is local on the
target. -/
theorem HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget :
    OfLocalizationSpanTarget HasLocalCompleteIntersectionFibers := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  intro R S _ _ f s hs hloc
  let _ : Algebra R S := f.toAlgebra
  intro p
  classical
  let _ : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let sp : Finset (p.asIdeal.Fiber S) := s.image (algebraMap S (p.asIdeal.Fiber S))
  have hsp : Ideal.span (sp : Set (p.asIdeal.Fiber S)) = ⊤ := by
    -- The target generators still span after mapping into the fiber ring.
    calc
      Ideal.span ((sp : Finset (p.asIdeal.Fiber S)) : Set (p.asIdeal.Fiber S))
          = Ideal.map (algebraMap S (p.asIdeal.Fiber S)) (Ideal.span (s : Set S)) := by
              simp [sp, Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (algebraMap S (p.asIdeal.Fiber S)) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  refine Algebra.IsLocalCompleteIntersection.of_span_eq_top_target sp hsp ?_
  intro g
  rcases Finset.mem_image.mp g.2 with ⟨x, hx, hxg⟩
  -- Each fiber chart comes from the corresponding syntomic target localization.
  rw [← hxg]
  exact
    fiber_localizationAway_isLocalCompleteIntersection_of_syntomic
      (R := R)
      (S := S)
      (f := f)
      p
      x
      (hloc ⟨x, hx⟩)

-- Proof sketch: combine the canonical target-locality results for flatness and finite
-- presentation with the fiberwise local-complete-intersection criterion. For a source prime `p`,
-- the induced principal-open cover on the fiber ring `κ(p) ⊗[R] S` is generated by the images of
-- the chosen target generators, and each localized fiber is a local complete intersection by the
-- syntomic hypotheses on the corresponding target localizations.
/-- Lemma 10.136.4: syntomicity is local on the target for finite principal-open covers. -/
theorem Syntomic.ofLocalizationSpanTarget : OfLocalizationSpanTarget Syntomic := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  intro R S _ _ f s hs hloc
  refine ⟨?_, ?_, ?_⟩
  · -- Flatness is already known to be local on the target.
    exact RingHom.Flat.ofLocalizationSpanTarget f s hs fun r ↦ (hloc r).flat
  · -- Finite presentation is also known to be local on the target.
    exact RingHom.finitePresentation_ofLocalizationSpanTarget f s hs
      fun r ↦ (hloc r).finitePresentation
  · -- Reassemble the fiberwise local complete intersection condition from the localized charts.
    exact HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget f s hs
      fun r ↦ (hloc r).hasLocalCompleteIntersectionFibers

end RingHom

end

/-! ### Definition_10_136_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra

namespace Presentation

variable {n c : ℕ}

/-- A finite presentation `P : R[x₁, …, xₙ] ⟶ S` exhibits `S` as a relative global complete
intersection over `R` if every nonempty fiber of `S` has Krull dimension equal to the
presentation dimension `n - c`. This is the presentation-level source-facing owner underlying the
intrinsic existential class `Algebra.IsRelativeGlobalCompleteIntersection R S`. -/
def IsRelativeGlobalCompleteIntersection (P : Algebra.Presentation R S (Fin n) (Fin c)) : Prop :=
  ∀ p : PrimeSpectrum R,
    Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) →
      ringKrullDim (p.asIdeal.Fiber S) = P.dimension

end Presentation

/- Source/core/bridge triage:
* source-facing: `IsRelativeGlobalCompleteIntersection R S`, the textbook relative global complete
  intersection condition;
* core/canonical: a finite algebra presentation `Algebra.Presentation R S (Fin n) (Fin c)` and
  the canonical finiteness owner `Algebra.FinitePresentation R S`;
* bridge/view: the presentation-level owner
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection` and explicit quotient-model or
  map-based reformulations in later files.

Primitive data are exactly one finite presentation together with the fiber-dimension condition.
Finite presentation of `S` over `R` is therefore derived API and should not remain a parallel
public wrapper around the same witness.
-/
/-- Definition 10.136.5: an `R`-algebra `S` is a relative global complete intersection if it
admits a presentation by `n` generators and `c` relations, and for every prime `p` of `R` whose
fiber is nonempty, the fiber ring `κ(p) ⊗[R] S` has Krull dimension equal to the presentation
dimension. -/
class IsRelativeGlobalCompleteIntersection (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] : Prop where
  exists_presentation :
    ∃ (n c : ℕ) (P : Algebra.Presentation R S (Fin n) (Fin c)),
        P.IsRelativeGlobalCompleteIntersection

/-- A presentation-level witness upgrades directly to the intrinsic relative global complete
intersection class. -/
theorem Presentation.toIsRelativeGlobalCompleteIntersection
    {n c : ℕ}
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Algebra.IsRelativeGlobalCompleteIntersection R S where
  exists_presentation := ⟨n, c, P, hP⟩

instance instFinitePresentationOfIsRelativeGlobalCompleteIntersection
    [h : IsRelativeGlobalCompleteIntersection R S] : Algebra.FinitePresentation R S := by
  rcases h.exists_presentation with ⟨n, c, P, _⟩
  simpa using P.finitePresentation_of_isFinite

end Algebra

end

/-! ### Lemma_10_136_6 (from Chap10) -/
/- Domain-style sampling:
- primary domain: finite algebra presentations, conormal modules, and free cotangent presentations;
- sampled owner API:
  `Algebra.Generators`,
  `Algebra.Presentation`,
  `Algebra.Generators.exists_presentation_of_basis_cotangent`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`;
- best owner abstraction: the canonical owner is the mathlib theorem
  `Algebra.Generators.exists_presentation_of_free_cotangent`, which upgrades free cotangent data
  for a finite generator family to a finite presentation whose relation classes give a basis of the
  conormal module;
- primitive vs. derived:
  the primitive data are a finite generator family together with freeness of its cotangent module;
  the enlarged presentation and its basis by relation classes are derived API and should not be
  repackaged here as a parallel local wrapper.

Source/core/bridge triage:
- `source-facing`: the textbook existence statement for a finite presentation with free conormal
  module generated by the defining relations;
- `core/canonical`: `Algebra.Generators.exists_presentation_of_free_cotangent`;
- `bridge/view`: none needed in this file, because the source statement is already exactly the
  canonical mathlib owner theorem.
-/

/- Lemma 10.136.6: if `S` is a finitely presented `R`-algebra with a finite polynomial
presentation whose conormal module `I / I²` is free over `S`, then `S` admits another finite
presentation whose conormal module is free with basis given by the classes of the defining
relations. In mathlib this is exactly
`Algebra.Generators.exists_presentation_of_free_cotangent`. -/
recall Algebra.Generators.exists_presentation_of_free_cotangent

/-! ### Example_10_136_7 (from Chap10) -/
open Polynomial
open scoped TensorProduct

noncomputable section

namespace MvPolynomial

variable (n m : ℕ)

/- Domain-style sampling:
* primary domain: generic factorization maps for monic polynomials in multivariable polynomial
  rings;
* inspected owner declarations:
  - `MvPolynomial.universalFactorizationMap`
  - `MvPolynomial.universalFactorizationMap_freeMonic`
  - `MvPolynomial.finite_universalFactorizationMap`
  - `MvPolynomial.tensorEquivSum`
* best owner abstraction:
  - `source-facing`: the textbook coefficient map
    `ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`
  - `core/canonical`: `MvPolynomial.universalFactorizationMap`
  - `bridge/view`: transport of that owner across `MvPolynomial.tensorEquivSum`
* primitive vs. derived:
  - primitive data: only `n`, `m`, and the canonical owner map
  - derived API: the source-facing sum-variable realization `genericFactorizationMap` and its
    consequences below
-/
/-- The textbook coefficient map
`ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`, obtained by transporting the canonical owner
`MvPolynomial.universalFactorizationMap` across `MvPolynomial.tensorEquivSum` to the polynomial
ring with variables `Fin n ⊕ Fin m`. -/
abbrev genericFactorizationMap :
    MvPolynomial (Fin (n + m)) ℤ →ₐ[ℤ] MvPolynomial (Fin n ⊕ Fin m) ℤ :=
  (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toAlgHom.comp
    (universalFactorizationMap ℤ (n + m) n m rfl)

/-- Helper for Example 10.136.7: transporting the left tensor-factor coefficient map through
`tensorEquivSum` identifies it with the `Sum.inl` variable renaming. -/
lemma tensorEquivSum_comp_includeLeft :
    ((tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom) =
      (rename Sum.inl).toRingHom := by
  -- The two maps agree on constants and variables, so the `MvPolynomial` extensionality lemma
  -- reduces the comparison to the defining formulas of `tensorEquivSum`.
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- Helper for Example 10.136.7: transporting the right tensor-factor coefficient map through
`tensorEquivSum` identifies it with the `Sum.inr` variable renaming. -/
lemma tensorEquivSum_comp_includeRight :
    ((tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom) =
      (rename Sum.inr).toRingHom := by
  -- The right factor is handled by the symmetric generator computation under `tensorEquivSum`.
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- The bridge to the canonical owner: the textbook coefficient map sends the generic monic
polynomial of degree `n + m` to the product of the two generic monic factors of degrees `n`
and `m`. -/
theorem genericFactorizationMap_freeMonic :
    (freeMonic ℤ (n + m)).map (genericFactorizationMap n m) =
      ((freeMonic ℤ n).map (rename Sum.inl).toRingHom) *
        ((freeMonic ℤ m).map (rename Sum.inr).toRingHom) := by
  -- Route correction: the tensor-product factorization identity is already canonical in mathlib,
  -- so the remaining work is to transport it across `tensorEquivSum`.
  let e := (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom
  have htransport := congrArg (Polynomial.map e)
    (universalFactorizationMap_freeMonic ℤ (n + m) n m rfl)
  have htransport' :
      (freeMonic ℤ (n + m)).map (genericFactorizationMap n m) =
        (((freeMonic ℤ n).map Algebra.TensorProduct.includeLeftRingHom).map e) *
          (((freeMonic ℤ m).map Algebra.TensorProduct.includeRight.toRingHom).map e) := by
    -- First normalize the source side to the displayed coefficient map.
    simpa [genericFactorizationMap, e, Polynomial.map_map, Algebra.TensorProduct.algebraMap_def,
      AlgHom.toRingHom_eq_coe] using htransport
  -- Rewriting the transported coefficient maps with the adapter lemmas yields the displayed map.
  have hleft_map :
      (((freeMonic ℤ n).map Algebra.TensorProduct.includeLeftRingHom).map e) =
        (freeMonic ℤ n).map (rename Sum.inl).toRingHom := by
    -- Combine the two polynomial maps into one composed map and apply the left transport lemma.
    rw [Polynomial.map_map, tensorEquivSum_comp_includeLeft]
  have hright_map :
      (((freeMonic ℤ m).map Algebra.TensorProduct.includeRight.toRingHom).map e) =
        (freeMonic ℤ m).map (rename Sum.inr).toRingHom := by
    -- The right factor is identical after the symmetric transport rewrite.
    rw [Polynomial.map_map, tensorEquivSum_comp_includeRight]
  rw [hleft_map, hright_map] at htransport'
  exact htransport'

/-- Helper for Example 10.136.7: every nonempty fiber of the generic factorization map has Krull
dimension `0`. -/
lemma genericFactorizationMap_fiber_ringKrullDim_eq_zero :
    letI := (genericFactorizationMap n m).toAlgebra
    ∀ p : PrimeSpectrum (MvPolynomial (Fin (n + m)) ℤ),
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ))) →
        ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) = 0 := by
  letI := (genericFactorizationMap n m).toAlgebra
  intro p hp
  have hfinite_map : (genericFactorizationMap n m).Finite := by
    -- Finiteness is transported from the canonical tensor-product model.
    exact RingHom.Finite.comp
      (RingEquiv.finite (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingEquiv)
      (finite_universalFactorizationMap ℤ (n + m) n m rfl)
  letI : Module.Finite (MvPolynomial (Fin (n + m)) ℤ) (MvPolynomial (Fin n ⊕ Fin m) ℤ) :=
    (RingHom.finite_algebraMap).mp hfinite_map
  letI : Module.Finite p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) := inferInstance
  letI : Nontrivial (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hp
  -- A finite algebra over the residue field is Artinian, hence zero-dimensional.
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp <|
    (Module.finite_iff_krullDimLE_zero p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ))).mp inferInstance

/-- Helper for Example 10.136.7: transporting the universal factorization presentation along
`tensorEquivSum` gives a relative global complete intersection presentation for the displayed map. -/
lemma genericFactorizationMap_presentation_isRelativeGlobalCompleteIntersection :
    letI := (genericFactorizationMap n m).toAlgebra
    ∃ P : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
        (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin (n + m)) (Fin (n + m)),
      P.IsRelativeGlobalCompleteIntersection := by
  letI := (genericFactorizationMap n m).toAlgebra
  letI := (universalFactorizationMap ℤ (n + m) n m rfl).toAlgebra
  let P₀ : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
      (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin n ⊕ Fin m) (Fin (n + m)) :=
    ((universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation).ofAlgEquiv
      { __ := tensorEquivSum ℤ (Fin n) (Fin m) ℤ
        commutes' := fun r ↦ rfl }
  let P : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
      (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin (n + m)) (Fin (n + m)) :=
    P₀.reindex (finSumFinEquiv.symm : Fin (n + m) ≃ Fin n ⊕ Fin m) (Equiv.refl _)
  have hdim :
      P.dimension = 0 := by
    -- Transport does not change presentation dimension, and here generators equal relations.
    calc
      P.dimension = P₀.dimension := by
            simpa [P] using P₀.dimension_reindex
              (finSumFinEquiv.symm : Fin (n + m) ≃ Fin n ⊕ Fin m) (Equiv.refl _)
      _ =
          (universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation.dimension := by
            simpa [P₀] using
              ((universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation
                .dimension_ofAlgEquiv
                  { __ := tensorEquivSum ℤ (Fin n) (Fin m) ℤ
                    commutes' := fun r ↦ rfl })
      _ = 0 := by
        simp [Algebra.Presentation.dimension]
  refine ⟨P, ?_⟩
  intro p hp
  -- The fiber calculation is the zero-dimensional part of the textbook argument.
  have hfiber :
      ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) = 0 :=
    genericFactorizationMap_fiber_ringKrullDim_eq_zero (n := n) (m := m) p hp
  simpa [hdim] using hfiber

-- Proof sketch: use `genericFactorizationMap_freeMonic` to identify the displayed coefficient map
-- with the canonical generic factorization map, and then transport the relative global complete
-- intersection structure across `tensorEquivSum`.
/-- Example 10.136.7: the coefficient ring map sending the coefficients of the generic monic
polynomial of degree `n + m` to the coefficients of the product of generic monic factors of
degrees `n` and `m` is a relative global complete intersection. -/
theorem genericFactorizationMap_isRelativeGlobalCompleteIntersection :
    letI := (genericFactorizationMap n m).toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection
      (MvPolynomial (Fin (n + m)) ℤ) (MvPolynomial (Fin n ⊕ Fin m) ℤ) := by
  letI := (genericFactorizationMap n m).toAlgebra
  -- Use the transported canonical presentation as the witness required by Definition 10.136.5.
  obtain ⟨P, hP⟩ :=
    genericFactorizationMap_presentation_isRelativeGlobalCompleteIntersection (n := n) (m := m)
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P) hP

-- Proof sketch: after identifying the displayed coefficient map with the canonical owner via
-- `genericFactorizationMap`, transport finiteness across `tensorEquivSum` and apply
-- `MvPolynomial.finite_universalFactorizationMap`.
/-- The generic factorization coefficient map is finite. -/
theorem genericFactorizationMap_finite :
    (genericFactorizationMap n m).Finite := by
  exact RingHom.Finite.comp
    (RingEquiv.finite (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingEquiv)
    (finite_universalFactorizationMap ℤ (n + m) n m rfl)

end MvPolynomial
