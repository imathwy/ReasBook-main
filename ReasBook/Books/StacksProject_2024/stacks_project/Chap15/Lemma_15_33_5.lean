import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_135_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_135_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_15
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_12
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_9
import StacksProject_2024.stacks_project.Chap10.Definition_10_112_5
import StacksProject_2024.stacks_project.Chap15.Definition_15_33_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_33_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open scoped TensorProduct

/- Domain-style sampling:
- primary domain: syntomic and local-complete-intersection properties of commutative ring
  homomorphisms;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.flat`,
  `RingHom.Syntomic.hasLocalCompleteIntersectionFibers`,
  `RingHom.IsLocalCompleteIntersection`;
- best owner abstraction: this lemma belongs on the ring-hom owner
  `RingHom.Syntomic`, not on the algebra-map specialization `algebraMap R S`;
- primitive vs. derived: the primitive owner data are already in `RingHom.Syntomic`, while the
  flatness projection is derived API and the local-complete-intersection criterion is the new
  companion characterization supplied here.

Source/core/bridge triage:
- `source-facing`: the equivalence between syntomicity and flat local complete intersection for a
  ring map;
- `core/canonical`: the owner predicates `RingHom.Syntomic` and
  `RingHom.IsLocalCompleteIntersection`;
- `bridge/view`: the algebra-map specialization obtained by instantiating the theorem below with
  `f := algebraMap R S`. -/

namespace Syntomic

/-- Helper for Lemma 15.33.5: the trivial localization chart `D(1)` of a syntomic map is still
of finite presentation over the base. -/
lemma finitePresentation_localizationAway_one_of_syntomic
    (f : R →+* S) (hf : f.Syntomic) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.FinitePresentation R (Localization.Away (1 : S)) := by
  let _ : Algebra R S := f.toAlgebra
  -- Proof comment: finite presentation is stable under composition, and localizing `S` away from
  -- `1` is finitely presented over `S`.
  have hg :
      (algebraMap S (Localization.Away (1 : S))).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr
      (IsLocalization.Away.finitePresentation (S := Localization.Away (1 : S)) (1 : S))
  let g : S →+* Localization.Away (1 : S) := algebraMap S (Localization.Away (1 : S))
  have hcomp : (g.comp f).FinitePresentation :=
    RingHom.FinitePresentation.comp hg hf.finitePresentation
  have hEq : g.comp f = algebraMap R (Localization.Away (1 : S)) := by
    ext r
    rfl
  exact (RingHom.finitePresentation_algebraMap).mp <| hEq ▸ hcomp

/-- Helper for Lemma 15.33.5: flatness of a syntomic map survives passage to the local ring map at
every target prime. -/
lemma localRingHom_flat_of_syntomic
    (f : R →+* S) (hf : f.Syntomic) (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal f rfl).Flat := by
  let _ : Algebra R S := f.toAlgebra
  -- Proof comment: flatness localizes along the canonical local ring map.
  exact RingHom.Flat.localRingHom hf.flat q.asIdeal (Ideal.under R q.asIdeal) rfl

/-- Helper for Lemma 15.33.5: syntomic fibers are complete intersections at every target prime's
canonical local fiber ring. -/
lemma fiberCompleteIntersectionAtPrime_of_hasLocalCompleteIntersectionFibers
    (f : R →+* S) (hfib : f.HasLocalCompleteIntersectionFibers) (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.FiberCompleteIntersectionAtPrime R q := by
  let _ : Algebra R S := f.toAlgebra
  let p : PrimeSpectrum R := PrimeSpectrum.comap f q
  let k : Type u := p.asIdeal.ResidueField
  let A : Type (max u v) := p.asIdeal.Fiber S
  let qf : PrimeSpectrum A := fiberPrimeAt R S q
  have hlocal : _root_.IsLocalCompleteIntersection k A := by
    -- Proof comment: specialize the fiberwise hypothesis to the contracted prime `q ∩ R`.
    simpa [p, k, A] using hfib p
  have hprimewise :
      ∀ Q : PrimeSpectrum A,
        Algebra.IsCompleteIntersectionOver.{u, max u v, max u v} k
          (Localization.AtPrime Q.asIdeal) := by
    -- Proof comment: the field-side local-complete-intersection owner is equivalent to the
    -- complete-intersection condition on every prime localization of the fixed fiber algebra.
    exact
      ((isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings.{u, max u v,
            max u v, max u v}
        (k := k) (S := A)).out 0 1 rfl rfl).mp hlocal
  -- Proof comment: evaluate the primewise criterion at the canonical prime of the fiber lying
  -- over `q`, whose localization is by definition the fiber local ring at `q`.
  simpa [Algebra.FiberCompleteIntersectionAtPrime, fiberLocalRingAt, fiberPrimeAt, p, k, A, qf]
    using hprimewise qf

/-- Helper for Lemma 15.33.5: a syntomic map yields a relative global complete-intersection
neighborhood at every target prime. -/
lemma relativeGCIAtPrime_of_syntomic
    (f : R →+* S) (hf : f.Syntomic) (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.RelativeGlobalCompleteIntersectionAtPrime R q := by
  let _ : Algebra R S := f.toAlgebra
  have hprimewise :
      Algebra.FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q := by
    refine ⟨1, ?_, ?_, localRingHom_flat_of_syntomic f hf q, ?_⟩
    · -- Proof comment: every prime ideal is proper, hence misses `1`.
      simpa [Ideal.eq_top_iff_one] using q.2.ne_top
    · -- Proof comment: the source-facing syntomic finite-presentation owner survives on `D(1)`.
      letI : Algebra.FinitePresentation R (Localization.Away (1 : S)) :=
        finitePresentation_localizationAway_one_of_syntomic f hf
      infer_instance
    · -- Proof comment: the fiber criterion comes from local complete-intersection fibers.
      exact fiberCompleteIntersectionAtPrime_of_hasLocalCompleteIntersectionFibers
        f hf.hasLocalCompleteIntersectionFibers q
  -- Proof comment: clause `(3) → (2)` of `syntomicAtPrime_tfae` packages the primewise witness.
  exact ((Algebra.syntomicAtPrime_tfae (R := R) (S := S) q).out 2 1 rfl rfl).mp hprimewise

/-- Helper for Lemma 15.33.5: if every prime admits a principal-open neighborhood cut out by an
element of `s`, then the elements of `s` span the unit ideal. -/
lemma span_eq_top_of_basicOpen_cover (s : Set S)
    (hs : ∀ q : PrimeSpectrum S, ∃ g ∈ s, g ∉ q.asIdeal) :
    Ideal.span s = ⊤ := by
  -- Proof comment: convert the primewise neighborhood condition into a cover by standard opens,
  -- then invoke the canonical `Spec`-cover criterion for `Ideal.span s = ⊤`.
  have hscover :
      (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ g ∈ s, PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    rcases hs q with ⟨g, hgs, hgq⟩
    have hgmem : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    exact
      (show (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) ≤
          ⨆ h ∈ s, PrimeSpectrum.basicOpen h from
        le_iSup_of_le g <| le_iSup_of_le hgs le_rfl) hgmem
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hscover

/-- Helper for Lemma 15.33.5: the relative-global-complete-intersection charts produced by a
syntomic map already span the target by principal opens. -/
lemma relativeGCI_charts_span_top_of_syntomic
    (f : R →+* S) (hf : f.Syntomic) :
    let _ : Algebra R S := f.toAlgebra
    Ideal.span {g : S | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g)} = ⊤ := by
  let _ : Algebra R S := f.toAlgebra
  -- Proof comment: apply the general basic-open cover criterion to the primewise relative-GCI
  -- neighborhoods furnished by `relativeGCIAtPrime_of_syntomic`.
  refine span_eq_top_of_basicOpen_cover
    (s := {g : S | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g)}) ?_
  intro q
  rcases relativeGCIAtPrime_of_syntomic f hf q with ⟨g, hgq, hg⟩
  exact ⟨g, hg, hgq⟩

/-- Helper for Lemma 15.33.5: further localizing a relative-global-complete-intersection chart
preserves the relative-global-complete-intersection owner. -/
lemma localizationAway_of_relativeGlobalCompleteIntersection
    {A : Type*} [CommRing A] [Algebra R A]
    (g : A) (hA : Algebra.IsRelativeGlobalCompleteIntersection R A) :
    Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- Proof comment: this is the canonical localization stability theorem for relative global
  -- complete intersections.
  exact Algebra.IsRelativeGlobalCompleteIntersection.localizationAway hA g

/-- Helper for Lemma 15.33.5: transporting a relative-global-complete-intersection presentation
across an algebra equivalence preserves the presentation-level owner. -/
lemma presentation_relativeGlobalCompleteIntersection_ofAlgEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {n c : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    (P.ofAlgEquiv e).IsRelativeGlobalCompleteIntersection := by
  intro p hp
  -- Proof comment: compare the two fibers by tensoring the algebra equivalence with the residue
  -- field of `p`; the fiber dimensions agree because ring equivalences preserve Krull dimension.
  let efiber : p.asIdeal.Fiber A ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber B :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl :
        p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      e
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    rcases hp with ⟨q⟩
    exact ⟨PrimeSpectrum.comap efiber.toRingHom q⟩
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa using (ringKrullDim_eq_of_ringEquiv efiber.toRingEquiv).symm
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      simpa using (P.dimension_ofAlgEquiv e).symm

/-- Helper for Lemma 15.33.5: the naive quotient presentation attached to the defining relations
of a relative-global-complete-intersection presentation is again a relative global complete
intersection. -/
lemma naivePresentation_isRelativeGlobalCompleteIntersection_of_presentation
    {A : Type*} [CommRing A] [Algebra R A]
    {n c : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation)
    (Algebra.Presentation.naive : Algebra.Presentation R T (Fin n) (Fin c)).IsRelativeGlobalCompleteIntersection := by
  let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation)
  let e : A ≃ₐ[R] T :=
    ((P.quotientEquiv.restrictScalars R).symm.trans
      (Ideal.quotientEquivAlgOfEq (R₁ := R) (A := P.Ring) P.span_range_relation_eq_ker).symm)
  -- Proof comment: after transporting `P` to the explicit quotient by its displayed relations,
  -- the presentation-level owner depends only on the common dimension `n - c`.
  simpa using presentation_relativeGlobalCompleteIntersection_ofAlgEquiv P hP e

/-- Helper for Lemma 15.33.5: a relative-global-complete-intersection principal chart should
package into the Chapter 15 ring-hom local-complete-intersection owner. -/
lemma relativeGCI_localizationAway_isLocalCompleteIntersection
    (f : R →+* S) (g : S) :
    let _ : Algebra R S := f.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) →
    RingHom.IsLocalCompleteIntersection (algebraMap R (Localization.Away g)) := by
  let _ : Algebra R S := f.toAlgebra
  exact fun hA ↦ by
    -- Proof comment: the explicit quotient route is now reduced to a single missing bridge.
    -- We can already transport any presentation witness to its naive quotient model by the two
    -- lemmas above; what remains is to replay the Chapter 15.33.4 Koszul-complex argument in this
    -- file, using `Algebra.relativeGCI_localized_relations_isRegular` on the naive model to
    -- produce a Koszul-regular kernel ideal and then packaging that kernel via `P.toGenerators`.
    rcases hA.exists_presentation with ⟨n, c, P, hP⟩
    let _ := naivePresentation_isRelativeGlobalCompleteIntersection_of_presentation P hP
    let _ := P
    let _ := c
    let _ := n
    sorry

/-- Helper for Lemma 15.33.5: a Koszul-regular ideal is finitely generated. -/
lemma fg_of_isKoszulRegularIdeal {A : Type*} [CommRing A] {I : Ideal A}
    (hI : I.IsKoszulRegularIdeal) :
    I.FG := by
  classical
  let J : (g : A) → Ideal (Localization.Away g) :=
    fun g ↦ I.map (algebraMap A (Localization.Away g))
  let s : Set A := {g | (J g).FG}
  have hs_mem {g : A} (hg : g ∈ s) :
      (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum A)) ≤
        ⨆ r ∈ s, PrimeSpectrum.basicOpen r :=
    le_iSup_of_le g <| le_iSup_of_le hg le_rfl
  have hs_cover : (⨆ r ∈ s, PrimeSpectrum.basicOpen r) = ⊤ := by
    -- Proof comment: the local Koszul-regular witnesses generate the localized ideal by finitely
    -- many elements on a basic-open cover of `V(I)`, while outside `V(I)` any element of `I`
    -- already trivializes the localization.
    apply SetLike.ext'
    change (↑(⨆ r ∈ s, PrimeSpectrum.basicOpen r) : Set (PrimeSpectrum A)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro p
    by_cases hpI : I ≤ p.asIdeal
    · rcases (Ideal.isKoszulRegularIdeal_iff I).1 hI p.asIdeal p.2 hpI with
        ⟨g, hg, r, f, _, hJg⟩
      have hgfg : g ∈ s := by
        simpa [J, s, hJg] using
          (Submodule.fg_span (Set.finite_range f) : (Ideal.span (Set.range f)).FG)
      have hpg : p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hg
      exact hs_mem hgfg hpg
    · have hpI' : ∃ x, x ∈ I ∧ x ∉ p.asIdeal := by
        simpa [SetLike.le_def] using hpI
      rcases hpI' with ⟨x, hxI, hxp⟩
      have hxfg : x ∈ s := by
        have hxmap : algebraMap A (Localization.Away x) x ∈ J x :=
          Ideal.mem_map_of_mem _ hxI
        have hxtop : J x = ⊤ :=
          (J x).eq_top_of_isUnit_mem hxmap
            (IsLocalization.map_units (Localization.Away x) ⟨x, Submonoid.mem_powers x⟩)
        simpa [J, s, hxtop] using Ideal.fg_top (Localization.Away x)
      have hpx : p ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hxp
      exact hs_mem hxfg hpx
  have hs_span : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hs_cover
  -- Proof comment: once the local finite generation data spans the target, the canonical
  -- localization-spanning descent theorem globalizes it to `I`.
  refine Ideal.fg_of_localizationSpan s hs_span ?_
  intro g
  change (J g.1).FG
  exact g.2

/-- Helper for Lemma 15.33.5: a local complete intersection ring map is finitely presented. -/
lemma finitePresentation_of_isLocalCompleteIntersection
    (f : R →+* S) (hci : f.IsLocalCompleteIntersection) :
    f.FinitePresentation := by
  let _ : Algebra R S := f.toAlgebra
  rcases hci.exists_generators_ker_isKoszulRegular with ⟨n, P, hker⟩
  have hfgker : P.ker.FG := fg_of_isKoszulRegularIdeal hker
  let φ : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  have hφsurj : Function.Surjective φ := P.algebraMap_surjective
  have hfpAlg : Algebra.FinitePresentation R S := by
    -- Proof comment: the chosen finite polynomial presentation has finitely generated kernel, so
    -- the surjective finite-presentation criterion applies directly.
    exact Algebra.FinitePresentation.of_surjective (f := φ) hφsurj hfgker
  -- Proof comment: translate the algebra-side finite-presentation owner back to the ring-hom
  -- owner for the actual map `f`.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.finitePresentation_algebraMap).mpr hfpAlg

/-- Helper for Lemma 15.33.5: the target-local descent theorem for local complete intersections
applies to mixed-universe source and target rings after a `ULift` universe alignment. -/
lemma isLocalCompleteIntersection_of_localizationSpanTarget
    (f : R →+* S)
    (s : Set S) (hs : Ideal.span s = ⊤)
    (hcover : ∀ g : s,
      RingHom.IsLocalCompleteIntersection
        ((algebraMap S (Localization.Away (g : S))).comp f)) :
    f.IsLocalCompleteIntersection := by
  -- Route correction: the source-facing proof already reduces the forward implication to target-
  -- local descent, but `RingHom.OfLocalizationSpanTarget` in mathlib is formulated in a single
  -- universe. The remaining work is a pure universe-alignment adapter: lift `R` and `S` to a
  -- common `ULift` universe, apply `RingHom.IsLocalCompleteIntersection.ofLocalizationSpanTarget`
  -- there, and transport the result back along the source and target `ULift` ring equivalences.
  let _ := hs
  let _ := hcover
  sorry

/-- Helper for Lemma 15.33.5: a flat local complete intersection map has local complete
intersection fibers. -/
lemma hasLocalCompleteIntersectionFibers_of_flat_isLocalCompleteIntersection
    (f : R →+* S) (hflat : f.Flat) (hci : f.IsLocalCompleteIntersection) :
    f.HasLocalCompleteIntersectionFibers := by
  -- TODO for Lemma 15.33.5: fix `p : PrimeSpectrum R`, base change the chosen Koszul-regular
  -- presentation of `f` to `p.asIdeal.ResidueField`, and follow the source proof prime-by-prime in
  -- the fiber using the `H₁`-regular and regular-sequence upgrades from Chapter 15 together with
  -- `Algebra.completeIntersectionOver_atPrime_tfae` and
  -- `Algebra.isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings`.
  let _ := hflat
  let _ := hci
  sorry

-- Proof sketch: for the forward implication, unpack `Syntomic R S`; flatness is built into the
-- definition, and the fiberwise local complete intersection condition can be upgraded to the ring-
-- map local complete intersection criterion via the relative-global-complete-intersection
-- neighborhood theorem together with Lemmas `15.33.3` and `15.33.4`. For the reverse implication,
-- a flat local complete intersection map is of finite presentation, and after base change to each
-- residue field its fibers are local complete intersections, which is exactly the remaining
-- syntomic condition.
/-- Lemma 15.33.5: a ring map is syntomic if and only if it is flat and a local complete
intersection. -/
theorem iff_flat_and_isLocalCompleteIntersection (f : R →+* S) :
    f.Syntomic ↔ f.Flat ∧ f.IsLocalCompleteIntersection := by
  constructor
  · intro hf
    refine ⟨hf.flat, ?_⟩
    let _ : Algebra R S := f.toAlgebra
    -- Proof comment: the forward route is reduced to target-local descent from the primewise
    -- relative-global-complete-intersection neighborhoods obtained from
    -- `Algebra.syntomicAtPrime_tfae`.
    have hspan :
        Ideal.span {g : S | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g)} =
          ⊤ :=
      relativeGCI_charts_span_top_of_syntomic f hf
    -- Proof comment: once each relative-GCI chart is known to be a Chapter 15 local complete
    -- intersection chart, the target-local descent theorem from `Lemma_15_33_3` globalizes the
    -- property immediately from the spanning basic-open cover.
    exact
      isLocalCompleteIntersection_of_localizationSpanTarget
        (f := f)
        {g : S | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g)}
        hspan
        (fun g ↦ by
          have hcomp :
              (algebraMap S (Localization.Away (g : S))).comp f =
                algebraMap R (Localization.Away (g : S)) := by
            ext x
            rfl
          exact hcomp ▸
            relativeGCI_localizationAway_isLocalCompleteIntersection f g.1 g.2)
  · intro h
    rcases h with ⟨hflat, hci⟩
    refine ⟨hflat, finitePresentation_of_isLocalCompleteIntersection f hci, ?_⟩
    -- Proof comment: finite presentation is now discharged directly from the chosen
    -- local-complete-intersection presentation, so only the source-faithful fiber argument
    -- remains.
    exact hasLocalCompleteIntersectionFibers_of_flat_isLocalCompleteIntersection f hflat hci

end Syntomic

end

end RingHom
