import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_161_1
import stacks_proof.stacks_project.Chap10.Definition_10_122_3
import stacks_proof.stacks_project.Chap10.Lemma_10_123_14
import stacks_proof.stacks_project.Chap10.Lemma_10_161_3
import stacks_proof.stacks_project.Chap10.Lemma_10_161_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

/-
Domain-style sampling:
* primary domain: quasi-finite finite-type extensions of Noetherian domains and permanence of the
  chapter owner `IsN2Ring`;
* sampled owner/bridge declarations:
  - `Algebra.FiniteType.QuasiFinite`, the chapter source-facing owner for a quasi-finite finite
    type extension from `Definition_10_122_3`;
  - `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`, the Zariski-main
    bridge from `Lemma_10_123_14`;
  - `isN2Ring_of_isLocalization`, the localization-stability bridge from `Lemma_10_161_3`;
  - `isN2Ring_of_isN2Ring_localizationAway`, the principal-open local-to-global bridge from
    `Lemma_10_161_4`.
* best owner abstraction: the source-facing extension hypothesis is
  `Algebra.FiniteType.QuasiFinite R S`; the public conclusion is the owner `IsN2Ring S`.
* primitive data: the quasi-finite extension owner `hRSqf`, the injectivity hypothesis on
  `algebraMap R S`, and the ambient Noetherian/domain data.
* derived API: the separate finite-type and quasi-finite components, the finite intermediate
  subalgebra from Zariski's Main Theorem, and localization/local-to-global permanence of
  `IsN2Ring`.

Source/core/bridge triage:
* `source-facing`: the permanence theorem for a quasi-finite extension of domains;
* `core/canonical`: `IsN2Ring`;
* `bridge/view`: the Zariski-main finite subalgebra and the localization/finite-extension
  permanence theorems above.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra R S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- The first helper is the finite-ascent input used for the finite subalgebra supplied by
Zariski's Main Theorem. -/
/-- Helper for Chap10 Lemma 10 161 5: an injective module-finite extension of Noetherian domains
preserves the `IsN2Ring` property upward. -/
private theorem isN2Ring_of_moduleFinite_base
    {A : Type*} {B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hAB : Function.Injective (algebraMap A B)) [IsN2Ring A] : IsN2Ring B := by
  -- Test the `N-2` condition on an arbitrary finite extension of `FractionRing B`.
  refine IsN2Ring.mk fun L => ?_
  intro _ _ _ _ _
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
  letI : FaithfulSMul A (FractionRing B) := inferInstance
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  letI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  letI : Algebra A L := (RingHom.comp (algebraMap B L) (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A B (FractionRing B) := inferInstance
  letI : Algebra (FractionRing A) L :=
    (RingHom.comp (algebraMap (FractionRing B) L)
      (algebraMap (FractionRing A) (FractionRing B))).toAlgebra
  letI : IsScalarTower (FractionRing A) (FractionRing B) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A (FractionRing A) L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      algebraMap A L x = algebraMap B L (algebraMap A B x) := by
        exact IsScalarTower.algebraMap_apply A B L x
      _ = algebraMap (FractionRing B) L (algebraMap B (FractionRing B) (algebraMap A B x)) := by
        exact IsScalarTower.algebraMap_apply B (FractionRing B) L (algebraMap A B x)
      _ = algebraMap (FractionRing B) L (algebraMap A (FractionRing B) x) := by
        rw [IsScalarTower.algebraMap_apply A B (FractionRing B)]
      _ = algebraMap (FractionRing B) L
          (algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) x)) := by
        rw [IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B)]
      _ = algebraMap (FractionRing A) L (algebraMap A (FractionRing A) x) := rfl
  have hfinFr : Module.Finite (FractionRing A) (FractionRing B) := by infer_instance
  letI : Module.Finite (FractionRing A) (FractionRing B) := hfinFr
  have hfinL : Module.Finite (FractionRing A) L := Module.Finite.trans (FractionRing B) L
  letI : FiniteDimensional (FractionRing A) L := by infer_instance
  have hfiniteA : Module.Finite A (integralClosure A L) := by
    -- The base `N-2` hypothesis applies after viewing `L` over `FractionRing A`.
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := A) (L := L)
  let fB : B →+* integralClosure A L :=
    (algebraMap B L).codRestrict (integralClosure A L) (fun b => by
      -- Elements of the finite `A`-algebra `B` are integral over `A`, hence land in the
      -- `A`-integral closure inside `L`.
      change IsIntegral A (algebraMap B L b)
      have hb : IsIntegral A b := IsIntegral.of_finite A b
      exact hb.map (IsScalarTower.toAlgHom A B L))
  letI : Algebra B (integralClosure A L) := fB.toAlgebra
  letI : IsScalarTower A B (integralClosure A L) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    rfl
  have hfiniteB : Module.Finite B (integralClosure A L) := by
    -- An `A`-finite module is also finite over the larger scalar ring `B`.
    exact Module.Finite.of_restrictScalars_finite A B (integralClosure A L)
  let incl : integralClosure B L →ₗ[B] integralClosure A L :=
    { toFun := fun x => ⟨(x : L), by
        -- Integrality descends through the integral finite extension `A → B`.
        change IsIntegral A (x : L)
        exact isIntegral_trans (A := B) (x : L) x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro b x
        have hfb : ((algebraMap B (integralClosure A L)) b : L) = algebraMap B L b := rfl
        ext
        simp [Algebra.smul_def, hfb] }
  have hinj : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : integralClosure A L => (z : L)) hxy)
  -- The `B`-integral closure is a submodule of a finite module over the Noetherian ring `B`.
  exact Module.Finite.of_injective incl hinj

/- The next helper extracts the finite principal-open cover on the target spectrum from the open
embedding part of Zariski's Main Theorem. -/
/-- Helper for Chap10 Lemma 10 161 5: an open embedding of spectra admits a finite basic-open
cover of the source whose chosen basic opens lie in the image. -/
private lemma exists_finset_basicOpen_subset_range_of_isOpenEmbedding
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hopen : IsOpenEmbedding (PrimeSpectrum.comap f)) :
    ∃ s : Finset A,
      Ideal.span (f '' (s : Set A)) = (⊤ : Ideal B) ∧
      ∀ g ∈ s, (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap f) := by
  classical
  let U : Set (PrimeSpectrum A) := Set.range (PrimeSpectrum.comap f)
  have hUopen : IsOpen U := hopen.isOpen_range
  have hchoose : ∀ q : PrimeSpectrum B,
      ∃ g : A, PrimeSpectrum.comap f q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ∧
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ U := by
    intro q
    -- Around each image point choose a basic open contained in the open image.
    obtain ⟨V, hVbasis, hqV, hVU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show PrimeSpectrum.comap f q ∈ U from ⟨q, rfl⟩) hUopen
    rcases hVbasis with ⟨g, rfl⟩
    exact ⟨g, hqV, hVU⟩
  choose g hgmem hgsub using hchoose
  have hcover : Set.univ ⊆ ⋃ q, (PrimeSpectrum.basicOpen (f (g q)) : Set (PrimeSpectrum B)) := by
    intro q hq
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hgmem q
  obtain ⟨t, htcover⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun q : PrimeSpectrum B => (PrimeSpectrum.basicOpen (f (g q)) : Set (PrimeSpectrum B)))
      (fun q => PrimeSpectrum.isOpen_basicOpen) hcover
  let s : Finset A := t.image g
  refine ⟨s, ?_, ?_⟩
  · have htop :
        (⨆ q : {q // q ∈ t}, PrimeSpectrum.basicOpen (f (g q.1))) =
          (⊤ : TopologicalSpace.Opens (PrimeSpectrum B)) := by
      ext p
      constructor
      · intro hp
        trivial
      · intro hp
        -- The finite subcover says every prime lies in one of the selected basic opens.
        have hpcover := htcover (show p ∈ (Set.univ : Set (PrimeSpectrum B)) from trivial)
        rcases Set.mem_iUnion.mp hpcover with ⟨q, hpq⟩
        rcases Set.mem_iUnion.mp hpq with ⟨hqt, hpbasic⟩
        exact (le_iSup (fun q : {q // q ∈ t} =>
          PrimeSpectrum.basicOpen (f (g q.1))) ⟨q, hqt⟩) hpbasic
    have hspan_range :
        Ideal.span (Set.range fun q : {q // q ∈ t} => f (g q.1)) = (⊤ : Ideal B) :=
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff
        (f := fun q : {q // q ∈ t} => f (g q.1))).mp htop
    have hsets : (Set.range fun q : {q // q ∈ t} => f (g q.1)) = f '' (s : Set A) := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨g q.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp ha with ⟨q, hqt, rfl⟩
        exact ⟨⟨q, hqt⟩, rfl⟩
    simpa [hsets] using hspan_range
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨q, hqt, rfl⟩
    exact hgsub q

/- This adapter converts the ZMT bijective away map into the `IsN2Ring` localization statement
needed by the finite-cover theorem. -/
/-- Helper for Chap10 Lemma 10 161 5: a bijective away map transports the `IsN2Ring` localization
from the source ring to the corresponding localization of the target. -/
private theorem isN2Ring_localizationAway_of_awayMap_bijective
    {A : Type*} {B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [IsN2Ring A] (g : A) [IsDomain (Localization.Away (algebraMap A B g))]
    (hbij : Function.Bijective (Localization.awayMap (algebraMap A B) g)) :
    IsN2Ring (Localization.Away (algebraMap A B g)) := by
  -- Upgrade the bijective ring map to an algebra equivalence over `A`.
  let e : Localization.Away g ≃ₐ[A] Localization.Away (algebraMap A B g) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A B) g) (by
      simpa [Localization.awayMapₐ] using hbij)
  letI : IsLocalization (Submonoid.powers g) (Localization.Away (algebraMap A B g)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g) e
  -- Once the target is identified as the localization of `A`, localization stability applies.
  exact isN2Ring_of_isLocalization (R := A)
    (Rₘ := Localization.Away (algebraMap A B g)) (Submonoid.powers g)

/- This packages the Zariski-main data in the exact form consumed by the final theorem. -/
/-- Helper for Chap10 Lemma 10 161 5: the finite Zariski-main subalgebra and its local away-map
comparisons imply `IsN2Ring S`. -/
private theorem isN2Ring_of_zariskiMain_finite_subalgebra
    (A : Subalgebra R S) [Module.Finite R A]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap A.val.toRingHom))
    (haway : ∀ g : A,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap A.val.toRingHom)) →
        Function.Bijective (Localization.awayMap A.val.toRingHom g))
    (hRA : Function.Injective (algebraMap R A)) [IsN2Ring R] : IsN2Ring S := by
  classical
  letI : IsDomain A := Subalgebra.isDomain (R := R) (A := S) A
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  haveI : IsN2Ring A := isN2Ring_of_moduleFinite_base (A := R) (B := A) hRA
  obtain ⟨s, hs_span, hs_subset⟩ :=
    exists_finset_basicOpen_subset_range_of_isOpenEmbedding A.val.toRingHom hopen
  let t : Finset S := (s.image fun a : A => (a : S)).erase 0
  have ht_span : Ideal.span (t : Set S) = ⊤ := by
    -- Push the finite cover from `A` to `S`, then discard the harmless zero generator.
    have himage : ((s.image fun a : A => (a : S)) : Set S) =
        A.val.toRingHom '' (s : Set A) := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [← hs_span]
    calc
      Ideal.span (t : Set S) =
          Ideal.span (((s.image fun a : A => (a : S)) : Set S) \ {0}) := by
        simp [t]
      _ = Ideal.span ((s.image fun a : A => (a : S)) : Set S) :=
        Ideal.span_sdiff_singleton_zero
      _ = Ideal.span (A.val.toRingHom '' (s : Set A)) := by rw [himage]
  have hdom : ∀ f : t, IsDomain (Localization.Away f.1) := by
    intro f
    refine IsLocalization.isDomain_of_le_nonZeroDivisors
      (R := S) (M := Submonoid.powers f.1) (S := Localization.Away f.1) ?_
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rcases (show ∃ n : ℕ, f.1 ^ n = x by
      simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
    exact pow_ne_zero n (Finset.mem_erase.mp f.2).1
  refine isN2Ring_of_isN2Ring_localizationAway (R := S) t ht_span hdom ?_
  intro f
  rcases f with ⟨x, hx⟩
  have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hx).1
  have hx_image : x ∈ s.image (fun a : A => (a : S)) := (Finset.mem_erase.mp hx).2
  rcases Finset.mem_image.mp hx_image with ⟨a, ha, hax⟩
  have ha_ne : (a : S) ≠ 0 := by
    intro hzero
    exact hx_ne (hax ▸ hzero)
  have ha_map_ne : algebraMap A S a ≠ 0 := by simpa using ha_ne
  subst x
  letI : IsDomain (Localization.Away (algebraMap A S a)) := by
    refine IsLocalization.isDomain_of_le_nonZeroDivisors
      (R := S) (M := Submonoid.powers (algebraMap A S a))
      (S := Localization.Away (algebraMap A S a)) ?_
    intro y hy
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rcases (show ∃ n : ℕ, (algebraMap A S a) ^ n = y by
      simpa [Submonoid.mem_powers_iff] using hy) with ⟨n, rfl⟩
    exact pow_ne_zero n ha_map_ne
  -- The selected basic open lies in the image, so ZMT gives the required local comparison.
  simpa using
    isN2Ring_localizationAway_of_awayMap_bijective (A := A) (B := S) a
      (haway a (hs_subset a ha))

-- Proof sketch: let `K = FractionRing R` and `L = FractionRing S`. Quasi-finiteness and
-- injectivity of `R → S` imply that `L / K` is finite. Applying the `N-2` hypothesis to `R`
-- shows that the integral closure of `R` in `L` is finite over `R`, hence so is the integral
-- closure of `R` in `S`. Zariski's Main Theorem gives a principal-open cover on which `S` agrees
-- with that finite integral closure, reducing to the finite-extension case; then one applies the
-- finite stability of `N-2` together with localization and transitivity of integral closure.
/-- Chap10 Lemma 10 161 5: if `R` is a Noetherian `N-2` domain and `R ⊂ S` is a
quasi-finite extension of domains, then `S` is `N-2`. -/
@[stacks 032I]
theorem isN2Ring_of_quasiFinite_extension
    (hRSqf : Algebra.FiniteType.QuasiFinite R S)
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring R] :
    IsN2Ring S := by
  -- Split the source-facing quasi-finite finite-type hypothesis into the instances expected by
  -- the Zariski-main theorem.
  letI : Algebra.FiniteType R S := hRSqf.finiteType
  letI : Algebra.QuasiFinite R S := hRSqf.toQuasiFinite
  obtain ⟨A, _, hAfin, hopen, haway⟩ :=
    exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties (R := R) (S := S)
  letI : Module.Finite R A := hAfin
  have hRA : Function.Injective (algebraMap R A) := by
    -- Equality in the finite subalgebra is detected after composing with the original
    -- injective map `R → S`.
    intro x y hxy
    apply hRS
    simpa using congrArg (fun z : A => (z : S)) hxy
  -- Apply the finite-subalgebra local-to-global package supplied above.
  exact isN2Ring_of_zariskiMain_finite_subalgebra (R := R) (S := S) A hopen haway hRA

end
