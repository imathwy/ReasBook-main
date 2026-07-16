import stacks_proof.stacks_project.Chap10.«10_118_3_2»
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap10.Lemma_10_118_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: generic-flatness loci on prime spectra under localization away from one element;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical bridge: `primeSpectrum_localizationAway_homeomorph_D f` and its pointwise
  description via `PrimeSpectrum.comap`;
* bridge/view target of this file: transport `goodLocus` across the canonical identification
  `Spec(R_f) ≃ D(f)`, with the restriction to `D(f)` expressed canonically as a subtype preimage
  rather than a separate wrapper set. -/

/-- Helper for Lemma 10.118.5: membership in `goodLocus` is equivalent to the existence of a
single witness element avoiding the given prime. -/
lemma mem_goodLocus_iff (p : PrimeSpectrum R) :
    p ∈ goodLocus R S M ↔ ∃ g : R, LocalizationCondition R S M g ∧ g ∉ p.asIdeal := by
  -- Unfold the defining union and rewrite basic-open membership into non-membership in the prime.
  rw [goodLocus_eq_iUnion]
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨g, hg⟩
    exact ⟨g.1, g.2, (PrimeSpectrum.mem_basicOpen g.1 p).mp hg⟩
  · rintro ⟨g, hgcond, hg⟩
    refine Set.mem_iUnion.mpr ?_
    exact ⟨⟨g, hgcond⟩, (PrimeSpectrum.mem_basicOpen g p).mpr hg⟩

/-- Helper for Lemma 10.118.5: the canonical map `R_f → R_(fg)` is compatible with the original
`R`-algebra structures, so `R_(fg)` sits in a scalar tower over `R_f`. -/
lemma away_mul_isScalarTower (f g : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
      (IsLocalization.Away.awayToAwayRight
        (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away (f * g)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
  -- The comparison map `R_f → R_(fg)` still agrees with the original structure map from `R`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  symm
  simpa using
    (IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away f) (P := Localization.Away (f * g)) (x := f) (y := g) x)

/-- Helper for Lemma 10.118.5: inside `R_f`, the elements `(fg) / 1` and `g / 1` are associated
because `f / 1` is a unit. -/
lemma away_mul_associated_right (f g : R) :
    Associated (algebraMap R (Localization.Away f) (f * g))
      (algebraMap R (Localization.Away f) g) := by
  -- After rewriting `(fg) / 1` as `(f / 1) * (g / 1)`, cancel the unit `f / 1`.
  rw [map_mul]
  simpa [mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f)))

/-- Helper for Lemma 10.118.5: the iterated localization `(R_f)_(g / 1)` carries the composed
`R`-algebra structure, and this agrees with the evident scalar tower through `R_f`. -/
lemma away_map_isScalarTower (f g : R) :
    letI : Algebra R (Localization.Away (algebraMap R (Localization.Away f) g)) :=
      ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))).comp
        (algebraMap R (Localization.Away f))).toAlgebra
    IsScalarTower R (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) := by
  -- The composed scalar structure is the canonical tower instance for the iterated localization.
  exact inferInstance

/-- Helper for Lemma 10.118.5: both `R_(fg)` and `(R_f)_(g / 1)` localize `R` away from `fg`, so
they are canonically isomorphic as `R`-algebras. -/
noncomputable def away_mul_base_algEquiv (f g : R) :
    Localization.Away (f * g) ≃ₐ[R]
      Localization.Away (algebraMap R (Localization.Away f) g) :=
  -- Uniqueness of localization away from `fg` supplies the canonical comparison map.
  IsLocalization.algEquiv (Submonoid.powers (f * g)) (Localization.Away (f * g))
    (Localization.Away (algebraMap R (Localization.Away f) g))

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of modules descends along a ring
equivalence by viewing the target module through the induced restricted scalar action. -/
lemma moduleFinitePresentationCompHomOfRingEquiv
    {A : Type*} {B : Type*} {N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (e : A ≃+* B) [Module.FinitePresentation B N] :
    letI : Module A N := Module.compHom N e.toRingHom
    Module.FinitePresentation A N := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : Module A N := Module.compHom N e.toRingHom
  letI : IsScalarTower A B N := IsScalarTower.restrictScalars A B N
  -- First transport the rank-one presentation of the base ring, then use transitivity for
  -- finite presentations of modules.
  have hfpB : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  letI : Module.FinitePresentation A B := hfpB
  exact Module.FinitePresentation.trans A N B

/-- Helper for Chap10 Lemma 10 118 5: freeness of modules descends along a ring equivalence by
restricting scalars through the equivalence. -/
lemma moduleFreeCompHomOfRingEquiv
    {A : Type*} {B : Type*} {N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (e : A ≃+* B) [Module.Free B N] :
    letI : Module A N := Module.compHom N e.toRingHom
    Module.Free A N := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : Module A N := Module.compHom N e.toRingHom
  letI : IsScalarTower A B N := IsScalarTower.restrictScalars A B N
  -- The base ring is free over the source via the ring equivalence; transitivity carries freeness
  -- of the module through the same scalar tower.
  have hfreeB : Module.Free A B :=
    Module.Free.of_equiv' (inferInstance : Module.Free A A) (Module.compHom.toLinearEquiv e)
  exact @Module.Free.trans A B N inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hfreeB

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of algebras descends along a ring
equivalence when the target algebra is viewed by restriction of scalars. -/
lemma algebraFinitePresentationCompHomOfRingEquiv
    {A : Type*} {B : Type*} {C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra B C] (e : A ≃+* B) [Algebra.FinitePresentation B C] :
    letI : Algebra A C := Algebra.compHom C e.toRingHom
    Algebra.FinitePresentation A C := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : Algebra A C := Algebra.compHom C e.toRingHom
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- The base equivalence presents `B` finitely over `A`; transitivity then carries the algebra
  -- finite-presentation structure from `B` to `A`.
  have hcomm : ∀ a : A, e a = algebraMap A B a := by
    intro a
    rfl
  have hfpB : Algebra.FinitePresentation A B := by
    let eAlg : A ≃ₐ[A] B := AlgEquiv.ofRingEquiv (R := A) (f := e) hcomm
    exact Algebra.FinitePresentation.equiv eAlg
  letI : Algebra.FinitePresentation A B := hfpB
  exact Algebra.FinitePresentation.trans A B C

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of algebras is transported across
compatible equivalences of both the base ring and the algebra. -/
lemma algebraFinitePresentationOfRingEquiv
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    [Algebra.FinitePresentation A B] :
    Algebra.FinitePresentation A' B' := by
  letI : Algebra A A' := eA.toRingHom.toAlgebra
  letI : Algebra A B' := Algebra.compHom B' eA.toRingHom
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Transport the presentation first over the old base, then descend along the finite
  -- presentation of the equivalent base ring.
  have hbaseCompat : ∀ a : A, eA a = algebraMap A A' a := by
    intro a
    rfl
  have hfpBase : Algebra.FinitePresentation A A' := by
    let eAlg : A ≃ₐ[A] A' := AlgEquiv.ofRingEquiv (R := A) (f := eA) hbaseCompat
    exact Algebra.FinitePresentation.equiv eAlg
  have hfpTargetOverA : Algebra.FinitePresentation A B' := by
    let eAlg : B ≃ₐ[A] B' := AlgEquiv.ofRingEquiv (R := A) (f := eB) hcompat
    exact Algebra.FinitePresentation.equiv eAlg
  letI : Algebra.FinitePresentation A B' := hfpTargetOverA
  letI : Algebra.FiniteType A A' := Algebra.FiniteType.of_finitePresentation
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'

/-- Helper for Chap10 Lemma 10 118 5: a localized module for powers of one element is also a
localized module for powers of an associated element. -/
lemma isLocalizedModulePowersOfAssociated
    {A : Type*} {N : Type*} {N' : Type*}
    [CommRing A] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    {x y : A} (hxy : Associated x y) (f : N →ₗ[A] N')
    [IsLocalizedModule (Submonoid.powers x) f] :
    IsLocalizedModule (Submonoid.powers y) f := by
  obtain ⟨u, rfl⟩ := hxy
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    -- Units from the associated factor multiply the already-inverted powers of `x`.
    rcases (Submonoid.mem_powers_iff s (x * u)).mp hs with ⟨n, hn⟩
    have hxunit : IsUnit (algebraMap A (Module.End A N') (x ^ n)) :=
      IsLocalizedModule.map_units f ⟨x ^ n,
        Submonoid.pow_mem (Submonoid.powers x) (Submonoid.mem_powers x) n⟩
    have huunit : IsUnit (algebraMap A (Module.End A N') ((↑u : A) ^ n)) :=
      IsUnit.map (algebraMap A (Module.End A N')) ((u ^ n : Aˣ).isUnit)
    simpa [← hn, mul_pow, map_mul] using hxunit.mul huunit
  · intro z
    -- Clear an `x`-power denominator and then multiply the numerator by the corresponding unit.
    obtain ⟨⟨m, sx⟩, hsx⟩ := IsLocalizedModule.surj (Submonoid.powers x) f z
    rcases (Submonoid.mem_powers_iff sx.1 x).mp sx.2 with ⟨n, hn⟩
    let sy : Submonoid.powers (x * u) :=
      ⟨(x * u) ^ n, Submonoid.pow_mem (Submonoid.powers (x * u))
        (Submonoid.mem_powers (x * u)) n⟩
    refine ⟨⟨((↑u : A) ^ n) • m, sy⟩, ?_⟩
    have hsx' : (x ^ n : A) • z = f m := by
      simpa [Submonoid.smul_def, hn] using hsx
    calc
      sy • z = ((x * u) ^ n : A) • z := by simp [Submonoid.smul_def, sy]
      _ = ((↑u : A) ^ n) • ((x ^ n : A) • z) := by
        rw [mul_pow, mul_comm (x ^ n) ((↑u : A) ^ n), mul_smul]
      _ = ((↑u : A) ^ n) • f m := by rw [hsx']
      _ = f (((↑u : A) ^ n) • m) := by rw [map_smul]
  · intro m₁ m₂ h
    -- The equality criterion is transported by multiplying the clearing power by the same unit.
    obtain ⟨sx, hsx⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers x) (f := f) h
    rcases (Submonoid.mem_powers_iff sx.1 x).mp sx.2 with ⟨n, hn⟩
    let sy : Submonoid.powers (x * u) :=
      ⟨(x * u) ^ n, Submonoid.pow_mem (Submonoid.powers (x * u))
        (Submonoid.mem_powers (x * u)) n⟩
    refine ⟨sy, ?_⟩
    have hsx' : (x ^ n : A) • m₁ = (x ^ n : A) • m₂ := by
      simpa [Submonoid.smul_def, hn] using hsx
    calc
      sy • m₁ = ((x * u) ^ n : A) • m₁ := by simp [Submonoid.smul_def, sy]
      _ = ((↑u : A) ^ n) • ((x ^ n : A) • m₁) := by
        rw [mul_pow, mul_comm (x ^ n) ((↑u : A) ^ n), mul_smul]
      _ = ((↑u : A) ^ n) • ((x ^ n : A) • m₂) := by rw [hsx']
      _ = ((x * u) ^ n : A) • m₂ := by
        rw [mul_pow, mul_comm (x ^ n) ((↑u : A) ^ n), mul_smul]
      _ = sy • m₂ := by simp [Submonoid.smul_def, sy]

/-- Helper for Chap10 Lemma 10 118 5: scalar multiplication units remain units after restricting
scalars along an algebra map. -/
lemma isUnitRestrictScalarsAlgebraMapEnd
    {A : Type*} {B : Type*} {P : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (a : A)
    (h : IsUnit (algebraMap B (Module.End B P) (algebraMap A B a))) :
    IsUnit (algebraMap A (Module.End A P) a) := by
  -- Reduce unithood to bijectivity and identify the two scalar endomorphisms pointwise.
  rw [Module.End.isUnit_iff] at h ⊢
  convert h using 1
  ext x
  exact (algebraMap_smul B a x).symm

/-- Helper for Chap10 Lemma 10 118 5: localizing a module away from an algebra-map image remains
a localization after restricting scalars. -/
lemma isLocalizedModuleRestrictScalarsPowersAlgebraMap
    {A : Type*} {B : Type*} {N : Type*} {N' : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module B N'] [Module A N'] [IsScalarTower A B N']
    (t : A) (f : N →ₗ[B] N')
    [IsLocalizedModule (Submonoid.powers (algebraMap A B t)) f] :
    IsLocalizedModule (Submonoid.powers t) (f.restrictScalars A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    -- Denominator powers map to denominator powers under the algebra map.
    rcases (Submonoid.mem_powers_iff s.1 t).mp s.2 with ⟨n, hn⟩
    apply isUnitRestrictScalarsAlgebraMapEnd (A := A) (B := B) (P := N') (a := s.1)
    have hsB : algebraMap A B s.1 ∈ Submonoid.powers (algebraMap A B t) := by
      rw [← hn, map_pow]
      exact Submonoid.pow_mem (Submonoid.powers (algebraMap A B t))
        (Submonoid.mem_powers (algebraMap A B t)) n
    exact IsLocalizedModule.map_units f ⟨algebraMap A B s.1, hsB⟩
  · intro y
    -- Pull the standard surjectivity witness back to the matching power in the source ring.
    obtain ⟨⟨x, sB⟩, hsB_y⟩ :=
      IsLocalizedModule.surj (Submonoid.powers (algebraMap A B t)) f y
    rcases (Submonoid.mem_powers_iff sB.1 (algebraMap A B t)).mp sB.2 with ⟨n, hn⟩
    let sA : Submonoid.powers t :=
      ⟨t ^ n, Submonoid.pow_mem (Submonoid.powers t) (Submonoid.mem_powers t) n⟩
    refine ⟨⟨x, sA⟩, ?_⟩
    have hsval : algebraMap A B sA.1 = sB.1 := by
      simp [sA, hn, map_pow]
    calc
      sA • y = (algebraMap A B sA.1) • y := by
        simp [Submonoid.smul_def]
      _ = sB • y := by
        rw [hsval]
        simp [Submonoid.smul_def]
      _ = f x := hsB_y
  · intro x₁ x₂ h
    -- The equality criterion is transported using the same exponent chosen in the target ring.
    obtain ⟨cB, hcB⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers (algebraMap A B t)) (f := f) h
    rcases (Submonoid.mem_powers_iff cB.1 (algebraMap A B t)).mp cB.2 with ⟨n, hn⟩
    let cA : Submonoid.powers t :=
      ⟨t ^ n, Submonoid.pow_mem (Submonoid.powers t) (Submonoid.mem_powers t) n⟩
    refine ⟨cA, ?_⟩
    have hcval : algebraMap A B cA.1 = cB.1 := by
      simp [cA, hn, map_pow]
    calc
      cA • x₁ = (algebraMap A B cA.1) • x₁ := by
        simp [Submonoid.smul_def]
      _ = cB • x₁ := by
        rw [hcval]
        simp [Submonoid.smul_def]
      _ = cB • x₂ := hcB
      _ = (algebraMap A B cA.1) • x₂ := by
        rw [hcval]
        simp [Submonoid.smul_def]
      _ = cA • x₂ := by
        simp [Submonoid.smul_def]

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of an algebra survives away
localization on the base and target. -/
lemma awayAlgebraFinitePresentationOverBase
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (t : A) :
    Algebra.FinitePresentation (Localization.Away t) (Localization.Away (algebraMap A B t)) := by
  -- Pin the scalar tower through the canonical away map before applying the restriction theorem.
  letI : IsScalarTower A (Localization.Away t) (Localization.Away (algebraMap A B t)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : Algebra.FinitePresentation A (Localization.Away (algebraMap A B t)) := by
    infer_instance
  letI : Algebra.FiniteType A (Localization.Away t) :=
    Algebra.FiniteType.of_finitePresentation
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A
    (Localization.Away t) (Localization.Away (algebraMap A B t))

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of a module survives away
localization. -/
lemma awayModuleFinitePresentation
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.FinitePresentation A N] (t : A) :
    Module.FinitePresentation (Localization.Away t) (LocalizedModule.Away t N) := by
  -- The localized-module finite-presentation instance is the canonical one from mathlib.
  infer_instance

/-- Helper for Chap10 Lemma 10 118 5: localizing an already-free algebra once more keeps it free
over the iterated away base. -/
lemma iteratedAwayFreeAlgebraOverBase
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let At := Localization.Away t
  let Bt := Localization.Away (algebraMap A B t)
  let alg := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := alg.toSMul
  letI : Algebra At Bt := alg
  -- Present the target algebra localization as a localized module over the already-free algebra.
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  have hIso : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Bt :=
    inferInstance
  have hloc : IsLocalizedModule (Submonoid.powers t)
      (IsScalarTower.toAlgHom A B Bt).toLinearMap :=
    (isLocalizedModule_iff_isLocalization (S := Submonoid.powers t) (A := B) (Aₛ := Bt)).mpr
      hIso
  have hfree : Module.Free A B := hf.free_algebra
  exact @Module.free_of_isLocalizedModule A B _ _ _ At Bt _ _ _ _ _ _
    (Submonoid.powers t) (IsScalarTower.toAlgHom A B Bt).toLinearMap inferInstance hloc hfree

/-- Helper for Chap10 Lemma 10 118 5: localizing an already-free module once more keeps it free
over the iterated away base. -/
lemma iteratedAwayFreeModuleOverBase
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (LocalizedModule.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))
        (LocalizedModule.Away (algebraMap R S f) M)) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let At := Localization.Away t
  let c : B := algebraMap A B t
  let Nt := LocalizedModule.Away c N
  let alg := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At (Localization.Away c) := alg.toSMul
  letI : Algebra At (Localization.Away c) := alg
  -- Keep the module localization in the scalar-tower spelling used by `free_of_isLocalizedModule`.
  letI : IsScalarTower A At (Localization.Away c) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower A B N := by
    refine IsScalarTower.mk ?_
    intro a b n
    change ((algebraMap A B) a * b) • n = (algebraMap A B a) • (b • n)
    exact smul_assoc (algebraMap A B a) b n
  let moduleA : Module A Nt := Module.compHom Nt (algebraMap A B)
  letI : SMul A Nt := moduleA.toSMul
  letI : Module A Nt := moduleA
  letI : IsScalarTower A B Nt := by
    refine IsScalarTower.mk ?_
    intro a b n
    change ((algebraMap A B) a * b) • n = (algebraMap A B a) • (b • n)
    exact smul_assoc (algebraMap A B a) b n
  let moduleAt : Module At Nt := Module.compHom Nt (algebraMap At (Localization.Away c))
  letI : SMul At Nt := moduleAt.toSMul
  letI : Module At Nt := moduleAt
  letI : IsScalarTower A At Nt := by
    refine IsScalarTower.mk ?_
    intro a b n
    rw [Algebra.smul_def]
    rw [show ∀ x : At, x • n = (algebraMap At (Localization.Away c) x) • n from fun x ↦ rfl]
    rw [show b • n = (algebraMap At (Localization.Away c) b) • n from rfl]
    rw [map_mul]
    rw [show algebraMap At (Localization.Away c) (algebraMap A At a) =
        algebraMap B (Localization.Away c) (algebraMap A B a) from
      (IsScalarTower.algebraMap_apply A At (Localization.Away c) a).symm.trans
        (IsScalarTower.algebraMap_apply A B (Localization.Away c) a)]
    rw [mul_smul]
    rw [algebraMap_smul]
    rfl
  let locB : N →ₗ[B] Nt := LocalizedModule.mkLinearMap (Submonoid.powers c) N
  let locA : N →ₗ[A] Nt := locB.restrictScalars A
  have hfree : Module.Free A N := hf.free_module
  have hloc : IsLocalizedModule (Submonoid.powers t) locA := by
    -- Restrict the canonical `B`-localization at `algebraMap A B t` to an `A`-localization.
    exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := A) (B := B) (N := N)
      (N' := Nt) t locB
  exact @Module.free_of_isLocalizedModule A N _ _ _ At Nt _ _ _ _ _ _
    (Submonoid.powers t) locA inferInstance hloc hfree

/-- Helper for Chap10 Lemma 10 118 5: once the condition holds at `f`, all four fields survive
one more localization in the already-localized `f`-world. -/
lemma localizationConditionSecondAway
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  letI : Algebra.FinitePresentation A B := hf.finitePresentation_algebra
  letI : Module.FinitePresentation B N := hf.finitePresentation_module
  -- Package the standard finite-presentation localizations with the two freeness transports.
  have hfpAlg : Algebra.FinitePresentation (Localization.Away t)
      (Localization.Away (algebraMap A B t)) :=
    awayAlgebraFinitePresentationOverBase (A := A) (B := B) t
  have hfpModule : Module.FinitePresentation (Localization.Away (algebraMap A B t))
      (LocalizedModule.Away (algebraMap A B t) N) :=
    awayModuleFinitePresentation (A := B) (N := N) (algebraMap A B t)
  have hfreeAlg : Module.Free (Localization.Away t)
      (Localization.Away (algebraMap A B t)) :=
    iteratedAwayFreeAlgebraOverBase (R := R) (S := S) (M := M) f g hf
  have hfreeModule : Module.Free (Localization.Away t)
      (LocalizedModule.Away (algebraMap A B t) N) :=
    iteratedAwayFreeModuleOverBase (R := R) (S := S) (M := M) f g hf
  exact
    { finitePresentation_algebra := hfpAlg
      finitePresentation_module := hfpModule
      free_algebra := hfreeAlg
      free_module := hfreeModule }

/-- Helper for Chap10 Lemma 10 118 5: finite presentation transports across a linear equivalence
with the source proof supplied explicitly. -/
private theorem moduleFinitePresentationOfLinearEquivExplicit
    {A N N' : Type*} [Ring A] [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (hfp : Module.FinitePresentation A N) :
    Module.FinitePresentation A N' := by
  -- Install the source finite-presentation proof only for this transport step.
  letI : Module.FinitePresentation A N := hfp
  exact Module.FinitePresentation.of_equiv e

/-- Helper for Chap10 Lemma 10 118 5: a linear equivalence over a base ring transports finite
presentation after extending scalars to a localization. -/
private theorem moduleFinitePresentationOfExtendedLocalizedEquiv
    {A Aₛ N N' : Type*} [CommRing A] (T : Submonoid A)
    [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization T Aₛ]
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module Aₛ N'] [IsScalarTower A Aₛ N']
    (e : N ≃ₗ[A] N') (hfp : Module.FinitePresentation Aₛ N) :
    Module.FinitePresentation Aₛ N' := by
  -- Extend the comparison to the localized scalar ring before applying linear transport.
  exact moduleFinitePresentationOfLinearEquivExplicit
    (e.extendScalarsOfIsLocalization T Aₛ) hfp

/-- Helper for Chap10 Lemma 10 118 5: compatible ring equivalences identify the pulled-back scalar
action on the source module. -/
private theorem sourceSmulOfCompatibleRingEquivCompHom
    {A A' B B' N : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a)) :
    letI : Module B' N := Module.compHom N (eB.symm : B' →+* B)
    ∀ (a : A) (n : N), algebraMap A' B' (eA a) • n = a • n := by
  letI : Module B' N := Module.compHom N (eB.symm : B' →+* B)
  intro a n
  change eB.symm (algebraMap A' B' (eA a)) • n = a • n
  have hs : eB.symm (algebraMap A' B' (eA a)) = algebraMap A B a := by
    apply eB.injective
    rw [eB.apply_symm_apply, hcompat a]
  rw [hs]
  exact IsScalarTower.algebraMap_smul B a n

/-- Helper for Chap10 Lemma 10 118 5: a compatible target-ring equivalence is semilinear for the
algebra scalar actions. -/
private lemma ringEquivMapSmulOfCompatible
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (a : A) (b : B) :
    eB (a • b) = eA a • eB b := by
  -- Expand scalar multiplication in both algebras and use compatibility of algebra maps.
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcompat a]

/-- Helper for Chap10 Lemma 10 118 5: freeness of an algebra as a module is invariant under
compatible equivalences of base and target rings. -/
private theorem moduleFreeOfCompatibleRingEquiv
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hfree : Module.Free A B) :
    Module.Free A' B' := by
  -- Package the compatible ring equivalence as a semilinear equivalence.
  letI : RingHomInvPair (eA : A →+* A') (eA.symm : A' →+* A) :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair (eA.symm : A' →+* A) (eA : A →+* A') :=
    RingHomInvPair.symm (eA : A →+* A') (eA.symm : A' →+* A)
  let e : B ≃ₛₗ[(eA : A →+* A')] B' :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := fun a b ↦ ringEquivMapSmulOfCompatible eA eB hcompat a b }
  letI : Module.Free A B := hfree
  exact Module.Free.of_equiv e

/-- Helper for Chap10 Lemma 10 118 5: freeness transports through a localized linear equivalence
when the source and target base scalar actions are compatible. -/
private theorem moduleFreeOfExtendedLocalizedEquiv
    {C B' A A' N N' : Type*} [CommRing C] (T : Submonoid C)
    [CommRing B'] [Algebra C B'] [IsLocalization T B']
    [CommRing A] [CommRing A'] [Algebra A' B']
    [AddCommGroup N] [Module C N] [Module B' N] [IsScalarTower C B' N] [Module A N]
    [AddCommGroup N'] [Module C N'] [Module B' N'] [IsScalarTower C B' N'] [Module A' N']
    [IsScalarTower A' B' N']
    (eA : A ≃+* A') (e : N ≃ₗ[C] N')
    (hsource : ∀ (a : A) (n : N), algebraMap A' B' (eA a) • n = a • n)
    (hfree : Module.Free A N) :
    Module.Free A' N' := by
  -- Extend the module comparison to the localized target ring, then read it semilinearly over `eA`.
  letI : RingHomInvPair (eA : A →+* A') (eA.symm : A' →+* A) :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair (eA.symm : A' →+* A) (eA : A →+* A') :=
    RingHomInvPair.symm (eA : A →+* A') (eA.symm : A' →+* A)
  let eB' : N ≃ₗ[B'] N' := e.extendScalarsOfIsLocalization T B'
  let eSemi : N ≃ₛₗ[(eA : A →+* A')] N' :=
    { toFun := eB'
      invFun := eB'.symm
      left_inv := eB'.left_inv
      right_inv := eB'.right_inv
      map_add' := eB'.map_add
      map_smul' := fun a n ↦ by
        calc
          eB' (a • n) = eB' ((algebraMap A' B' (eA a)) • n) := by
            rw [hsource a n]
          _ = (algebraMap A' B' (eA a)) • eB' n := by
            rw [map_smul]
          _ = eA a • eB' n := by
            exact IsScalarTower.algebraMap_smul B' (eA a) (eB' n) }
  letI : Module.Free A N := hfree
  exact Module.Free.of_equiv eSemi

/-- Helper for Chap10 Lemma 10 118 5: the canonical map into an iterated localized module. -/
private noncomputable abbrev iteratedLocalizedModuleMkLinearMap
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    N →ₗ[A] LocalizedModule S (LocalizedModule S' N) :=
  (LocalizedModule.mkLinearMap S (LocalizedModule S' N)).comp
    (LocalizedModule.mkLinearMap S' N)

/-- Helper for Chap10 Lemma 10 118 5: an invertible scalar endomorphism remains invertible after
localizing a module. -/
private theorem localizedModuleEndIsUnit
    {A : Type*} [CommRing A] (S : Submonoid A)
    {N : Type*} [AddCommGroup N] [Module A N] {r : A}
    (h : IsUnit (algebraMap A (Module.End A N) r)) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule S N)) r) := by
  -- Localize the scalar endomorphism and compare it with scalar multiplication upstairs.
  let localizedEnd :
      Module.End A (LocalizedModule S N) :=
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S N) (algebraMap A (Module.End A N) r)
  have hbij : Function.Bijective localizedEnd := by
    have hbij₀ : Function.Bijective (algebraMap A (Module.End A N) r) :=
      (Module.End.isUnit_iff _).mp h
    constructor
    · exact
        IsLocalizedModule.map_injective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.1
    · exact
        IsLocalizedModule.map_surjective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.2
  have hEq :
      localizedEnd = algebraMap A (Module.End A (LocalizedModule S N)) r := by
    -- Check the localized endomorphism on canonical numerator representatives.
    ext x
    induction x using LocalizedModule.induction_on with
    | _ n s =>
        simp [localizedEnd, IsLocalizedModule.map_LocalizedModules, LocalizedModule.smul'_mk]
  rw [← hEq]
  exact (Module.End.isUnit_iff _).2 hbij

/-- Helper for Chap10 Lemma 10 118 5: iterated localization localizes at the supremum of the two
denominator submonoids. -/
private instance iteratedLocalizedModuleIsLocalizedModuleSup
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    IsLocalizedModule (S ⊔ S')
      (iteratedLocalizedModuleMkLinearMap (A := A) (N := N) S S') := by
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨s, hs, s', hs', hss'⟩
    have hx : (x : A) = s * s' := by
      simpa using hss'.symm
    -- The outer localization inverts `S`, and the inner denominators remain units upstairs.
    have hsUnit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s) :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ⟨s, hs⟩
    have hs'Unit₀ :
        IsUnit (algebraMap A (Module.End A (LocalizedModule S' N)) s') :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S' N) ⟨s', hs'⟩
    have hs'Unit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s') :=
      localizedModuleEndIsUnit (S := S) hs'Unit₀
    rw [hx, map_mul]
    exact hsUnit.mul hs'Unit
  · intro m
    -- Clear the outer denominator, then the inner denominator, and combine them in the supremum.
    obtain ⟨⟨p, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) m
    obtain ⟨⟨x, s'⟩, hs'⟩ :=
      IsLocalizedModule.surj S' (LocalizedModule.mkLinearMap S' N) p
    refine ⟨⟨x, ⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩⟩, ?_⟩
    change (s.1 * s'.1 : A) • m =
      (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ((LocalizedModule.mkLinearMap S' N) x)
    calc
      (s.1 * s'.1 : A) • m = (s'.1 * s.1 : A) • m := by rw [mul_comm]
      _ = s'.1 • (s • m) := by
        change (s'.1 * s.1 : A) • m = (s'.1 : A) • ((s : A) • m)
        rw [smul_smul]
      _ = s'.1 • (LocalizedModule.mkLinearMap S (LocalizedModule S' N) p) := by rw [hs]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) (s'.1 • p) := by
        rw [LinearMap.map_smul_of_tower]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
            ((LocalizedModule.mkLinearMap S' N) x) := by
        simpa using congrArg (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) hs'
  · intro x₁ x₂ h
    -- Equality clears first in the outer localization and then in the inner localization.
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := S)
        (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N)) h
    have hs'₀ :
        (LocalizedModule.mkLinearMap S' N) (s • x₁) =
          (LocalizedModule.mkLinearMap S' N) (s • x₂) := by
      simpa [LinearMap.map_smul_of_tower] using hs
    obtain ⟨s', hs'⟩ :=
      IsLocalizedModule.exists_of_eq (S := S')
        (f := LocalizedModule.mkLinearMap S' N) hs'₀
    refine ⟨⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩, ?_⟩
    change (s.1 * s'.1 : A) • x₁ = (s.1 * s'.1 : A) • x₂
    calc
      (s.1 * s'.1 : A) • x₁ = (s'.1 * s.1 : A) • x₁ := by rw [mul_comm]
      _ = s'.1 • (s • x₁) := by
        change (s'.1 * s.1 : A) • x₁ = (s'.1 : A) • ((s : A) • x₁)
        rw [smul_smul]
      _ = s'.1 • (s • x₂) := by simpa using hs'
      _ = (s'.1 * s.1 : A) • x₂ := by
        change (s'.1 : A) • ((s : A) • x₂) = (s'.1 * s.1 : A) • x₂
        rw [smul_smul]
      _ = (s.1 * s'.1 : A) • x₂ := by rw [mul_comm]

/-- Helper for Chap10 Lemma 10 118 5: direct localization away from `ab` is localization at the
supremum of the two principal denominator submonoids. -/
private instance mkLinearMapIsLocalizedModuleSupAwayMul
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  refine
    IsLocalizedModule.of_exists_mul_mem (S := Submonoid.powers (a * b))
      (T := Submonoid.powers a ⊔ Submonoid.powers b) ?_ ?_
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
  · intro x hx
    rcases (Submonoid.mem_powers_iff x (a * b)).mp hx with ⟨n, rfl⟩
    simpa [mul_pow] using
      (Submonoid.mul_mem_sup
        (show a ^ n ∈ Submonoid.powers a from ⟨n, rfl⟩)
        (show b ^ n ∈ Submonoid.powers b from ⟨n, rfl⟩))
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨y, hy, z, hz, hyz⟩
    have hx : (x : A) = y * z := by
      simpa using hyz.symm
    rcases (Submonoid.mem_powers_iff y a).mp hy with ⟨m, rfl⟩
    rcases (Submonoid.mem_powers_iff z b).mp hz with ⟨n, rfl⟩
    refine ⟨a ^ n * b ^ m, ?_⟩
    rw [hx]
    refine ⟨m + n, ?_⟩
    simp [pow_add, mul_pow, mul_assoc, mul_left_comm]

/-- Helper for Chap10 Lemma 10 118 5: the symmetric supremum presentation of direct localization
away from a product. -/
private instance mkLinearMapIsLocalizedModuleSupAwayMulComm
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  -- Swap the two generators in the supremum and commute the product.
  simpa [sup_comm, mul_comm] using
    (mkLinearMapIsLocalizedModuleSupAwayMul (A := A) (N := N) a b :
      IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N))

/-- Helper for Chap10 Lemma 10 118 5: reindex direct away localizations along an equality of
denominators. -/
private noncomputable abbrev awayEqLinearEquiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {a b : A} (h : a = b) :
    LocalizedModule.Away a N ≃ₗ[A] LocalizedModule.Away b N :=
  h.rec (LinearEquiv.refl A (LocalizedModule.Away a N))

/-- Helper for Chap10 Lemma 10 118 5: localizing first away from `a` and then away from `b` agrees
with direct localization away from `ab`. -/
private noncomputable abbrev awayMulLinearEquiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    LocalizedModule.Away b (LocalizedModule.Away a N) ≃ₗ[A]
      LocalizedModule.Away (a * b) N :=
  IsLocalizedModule.linearEquiv (Submonoid.powers b ⊔ Submonoid.powers a)
    (iteratedLocalizedModuleMkLinearMap (A := A) (N := N)
      (Submonoid.powers b) (Submonoid.powers a))
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of the target algebra transports from the
direct product localization to the iterated product localization. -/
private lemma iteratedAwayAlgebraFinitePresentationOfProduct
    (f g : R) (hfg : LocalizationCondition R S M (f * g)) :
    Algebra.FinitePresentation (Localization.Away (algebraMap R (Localization.Away f) g))
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the first localized target.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of `f * g`.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : Rfg ≃+* At :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) Rfg At).toRingEquiv
  let eS : Sfg ≃+* Bt :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt).toRingEquiv
  have hcompat : ∀ a : Rfg, eS (algebraMap Rfg Sfg a) = algebraMap At Bt (eR a) := by
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := Rfg) (Sₙ := Sfg) (Rₘ' := At) (Sₙ' := Bt) a
  letI : Algebra.FinitePresentation Rfg Sfg := hfg.finitePresentation_algebra
  exact algebraFinitePresentationOfRingEquiv eR eS hcompat

/-- Helper for Chap10 Lemma 10 118 5: freeness of the target algebra transports from the direct
product localization to the iterated product localization. -/
private lemma iteratedAwayAlgebraFreeOfProduct
    (f g : R) (hfg : LocalizationCondition R S M (f * g)) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the first localized target.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of `f * g`.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : Rfg ≃+* At :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) Rfg At).toRingEquiv
  let eS : Sfg ≃+* Bt :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt).toRingEquiv
  have hcompat : ∀ a : Rfg, eS (algebraMap Rfg Sfg a) = algebraMap At Bt (eR a) := by
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := Rfg) (Sₙ := Sfg) (Rₘ' := At) (Sₙ' := Bt) a
  exact moduleFreeOfCompatibleRingEquiv eR eS hcompat hfg.free_algebra

/-- Helper for Chap10 Lemma 10 118 5: finite presentation of the localized module transports from
the direct product localization to the iterated product localization. -/
private lemma iteratedAwayModuleFinitePresentationOfProduct
    (f g : R) (hfg : LocalizationCondition R S M (f * g)) :
    Module.FinitePresentation
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g)))
      (LocalizedModule.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))
        (LocalizedModule.Away (algebraMap R S f) M)) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let Bt := Localization.Away c
  let Nt := LocalizedModule.Away c N
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let Mfg := LocalizedModule.Away (algebraMap R S (f * g)) M
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the first localized target.
    dsimp [c, t, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eS : Sfg ≃+* Bt :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt).toRingEquiv
  have hScompat : ∀ s : S, eS (algebraMap S Sfg s) = algebraMap S Bt s := by
    -- The target equivalence fixes original `S`-numerators.
    intro s
    dsimp [eS]
    exact AlgEquiv.commutes
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt) s
  letI : IsScalarTower S B N := inferInstance
  letI : IsScalarTower S B Nt := inferInstance
  let locB : N →ₗ[B] Nt := LocalizedModule.mkLinearMap (Submonoid.powers c) N
  have hlocB :
      IsLocalizedModule (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := by
    -- Rewrite the canonical `B`-denominator `c` to the image of `g` from `S`.
    simpa [hc] using
      (inferInstance :
        IsLocalizedModule (Submonoid.powers c)
          (LocalizedModule.mkLinearMap (Submonoid.powers c) N))
  let locS : N →ₗ[S] Nt := locB.restrictScalars S
  have hlocS : IsLocalizedModule (Submonoid.powers (algebraMap R S g)) locS := by
    -- Restrict the `B`-localized-module map to `S`.
    letI : IsLocalizedModule
        (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := hlocB
    exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := S) (B := B)
      (N := N) (N' := Nt) (algebraMap R S g) locB
  let directG : N →ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S g)) N
  let eIter : Nt ≃ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S g)) locS directG
  let eMul :
      LocalizedModule.Away (algebraMap R S g) N ≃ₗ[S]
        LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M :=
    awayMulLinearEquiv (A := S) (N := M) (algebraMap R S f) (algebraMap R S g)
  let eEq :
      LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M ≃ₗ[S] Mfg :=
    awayEqLinearEquiv (A := S) (N := M) (map_mul (algebraMap R S) f g).symm
  let eM : Mfg ≃ₗ[S] Nt := (eIter.trans (eMul.trans eEq)).symm
  let moduleBtMfg : Module Bt Mfg := Module.compHom Mfg (eS.symm : Bt →+* Sfg)
  letI : Module Bt Mfg := moduleBtMfg
  letI : SMul Bt Mfg := moduleBtMfg.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Bt Mfg Mfg := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Bt Mfg := Module.toDistribMulAction
  letI : MulAction Bt Mfg := DistribMulAction.toMulAction
  letI : IsScalarTower S Bt Mfg := by
    -- The pulled-back `Bt`-action restricts to the original `S`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro s n
    have hsymm : eS.symm (algebraMap S Bt s) = algebraMap S Sfg s := by
      apply eS.injective
      rw [eS.apply_symm_apply, hScompat s]
    calc
      algebraMap S Bt s • n = eS.symm (algebraMap S Bt s) • n := rfl
      _ = algebraMap S Sfg s • n := by rw [hsymm]
      _ = s • n := IsScalarTower.algebraMap_smul Sfg s n
  have hfpMfg : Module.FinitePresentation Bt Mfg := by
    exact moduleFinitePresentationCompHomOfRingEquiv
      (A := Bt) (B := Sfg) (N := Mfg) eS.symm
  exact moduleFinitePresentationOfExtendedLocalizedEquiv
    (A := S) (Aₛ := Bt) (N := Mfg) (N' := Nt)
    (Submonoid.powers (algebraMap R S (f * g))) eM hfpMfg

/-- Helper for Chap10 Lemma 10 118 5: freeness of the localized module transports from the direct
product localization to the iterated product localization. -/
private lemma iteratedAwayModuleFreeOfProduct
    (f g : R) (hfg : LocalizationCondition R S M (f * g)) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (LocalizedModule.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))
        (LocalizedModule.Away (algebraMap R S f) M)) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Nt := LocalizedModule.Away c N
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let Mfg := LocalizedModule.Away (algebraMap R S (f * g)) M
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the first localized target.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : Rfg ≃+* At :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) Rfg At).toRingEquiv
  let eS : Sfg ≃+* Bt :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt).toRingEquiv
  have hcompat : ∀ a : Rfg, eS (algebraMap Rfg Sfg a) = algebraMap At Bt (eR a) := by
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := Rfg) (Sₙ := Sfg) (Rₘ' := At) (Sₙ' := Bt) a
  have hScompat : ∀ s : S, eS (algebraMap S Sfg s) = algebraMap S Bt s := by
    -- The target equivalence fixes original `S`-numerators.
    intro s
    dsimp [eS]
    exact AlgEquiv.commutes
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Sfg Bt) s
  letI : IsScalarTower S B N := inferInstance
  letI : IsScalarTower S B Nt := inferInstance
  let locB : N →ₗ[B] Nt := LocalizedModule.mkLinearMap (Submonoid.powers c) N
  have hlocB :
      IsLocalizedModule (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := by
    -- Rewrite the canonical `B`-denominator `c` to the image of `g` from `S`.
    simpa [hc] using
      (inferInstance :
        IsLocalizedModule (Submonoid.powers c)
          (LocalizedModule.mkLinearMap (Submonoid.powers c) N))
  let locS : N →ₗ[S] Nt := locB.restrictScalars S
  have hlocS : IsLocalizedModule (Submonoid.powers (algebraMap R S g)) locS := by
    -- Restrict the `B`-localized-module map to `S`.
    letI : IsLocalizedModule
        (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := hlocB
    exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := S) (B := B)
      (N := N) (N' := Nt) (algebraMap R S g) locB
  let directG : N →ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S g)) N
  let eIter : Nt ≃ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S g)) locS directG
  let eMul :
      LocalizedModule.Away (algebraMap R S g) N ≃ₗ[S]
        LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M :=
    awayMulLinearEquiv (A := S) (N := M) (algebraMap R S f) (algebraMap R S g)
  let eEq :
      LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M ≃ₗ[S] Mfg :=
    awayEqLinearEquiv (A := S) (N := M) (map_mul (algebraMap R S) f g).symm
  let eM : Mfg ≃ₗ[S] Nt := (eIter.trans (eMul.trans eEq)).symm
  let moduleBtMfg : Module Bt Mfg := Module.compHom Mfg (eS.symm : Bt →+* Sfg)
  letI : Module Bt Mfg := moduleBtMfg
  letI : SMul Bt Mfg := moduleBtMfg.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Bt Mfg Mfg := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Bt Mfg := Module.toDistribMulAction
  letI : MulAction Bt Mfg := DistribMulAction.toMulAction
  letI : IsScalarTower S Bt Mfg := by
    -- The pulled-back `Bt`-action restricts to the original `S`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro s n
    have hsymm : eS.symm (algebraMap S Bt s) = algebraMap S Sfg s := by
      apply eS.injective
      rw [eS.apply_symm_apply, hScompat s]
    calc
      algebraMap S Bt s • n = eS.symm (algebraMap S Bt s) • n := rfl
      _ = algebraMap S Sfg s • n := by rw [hsymm]
      _ = s • n := IsScalarTower.algebraMap_smul Sfg s n
  let moduleRfgMfg : Module Rfg Mfg := Module.compHom Mfg (algebraMap Rfg Sfg)
  letI : Module Rfg Mfg := moduleRfgMfg
  letI : SMul Rfg Mfg := moduleRfgMfg.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Rfg Mfg Mfg := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Rfg Mfg := Module.toDistribMulAction
  letI : MulAction Rfg Mfg := DistribMulAction.toMulAction
  letI : IsScalarTower Rfg Sfg Mfg := by
    -- The direct product module action over `Rfg` is the restriction of the `Sfg`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a n
    rfl
  let moduleAtNt : Module At Nt := Module.compHom Nt (algebraMap At Bt)
  letI : Module At Nt := moduleAtNt
  letI : SMul At Nt := moduleAtNt.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul At Nt Nt := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction At Nt := Module.toDistribMulAction
  letI : MulAction At Nt := DistribMulAction.toMulAction
  letI : IsScalarTower At Bt Nt := by
    -- The pulled-back `At`-action on `Nt` is defined through the algebra map to `Bt`.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a n
    rfl
  have hsource : ∀ (a : Rfg) (n : Mfg), algebraMap At Bt (eR a) • n = a • n := by
    -- Compatible ring equivalences identify source scalars after pulling back the target action.
    simpa using sourceSmulOfCompatibleRingEquivCompHom eR eS hcompat
  exact moduleFreeOfExtendedLocalizedEquiv
    (C := S) (B' := Bt) (A := Rfg) (A' := At) (N := Mfg) (N' := Nt)
    (Submonoid.powers (algebraMap R S (f * g))) eR eM hsource hfg.free_module

/-- Helper for Chap10 Lemma 10 118 5: the direct localization away from `f * g` is equivalent to
first localizing away from `f` and then away from `g / 1`. -/
lemma localizationCondition_product_iff_iteratedAway (f g : R) :
    LocalizationCondition R S M (f * g) ↔
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  constructor
  · intro hfg
    -- Transport each field from the direct product localization to the iterated chart.
    exact
      { finitePresentation_algebra :=
          iteratedAwayAlgebraFinitePresentationOfProduct (R := R) (S := S) (M := M) f g hfg
        finitePresentation_module :=
          iteratedAwayModuleFinitePresentationOfProduct (R := R) (S := S) (M := M) f g hfg
        free_algebra :=
          iteratedAwayAlgebraFreeOfProduct (R := R) (S := S) (M := M) f g hfg
        free_module :=
          iteratedAwayModuleFreeOfProduct (R := R) (S := S) (M := M) f g hfg }
  · intro hfg
    -- The reverse transport is the product comparison already established in Lemma 10.118.4.
    exact CategoryTheory.ShortComplex.ShortExact.localizationCondition_of_map_away_product
      (R := R) (S := S) (M := M) f g hfg

/-- Helper for Chap10 Lemma 10 118 5: associated localization parameters give equivalent
generic-flatness localization conditions for a fixed algebra and module. -/
lemma localizationCondition_associatedParameter_iff
    {A : Type*} {B : Type*} {N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {x y : A} (hxy : Associated x y) :
    LocalizationCondition A B N x ↔ LocalizationCondition A B N y := by
  -- Route correction: the associated-denominator transport is handled field-by-field. The algebra
  -- fields already follow from compatible localization equivalences; the remaining module fields
  -- need the same localized-module equivalence promoted to semilinear form over those rings.
  have transport :
      ∀ {x y : A}, Associated x y →
        LocalizationCondition A B N x → LocalizationCondition A B N y := by
    intro x y hxy h
    let hBxy : Associated (algebraMap A B x) (algebraMap A B y) :=
      Associated.map (algebraMap A B) hxy
    letI : IsLocalization.Away x (Localization.Away y) :=
      IsLocalization.Away.of_associated hxy.symm
    letI : IsLocalization.Away (algebraMap A B x)
        (Localization.Away (algebraMap A B y)) :=
      IsLocalization.Away.of_associated hBxy.symm
    letI : IsLocalizedModule (Submonoid.powers (algebraMap A B x))
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B y)) N) :=
      isLocalizedModulePowersOfAssociated hBxy.symm
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B y)) N)
    letI : IsScalarTower A (Localization.Away x) (Localization.Away (algebraMap A B x)) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        symm
        exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) x).comp_algebraMap a
    letI : IsScalarTower A (Localization.Away y) (Localization.Away (algebraMap A B y)) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        symm
        exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) y).comp_algebraMap a
    let eA : Localization.Away x ≃+* Localization.Away y :=
      (IsLocalization.algEquiv (Submonoid.powers x)
        (Localization.Away x) (Localization.Away y)).toRingEquiv
    let eB : Localization.Away (algebraMap A B x) ≃+*
        Localization.Away (algebraMap A B y) :=
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap A B x))
        (Localization.Away (algebraMap A B x))
        (Localization.Away (algebraMap A B y))).toRingEquiv
    have hring :
        eB.toRingHom.comp
            (algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x))) =
          (algebraMap (Localization.Away y)
            (Localization.Away (algebraMap A B y))).comp eA.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers x)
      ext a
      calc
        eB (algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x))
            (algebraMap A (Localization.Away x) a))
            = eB (algebraMap A (Localization.Away (algebraMap A B x)) a) := by
              rw [IsScalarTower.algebraMap_apply A (Localization.Away x)
                (Localization.Away (algebraMap A B x)) a]
        _ = eB (algebraMap B (Localization.Away (algebraMap A B x))
              (algebraMap A B a)) := by
              rw [IsScalarTower.algebraMap_apply A B
                (Localization.Away (algebraMap A B x)) a]
        _ = algebraMap B (Localization.Away (algebraMap A B y))
              (algebraMap A B a) := by
              simp [eB]
        _ = algebraMap A (Localization.Away (algebraMap A B y)) a := by
              rw [IsScalarTower.algebraMap_apply A B
                (Localization.Away (algebraMap A B y)) a]
        _ = algebraMap (Localization.Away y) (Localization.Away (algebraMap A B y))
              (algebraMap A (Localization.Away y) a) := by
              rw [IsScalarTower.algebraMap_apply A (Localization.Away y)
                (Localization.Away (algebraMap A B y)) a]
        _ = algebraMap (Localization.Away y) (Localization.Away (algebraMap A B y))
              (eA (algebraMap A (Localization.Away x) a)) := by
              congr 1
              simp [eA]
    have hcompat : ∀ a : Localization.Away x,
        eB (algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x)) a) =
          algebraMap (Localization.Away y) (Localization.Away (algebraMap A B y)) (eA a) := by
      intro a
      exact DFunLike.congr_fun hring a
    have hfpAlg : Algebra.FinitePresentation (Localization.Away y)
        (Localization.Away (algebraMap A B y)) := by
      letI : Algebra.FinitePresentation (Localization.Away x)
          (Localization.Away (algebraMap A B x)) := h.finitePresentation_algebra
      exact algebraFinitePresentationOfRingEquiv eA eB hcompat
    letI : RingHomInvPair (eA : Localization.Away x →+* Localization.Away y)
        (eA.symm : Localization.Away y →+* Localization.Away x) :=
      RingHomInvPair.of_ringEquiv eA
    letI : RingHomInvPair (eA.symm : Localization.Away y →+* Localization.Away x)
        (eA : Localization.Away x →+* Localization.Away y) :=
      RingHomInvPair.symm (eA : Localization.Away x →+* Localization.Away y)
        (eA.symm : Localization.Away y →+* Localization.Away x)
    have hmapB : ∀ (r : Localization.Away x) (b : Localization.Away (algebraMap A B x)),
        eB (r • b) = (eA r) • eB b := by
      intro r b
      change
        eB (algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x)) r * b) =
          algebraMap (Localization.Away y) (Localization.Away (algebraMap A B y)) (eA r) *
            eB b
      rw [map_mul, hcompat]
    let eBsemiA : Localization.Away (algebraMap A B x) ≃ₛₗ[
        (eA : Localization.Away x →+* Localization.Away y)]
        Localization.Away (algebraMap A B y) :=
      { toFun := eB
        invFun := eB.symm
        left_inv := eB.left_inv
        right_inv := eB.right_inv
        map_add' := eB.map_add
        map_smul' := hmapB }
    have hfreeAlg : Module.Free (Localization.Away y)
        (Localization.Away (algebraMap A B y)) :=
      Module.Free.of_equiv eBsemiA
    have hfpModule : Module.FinitePresentation (Localization.Away (algebraMap A B y))
        (LocalizedModule.Away (algebraMap A B y) N) := by
      let fy : N →ₗ[B] LocalizedModule.Away (algebraMap A B y) N :=
        LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B y)) N
      letI : Module (Localization.Away (algebraMap A B x))
          (LocalizedModule.Away (algebraMap A B y) N) :=
        (IsLocalizedModule.iso (Submonoid.powers (algebraMap A B x)) fy).symm.toAddEquiv.module
          (Localization.Away (algebraMap A B x))
      letI : IsScalarTower B (Localization.Away (algebraMap A B x))
          (LocalizedModule.Away (algebraMap A B y) N) :=
        (IsLocalizedModule.iso (Submonoid.powers (algebraMap A B x)) fy).symm.isScalarTower
          (Localization.Away (algebraMap A B x))
      let eN : LocalizedModule.Away (algebraMap A B x) N ≃ₗ[
          Localization.Away (algebraMap A B x)]
          LocalizedModule.Away (algebraMap A B y) N :=
        ((IsLocalizedModule.iso (Submonoid.powers (algebraMap A B x)) fy).symm.toAddEquiv.linearEquiv
          (Localization.Away (algebraMap A B x))).symm
      letI : Module.FinitePresentation (Localization.Away (algebraMap A B x))
          (LocalizedModule.Away (algebraMap A B x) N) := h.finitePresentation_module
      letI : Module.FinitePresentation (Localization.Away (algebraMap A B x))
          (LocalizedModule.Away (algebraMap A B y) N) :=
        Module.FinitePresentation.of_equiv eN
      -- Transport finite presentation through the target-ring equivalence, then identify the
      -- transported scalar action with the canonical action by checking it on localized fractions.
      convert (moduleFinitePresentationCompHomOfRingEquiv
        (A := Localization.Away (algebraMap A B y))
        (B := Localization.Away (algebraMap A B x))
        (N := LocalizedModule.Away (algebraMap A B y) N) eB.symm) using 1
      apply Module.ext'
      intro r m
      obtain ⟨⟨b, s⟩, rfl⟩ :=
        IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B x)) r
      obtain ⟨⟨n, t⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective (Submonoid.powers (algebraMap A B x)) fy m
      simp only [Function.uncurry_apply_pair]
      rw [IsLocalizedModule.mk'_smul_mk' (A := Localization.Away (algebraMap A B y)) fy b n s t]
      symm
      change
        (eB.symm (IsLocalization.mk' (Localization.Away (algebraMap A B y)) b s)) •
            IsLocalizedModule.mk' fy n t =
          IsLocalizedModule.mk' fy (b • n) (s * t)
      have heBsymm :
          eB.symm (IsLocalization.mk' (Localization.Away (algebraMap A B y)) b s) =
            IsLocalization.mk' (Localization.Away (algebraMap A B x)) b s := by
        rw [show eB = (IsLocalization.algEquiv (Submonoid.powers (algebraMap A B x))
          (Localization.Away (algebraMap A B x))
          (Localization.Away (algebraMap A B y))).toRingEquiv from rfl]
        exact (IsLocalization.algEquiv_symm_mk' (M := Submonoid.powers (algebraMap A B x))
          (S := Localization.Away (algebraMap A B x))
          (Q := Localization.Away (algebraMap A B y)) b s)
      rw [heBsymm]
      exact IsLocalizedModule.mk'_smul_mk' (A := Localization.Away (algebraMap A B x)) fy b n s t
    have hfreeModule : Module.Free (Localization.Away y)
        (LocalizedModule.Away (algebraMap A B y) N) := by
      -- Compare the two localized modules by the universal property, then promote the
      -- `B`-linear comparison to a semilinear comparison over the associated base localizations.
      let fx : N →ₗ[B] LocalizedModule.Away (algebraMap A B x) N :=
        LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B x)) N
      let fy : N →ₗ[B] LocalizedModule.Away (algebraMap A B y) N :=
        LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B y)) N
      let eN_B : LocalizedModule.Away (algebraMap A B x) N ≃ₗ[B]
          LocalizedModule.Away (algebraMap A B y) N :=
        IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap A B x)) fx fy
      let eNbase : LocalizedModule.Away (algebraMap A B x) N ≃ₛₗ[
          (eA : Localization.Away x →+* Localization.Away y)]
          LocalizedModule.Away (algebraMap A B y) N :=
        { toFun := eN_B
          invFun := eN_B.symm
          left_inv := eN_B.left_inv
          right_inv := eN_B.right_inv
          map_add' := eN_B.map_add
          map_smul' := by
            intro r m
            -- Write both the base scalar and the localized module element as fractions, then
            -- compare the two scalar actions through the compatible ring equivalences.
            obtain ⟨⟨a, s⟩, rfl⟩ :=
              IsLocalization.mk'_surjective (Submonoid.powers x) r
            obtain ⟨⟨n, t⟩, rfl⟩ :=
              IsLocalizedModule.mk'_surjective (Submonoid.powers (algebraMap A B x)) fx m
            have hden :
                Submonoid.powers x ≤
                  (Submonoid.powers (algebraMap A B x)).comap (algebraMap A B) := by
              intro z hz
              rcases (Submonoid.mem_powers_iff z x).mp hz with ⟨k, hk⟩
              refine ⟨k, ?_⟩
              rw [← hk, map_pow]
            let sB : Submonoid.powers (algebraMap A B x) :=
              ⟨algebraMap A B s.1, hden s.2⟩
            have hmapBaseHom :
                algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x)) =
                  IsLocalization.map (Localization.Away (algebraMap A B x))
                    (algebraMap A B) hden := by
              apply IsLocalization.ringHom_ext (Submonoid.powers x)
              ext z
              calc
                ((algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x))).comp
                    (algebraMap A (Localization.Away x))) z =
                    algebraMap A (Localization.Away (algebraMap A B x)) z := by
                      exact (IsScalarTower.algebraMap_apply A (Localization.Away x)
                        (Localization.Away (algebraMap A B x)) z).symm
                _ = ((IsLocalization.map (Localization.Away (algebraMap A B x))
                    (algebraMap A B) hden).comp (algebraMap A (Localization.Away x))) z := by
                      rw [DFunLike.congr_fun (IsLocalization.map_comp hden) z]
                      exact IsScalarTower.algebraMap_apply A B
                        (Localization.Away (algebraMap A B x)) z
            have hmapBase :
                algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x))
                    (IsLocalization.mk' (Localization.Away x) a s) =
                  IsLocalization.mk' (Localization.Away (algebraMap A B x))
                    (algebraMap A B a) sB := by
              rw [hmapBaseHom]
              exact IsLocalization.map_mk'
                (Q := Localization.Away (algebraMap A B x))
                (g := algebraMap A B) (hy := hden) a s
            have hmapTarget :
                eB (IsLocalization.mk' (Localization.Away (algebraMap A B x))
                    (algebraMap A B a) sB) =
                  IsLocalization.mk' (Localization.Away (algebraMap A B y))
                    (algebraMap A B a) sB := by
              simpa [eB] using
                (IsLocalization.algEquiv_mk'
                  (M := Submonoid.powers (algebraMap A B x))
                  (S := Localization.Away (algebraMap A B x))
                  (Q := Localization.Away (algebraMap A B y))
                  (algebraMap A B a) sB)
            have hsource :
                (IsLocalization.mk' (Localization.Away x) a s) •
                    IsLocalizedModule.mk' fx n t =
                  IsLocalizedModule.mk' fx ((algebraMap A B a) • n) (sB * t) := by
              change
                (algebraMap (Localization.Away x) (Localization.Away (algebraMap A B x))
                    (IsLocalization.mk' (Localization.Away x) a s)) •
                    IsLocalizedModule.mk' fx n t =
                  IsLocalizedModule.mk' fx ((algebraMap A B a) • n) (sB * t)
              rw [hmapBase]
              exact IsLocalizedModule.mk'_smul_mk'
                (A := Localization.Away (algebraMap A B x)) fx (algebraMap A B a) n sB t
            have htarget :
                eA (IsLocalization.mk' (Localization.Away x) a s) •
                    IsLocalizedModule.mk' fy n t =
                  IsLocalizedModule.mk' fy ((algebraMap A B a) • n) (sB * t) := by
              change
                (algebraMap (Localization.Away y) (Localization.Away (algebraMap A B y))
                    (eA (IsLocalization.mk' (Localization.Away x) a s))) •
                    IsLocalizedModule.mk' fy n t =
                  IsLocalizedModule.mk' fy ((algebraMap A B a) • n) (sB * t)
              rw [← hcompat (IsLocalization.mk' (Localization.Away x) a s), hmapBase,
                hmapTarget]
              exact IsLocalizedModule.mk'_smul_mk'
                (A := Localization.Away (algebraMap A B y)) fy (algebraMap A B a) n sB t
            have heN_mk (n : N) (t : Submonoid.powers (algebraMap A B x)) :
                eN_B (IsLocalizedModule.mk' fx n t) = IsLocalizedModule.mk' fy n t := by
              apply IsLocalizedModule.smul_injective fy t
              calc
                t • eN_B (IsLocalizedModule.mk' fx n t)
                    = eN_B (t • IsLocalizedModule.mk' fx n t) := by
                      exact (eN_B.map_smul (t : B) (IsLocalizedModule.mk' fx n t)).symm
                _ = eN_B (fx n) := by rw [IsLocalizedModule.mk'_cancel']
                _ = fy n := by
                      simpa [eN_B] using
                        (IsLocalizedModule.linearEquiv_apply
                          (Submonoid.powers (algebraMap A B x)) fx fy n)
                _ = t • IsLocalizedModule.mk' fy n t := by
                      rw [IsLocalizedModule.mk'_cancel']
            calc
              eN_B ((IsLocalization.mk' (Localization.Away x) a s) •
                  IsLocalizedModule.mk' fx n t)
                  = eN_B (IsLocalizedModule.mk' fx ((algebraMap A B a) • n) (sB * t)) := by
                    rw [hsource]
              _ = IsLocalizedModule.mk' fy ((algebraMap A B a) • n) (sB * t) := by
                    rw [heN_mk]
              _ = eA (IsLocalization.mk' (Localization.Away x) a s) •
                  eN_B (IsLocalizedModule.mk' fx n t) := by
                    rw [heN_mk, htarget] }
      letI : Module.Free (Localization.Away x)
          (LocalizedModule.Away (algebraMap A B x) N) := h.free_module
      exact Module.Free.of_equiv eNbase
    exact
      { finitePresentation_algebra := hfpAlg
        finitePresentation_module := hfpModule
        free_algebra := hfreeAlg
        free_module := hfreeModule }
  constructor
  · exact transport hxy
  · exact transport hxy.symm

/-- Helper for Lemma 10.118.5: a witness for `U(R → S, M)` remains a witness after localizing the
whole setup away from `f`. -/
lemma localizationCondition_map_away (f g : R) (hg : LocalizationCondition R S M g) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  -- Move from the `g`-chart to the product normal form, commute the product, then return to the
  -- desired `f`-chart.
  have hIter :
      LocalizationCondition (Localization.Away g) (Localization.Away (algebraMap R S g))
        (LocalizedModule.Away (algebraMap R S g) M) (algebraMap R (Localization.Away g) f) :=
    localizationConditionSecondAway (R := R) (S := S) (M := M) g f hg
  have hProductGF : LocalizationCondition R S M (g * f) :=
    (localizationCondition_product_iff_iteratedAway (R := R) (S := S) (M := M) g f).mpr hIter
  have hProductFG : LocalizationCondition R S M (f * g) := by
    simpa [mul_comm] using hProductGF
  exact
    (localizationCondition_product_iff_iteratedAway (R := R) (S := S) (M := M) f g).mp
      hProductFG

/-- Helper for Lemma 10.118.5: a witness in the localized pair can be cleared to a witness in the
original pair by multiplying by the numerator returned by `IsLocalization.Away.sec`. -/
lemma localizationCondition_of_localized_witness (f : R) (u : Localization.Away f)
    (hu :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) u) :
    LocalizationCondition R S M (f * (IsLocalization.Away.sec f u).1) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let a : R := (IsLocalization.Away.sec f u).1
  have hassoc : Associated (algebraMap R A a) u :=
    IsLocalization.Away.associated_sec_fst (R := R) (S := A) (x := f) u
  -- Replace the arbitrary localized parameter by its numerator image, then use the product
  -- comparison to descend from the iterated chart to the direct `(f * a)` chart.
  have ha :
      LocalizationCondition A B N (algebraMap R A a) :=
    (localizationCondition_associatedParameter_iff (A := A) (B := B) (N := N) hassoc).mpr hu
  have hProduct : LocalizationCondition R S M (f * a) :=
    (localizationCondition_product_iff_iteratedAway (R := R) (S := S) (M := M) f a).mpr ha
  simpa [a] using hProduct

/-- Chap10 Lemma 10 118 5: pulling back `U(R → S, M)` along `Spec(R_f) → Spec(R)` gives the
good locus of the localized pair `(R_f → S_f, M_f)`. Equivalently, under the identification
`Spec(R_f) ≃ D(f)`, this is the equality `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)`. -/
-- Proof sketch: membership in the localized good locus means there is `g ∈ R_f` such that
-- `(10.118.3.1)` holds after localizing once more at `g`. Write `g = a / f^n`, replace it by an
-- element of `R` giving the same doubly localized rings and modules, and use that the image of
-- `Spec(R_f) → Spec(R)` is `D(f)`.
@[stacks 051X]
theorem goodLocus_localizationAway_eq_preimage (f : R) :
    goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) =
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ⁻¹'
      goodLocus R S M := by
  ext p
  -- Rewrite both sides as existence of a single witness avoiding the relevant prime.
  rw [mem_goodLocus_iff, Set.mem_preimage, mem_goodLocus_iff]
  constructor
  · rintro ⟨u, hucond, hu⟩
    let a : R := (IsLocalization.Away.sec f u).1
    refine ⟨f * a, localizationCondition_of_localized_witness (R := R) (S := S) (M := M) f u hucond, ?_⟩
    -- Clearing the denominator multiplies by `f`, and `f` is already invertible in `R_f`.
    intro hfa_mem
    have hf_not_mem : algebraMap R (Localization.Away f) f ∉ p.asIdeal := by
      intro hf_mem
      exact p.2.ne_top <| Ideal.eq_top_of_isUnit_mem _ hf_mem
        (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f))
    have ha_mem : algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
      have hprod_mem : algebraMap R (Localization.Away f) (f * a) ∈ p.asIdeal := by
        simpa using hfa_mem
      have hmul_mem :
          algebraMap R (Localization.Away f) f * algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
        simpa [map_mul] using hprod_mem
      exact (p.2.mem_or_mem hmul_mem).resolve_left hf_not_mem
    have hu_mem : u ∈ p.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst (R := R) (S := Localization.Away f) (x := f) u)).mp ha_mem
    exact hu hu_mem
  · rintro ⟨g, hgcond, hg⟩
    refine ⟨algebraMap R (Localization.Away f) g,
      localizationCondition_map_away (R := R) (S := S) (M := M) f g hgcond, ?_⟩
    simpa using hg

/-- Under the canonical homeomorphism `Spec(R_f) ≃ D(f)`, the localized good locus is the
restriction of `U(R → S, M)` to the basic open `D(f)`. -/
-- Proof sketch: rewrite `goodLocus_localizationAway_eq_preimage` through
-- `primeSpectrum_localizationAway_homeomorph_D f`, using the explicit description of that
-- homeomorphism on points. Express the restriction to `D(f)` as the preimage of `goodLocus R S M`
-- under the subtype coercion `D(f) → Spec(R)`.
theorem goodLocus_localizationAway_eq_D_restrict (f : R) :
    Set.image (primeSpectrum_localizationAway_homeomorph_D f)
      (goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M)) =
    ((↑) : D(f) → PrimeSpectrum R) ⁻¹' goodLocus R S M := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    -- Transport membership across theorem 1, then read the homeomorphism pointwise.
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using hp'
  · intro hx
    let p : PrimeSpectrum (Localization.Away f) := (primeSpectrum_localizationAway_homeomorph_D f).symm x
    -- Pull the point back along the homeomorphism and apply theorem 1 in the reverse direction.
    have hp_eq : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p = x.1 := by
      change (primeSpectrum_localizationAway_homeomorph_D f p).1 = x.1
      simpa [p] using congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x)
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [hp_eq] using hx
    have hp : p ∈ goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp'
    refine ⟨p, hp, ?_⟩
    simpa [p] using (primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x

end GenericFlatness

end
