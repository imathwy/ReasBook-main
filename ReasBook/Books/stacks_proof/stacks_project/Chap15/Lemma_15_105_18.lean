import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Lemma_10_75_8
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap10.Lemma_10_50_15
import StacksProject_2024.Chap15.Definition_15_105_3
import StacksProject_2024.Chap15.Lemma_15_22_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling:
- primary domain: commutative algebra of weak dimension, flatness criteria for ideals and
  submodules, and the valuation-ring criterion on prime localizations;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `Module.Flat`,
  `ValuationRing`,
  `ValuationRing.iff_local_bezout_domain`;
- best owner abstraction: clause `(1)` should use the chapter owner `HasWeakDimensionLE A 1`,
  clauses `(2)` through `(4)` should stay as the source-facing flatness conditions on ideals and
  `A`-modules, with clause `(4)` quantified over the canonical owner `ModuleCat A`; clause `(5)`
  should use the canonical mathlib owner `ValuationRing` directly rather than a one-off local
  wrapper;
- primitive vs. derived:
  primitive data is only the ring `A` together with the owner predicates on ideals, submodules,
  and prime localizations;
  derived API is the TFAE bridge among these five formulations, so no extra public packaging is
  warranted here.

Source/core/bridge triage:
- `source-facing`: the five-way equivalence matching the Stacks lemma;
- `core/canonical`: `HasWeakDimensionLE`, `Module.Flat`, `PrimeSpectrum`, `Localization.AtPrime`,
  and `ValuationRing`;
- `bridge/view`: the theorem itself, whose last clause presents the Stacks “`A_p` is a valuation
  ring” wording via the minimal existential witness needed to supply the domain instance required
  by the canonical owner `ValuationRing`.
-/

-- Proof sketch: `(1) → (2)` uses the short exact sequence `0 → I → A → A ⧸ I → 0` and the
-- characterization of weak dimension `≤ 1` by vanishing of higher tors. `(2) ↔ (3)` is the
-- filtered-colimit argument reducing arbitrary ideals to finitely generated ones. `(2) → (4)`
-- writes a flat module as a filtered colimit of finite free modules and filters submodules by
-- ideals. `(4) → (1)` resolves an arbitrary module by a free module with flat kernel. `(1) → (5)`
-- localizes weak dimension `≤ 1` and uses the local criterion that finitely generated flat ideals
-- in a local ring are principal, giving a valuation ring on each canonical prime localization.
-- `(5) → (3)` checks finitely generated ideals after localizing at primes and applies the local
-- criterion for flatness.
/-- Helper for Lemma 15.105.18: if every prime localization of `A` is a valuation ring, then every
submodule of a flat `A`-module is flat. -/
theorem submodule_flat_of_localizations_valuationRing
    (hvaluation :
      ∀ p : PrimeSpectrum A,
        ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
          ValuationRing (Localization.AtPrime p.asIdeal))
    (M : ModuleCat.{v} A) [Module.Flat A M] (N : Submodule A M) :
    Module.Flat A N := by
  -- Flatness is local on prime spectra, so it suffices to work over each valuation-ring
  -- localization and use the torsion-free criterion there.
  refine (flat_iff_flat_localizedModule_atPrime (R := A) (M := N)).2 ?_
  intro p
  rcases hvaluation p with ⟨hdom, hval⟩
  letI : IsDomain (Localization.AtPrime p.asIdeal) := hdom
  letI : ValuationRing (Localization.AtPrime p.asIdeal) := hval
  have hMlocal :
      Module.Flat (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) :=
    (flat_iff_flat_localizedModule_atPrime (R := A) (M := M)).1 inferInstance p
  let ι :
      LocalizedModule.AtPrime p.asIdeal N →ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal M :=
    LocalizedModule.map p.asIdeal.primeCompl N.subtype
  have hι_injective : Function.Injective ι := by
    exact LocalizedModule.map_injective p.asIdeal.primeCompl N.subtype N.subtype_injective
  have hMtorsionFree :
      Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := by
    -- Flat modules over a valuation ring are torsion-free.
    exact
      (flat_iff_isTorsionFree_of_valuationRing
        (A := Localization.AtPrime p.asIdeal)
        (M := LocalizedModule.AtPrime p.asIdeal M)).1 hMlocal
  letI :
      Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := hMtorsionFree
  have hNtorsionFree :
      Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal N) :=
    -- Localizing the inclusion `N ↪ M` embeds the localized submodule into a torsion-free module.
    hι_injective.moduleIsTorsionFree ι (fun r x ↦ by simpa using ι.map_smul r x)
  -- Over a valuation ring, torsion-free and flat are equivalent.
  exact
    (flat_iff_isTorsionFree_of_valuationRing
      (A := Localization.AtPrime p.asIdeal)
      (M := LocalizedModule.AtPrime p.asIdeal N)).2 hNtorsionFree

/-- Helper for Lemma 15.105.18: if every prime localization is a valuation ring, then every ideal
of `A` is flat. -/
theorem ideal_flat_of_localizations_valuationRing
    (hvaluation :
      ∀ p : PrimeSpectrum A,
        ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
          ValuationRing (Localization.AtPrime p.asIdeal)) :
    ∀ I : Ideal A, Module.Flat A I := by
  intro I
  -- Flatness is local, so it suffices to prove flatness after localizing the ideal at each prime.
  refine (flat_iff_flat_localizedModule_atPrime (R := A) (M := I)).2 ?_
  intro p
  rcases hvaluation p with ⟨hdom, hval⟩
  letI : IsDomain (Localization.AtPrime p.asIdeal) := hdom
  letI : ValuationRing (Localization.AtPrime p.asIdeal) := hval
  have hAlocalFlat :
      Module.Flat (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal A) := by
    -- The ring is flat over itself, hence so is its prime localization as a localized module.
    exact (flat_iff_flat_localizedModule_atPrime (R := A) (M := A)).1 inferInstance p
  have hAlocalTorsionFree :
      Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal A) := by
    -- Over a valuation ring, flat modules are torsion-free.
    exact
      (flat_iff_isTorsionFree_of_valuationRing
        (A := Localization.AtPrime p.asIdeal)
        (M := LocalizedModule.AtPrime p.asIdeal A)).1 hAlocalFlat
  let ι :
      LocalizedModule.AtPrime p.asIdeal I →ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal A :=
    LocalizedModule.map p.asIdeal.primeCompl I.subtype
  have hι_injective : Function.Injective ι := by
    exact LocalizedModule.map_injective p.asIdeal.primeCompl I.subtype I.injective_subtype
  have hIlocalTorsionFree :
      Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal I) :=
    -- The localized ideal injects into the localized ring, so it stays torsion-free.
    hι_injective.moduleIsTorsionFree ι (fun r x ↦ by simpa using ι.map_smul r x)
  -- Over each valuation-ring localization, torsion-free is equivalent to flat.
  exact
    (flat_iff_isTorsionFree_of_valuationRing
      (A := Localization.AtPrime p.asIdeal)
      (M := LocalizedModule.AtPrime p.asIdeal I)).2 hIlocalTorsionFree

/-- Helper for Lemma 15.105.18: if every submodule of a flat `A`-module is flat in
`ModuleCat.{u} A`, then `A` has weak dimension at most `1`. -/
theorem hasWeakDimensionLEOne_of_submoduleFlat
    (hsub :
      ∀ (M : ModuleCat.{u} A) [Module.Flat A M] (N : Submodule A M),
        Module.Flat A N) :
    HasWeakDimensionLE A 1 := by
  refine ⟨?_⟩
  intro M
  let q : Projective.over M ⟶ M := Projective.π M
  let F : Fin 2 → ModuleCat A := fun i ↦ Fin.cases (Projective.over M) (fun _ ↦ kernel q) i
  let δ : (i : Fin 1) → F i.succ ⟶ F i.castSucc :=
    fun i ↦ Fin.cases (kernel.ι q) (fun j ↦ Fin.elim0 j) i
  have hProjectiveFlat : Module.Flat A ↑(Projective.over M) := by
    -- The chosen cover object is projective, hence flat.
    exact Module.Flat.of_projective
  have hKernelKerFlat : Module.Flat A (LinearMap.ker q.hom) := by
    -- Apply clause `(4)` to the kernel submodule inside the flat projective cover.
    letI : Module.Flat A ↑(Projective.over M) := hProjectiveFlat
    exact hsub (Projective.over M) (LinearMap.ker q.hom)
  have hKernelFlat : Module.Flat A ↑(kernel q) := by
    -- Transport the flatness of the concrete kernel submodule back to the categorical kernel.
    letI : Module.Flat A (ModuleCat.of A (LinearMap.ker q.hom)) := hKernelKerFlat
    exact Module.Flat.of_linearEquiv (ModuleCat.kernelIsoKer q).toLinearEquiv
  have hq_surj : Function.Surjective q.hom := by
    -- The canonical projective cover map is an epimorphism in `ModuleCat`.
    exact (ModuleCat.epi_iff_surjective q).1 inferInstance
  have hq_exact : Function.Exact (kernel.ι q).hom q.hom := by
    -- The kernel row `0 → ker q → Projective.over M → M` is exact.
    let S : ShortComplex (ModuleCat A) := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hSExact : S.Exact := by
      simpa [S] using ShortComplex.exact_kernel q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hSExact
  have hδ_injective : Function.Injective (kernel.ι q).hom := by
    -- Kernels are monomorphisms in `ModuleCat`.
    exact (ModuleCat.mono_iff_injective (kernel.ι q)).1 inferInstance
  have hresolution : ModuleCat.HasFiniteFlatResolutionLengthLE M 1 := by
    -- Package the projective cover and its flat kernel as a two-term flat resolution.
    refine ⟨F, ?_, δ, q, hq_surj, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa [F] using hProjectiveFlat
      · intro j
        simpa [F] using hKernelFlat
    · simpa [δ] using hq_exact
    · intro i
      exact Fin.elim0 i
    · simpa [δ] using hδ_injective
  -- Convert the explicit flat resolution into the weak-dimension owner.
  exact ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE (M := M) hresolution

/-- Helper for Lemma 15.105.18: under weak dimension `≤ 1`, the source dimension-shift argument
kills `Tor₁^A(I, A ⧸ J)` for every pair of ideals `I, J`. -/
lemma tor_one_ideal_quotient_isZero_of_hasWeakDimensionLE_one
    [HasWeakDimensionLE A 1] (I J : Ideal A) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A I)).obj
      (ModuleCat.of A (A ⧸ J)))) := by
  -- Route correction: the source proof needs the missing `Tor₂(A / I, A / J) → Tor₁(I, A / J)`
  -- dimension shift, so this theorem isolates that exact long-exact-sequence step.
  -- TODO: use the short exact sequence `0 → I → A → A / I → 0`, identify `Tor₁(I, A / J)` with
  -- the image of `Tor₂(A / I, A / J)`, and kill the latter by weak dimension `≤ 1`.
  sorry

/-- Helper for Lemma 15.105.18: quotient-side `Tor₁`-vanishing forces flatness by the Chapter 10
flatness `TFAE`. -/
lemma flat_of_tor_one_quotient_vanishing_local
    (C : ModuleCat A)
    (hTor : ∀ J : Ideal A,
      IsZero ((((Tor (ModuleCat A) 1).obj C).obj (ModuleCat.of A (A ⧸ J))))) :
    Module.Flat A (C : Type u) := by
  -- Repackage the quotient-side `Tor₁` vanishing into the exact fourth clause of the owner `TFAE`.
  have hTFAE :
      List.TFAE
        [ Module.Flat A (C : Type u)
        , ∀ i : ℕ, 0 < i → ∀ N : ModuleCat A,
            IsZero ((((Tor (ModuleCat A) i).obj C).obj N))
        , ∀ N : ModuleCat A, IsZero ((((Tor (ModuleCat A) 1).obj C).obj N))
        , ∀ J : Ideal A,
            IsZero ((((Tor (ModuleCat A) 1).obj C).obj (ModuleCat.of A (A ⧸ J))))
        , ∀ J : Ideal A, J.FG →
            IsZero ((((Tor (ModuleCat A) 1).obj C).obj (ModuleCat.of A (A ⧸ J)))) ] := by
    simpa using flat_tfae_tor_vanishing_criteria (R := A) (M := (C : Type u))
  -- The fourth leg of the `TFAE` is exactly the needed flatness criterion.
  exact (hTFAE.out 0 3).2 hTor

/-- Helper for Lemma 15.105.18: weak dimension `≤ 1` forces every ideal of `A` to be flat. -/
lemma ideal_flat_of_hasWeakDimensionLEOne
    [HasWeakDimensionLE A 1] (I : Ideal A) :
    Module.Flat A I := by
  -- Once the source dimension-shift kills `Tor₁(I, A / J)` for every quotient, the quotient-side
  -- flatness criterion from Lemma `15.67.2` finishes immediately.
  exact
    flat_of_tor_one_quotient_vanishing_local (A := A) (C := ModuleCat.of A I)
      (fun J ↦ tor_one_ideal_quotient_isZero_of_hasWeakDimensionLE_one (A := A) I J)

/-- Helper for Lemma 15.105.18: if every finitely generated ideal of `A` is flat, then every
ideal of `A` is flat via the filtered-colimit presentation by finitely generated subideals. -/
lemma ideal_flat_of_fg_flat_via_filtered_colimit
    (hfg : ∀ I : Ideal A, I.FG → Module.Flat A I) :
    ∀ I : Ideal A, Module.Flat A I := by
  intro I
  -- Route correction: stay on the source route by indexing `I` with its finitely generated
  -- subideals, instead of switching to an unrelated recursive flatness argument.
  -- TODO: build the filtered diagram of finitely generated subideals of `I`, identify `I` as its
  -- colimit cocone point, and apply `flat_of_isColimit_filtered_system`.
  let _ := hfg
  let _ := I
  sorry

/-- Helper for Lemma 15.105.18: in a nontrivial local ring, a nonzero element whose principal
ideal is flat acts injectively on the ring. -/
lemma isRegular_of_nonzero_of_principalIdeal_flat_of_isLocalRing
    [IsLocalRing A] [Nontrivial A]
    (hfg : ∀ I : Ideal A, I.FG → Module.Flat A I)
    {a : A} (ha : a ≠ 0) :
    IsSMulRegular A a := by
  let I : Ideal A := Ideal.span ({a} : Set A)
  have hIfg : I.FG := by
    -- The principal ideal `(a)` is finitely generated by its defining singleton.
    simpa [I] using
      (Submodule.fg_span_singleton a : (Ideal.span ({a} : Set A)).FG)
  have hIflat : Module.Flat A I := hfg I hIfg
  letI : Module.Flat A I := hIflat
  letI : Module.Finite A I := Module.Finite.of_fg hIfg
  letI : Module.Free A I := Module.free_of_flat_of_isLocalRing
  let μ : A →ₗ[A] I :=
    LinearMap.codRestrict I (LinearMap.toSpanSingleton A A a) (fun r ↦ by
      -- Multiples of `a` lie in the principal ideal by construction.
      change r * a ∈ Ideal.span ({a} : Set A)
      exact Ideal.mem_span_singleton.2 ⟨r, by simp [mul_comm]⟩)
  have hμ_surj : Function.Surjective μ := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp y.2
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change r * a = y.1
    simpa [μ, LinearMap.toSpanSingleton_apply, mul_comm] using hr.symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    μ (LinearMap.id : I →ₗ[A] I) hμ_surj
  let z : I := ⟨a, Ideal.subset_span (by simp : a ∈ ({a} : Set A))⟩
  let u : A := s z
  have hu_spec : u * a = a := by
    -- Evaluating the splitting on the distinguished generator recovers `a`.
    have hs_z : (μ.comp s) z = z := by
      simpa [hs]
    simpa [u, z, μ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using
      congrArg Subtype.val hs_z
  have hu_not_mem_maximal :
      u ∉ IsLocalRing.maximalIdeal A := by
    intro hu_mem
    have ha_mem_mul : a ∈ IsLocalRing.maximalIdeal A * I := by
      rw [← hu_spec]
      exact Ideal.mul_mem_mul hu_mem z.2
    have hle : I ≤ IsLocalRing.maximalIdeal A * I := by
      simpa [I] using
        (Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A * I)).2 ha_mem_mul
    have hIeq : I = ⊥ := by
      exact
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal A) I hIfg hle
          (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
    have hIne : I ≠ ⊥ := by
      simpa [I, Ideal.span_singleton_eq_bot] using ha
    exact hIne hIeq
  have hu_unit : IsUnit u := IsLocalRing.notMem_maximalIdeal.mp hu_not_mem_maximal
  have hs_surj : Function.Surjective s := by
    rcases hu_unit with ⟨u', hu'⟩
    intro x
    refine ⟨(x * ↑u'⁻¹) • z, ?_⟩
    calc
      s ((x * ↑u'⁻¹) • z) = (x * ↑u'⁻¹) * u := by simp [u, mul_assoc]
      _ = x := by
        rw [← hu']
        simp [mul_assoc]
  -- Route correction: instead of comparing free ranks abstractly, use the projective splitting
  -- and the unit coefficient above to force the section to be surjective, hence `μ` injective.
  intro x y hxy
  apply sub_eq_zero.mp
  rcases hs_surj (x - y) with ⟨w, hw⟩
  have hxy' : x * a = y * a := by
    simpa [smul_eq_mul, mul_comm] using hxy
  have hμ_zero : μ (s w) = 0 := by
    apply Subtype.ext
    change (s w) * a = 0
    rw [hw, sub_mul]
    simpa using sub_eq_zero.mpr hxy'
  have hw_zero : w = 0 := by
    have hw_eq : (μ.comp s) w = 0 := by
      simpa [LinearMap.comp_apply] using hμ_zero
    rw [hs] at hw_eq
    simpa using hw_eq
  rw [← hw]
  simp [hw_zero]

/-- Helper for Lemma 15.105.18: a nontrivial local ring whose finitely generated ideals are flat
is a domain. -/
lemma isDomain_of_isLocalRing_of_fgIdealFlat
    [IsLocalRing A] [Nontrivial A]
    (hfg : ∀ I : Ideal A, I.FG → Module.Flat A I) :
    IsDomain A := by
  refine (isDomain_iff_noZeroDivisors_and_nontrivial A).2 ?_
  refine ⟨?_, inferInstance⟩
  exact
    { eq_zero_or_eq_zero_of_mul_eq_zero := by
        intro a b hab
        by_cases ha : a = 0
        · exact Or.inl ha
        · right
          have hreg : IsSMulRegular A a := by
            simpa using
              isRegular_of_nonzero_of_principalIdeal_flat_of_isLocalRing (A := A) hfg ha
          exact hreg (by simpa [smul_eq_mul, hab]) }

/-- Helper for Lemma 15.105.18: a finite free ideal in a domain has rank at most one, so it is
generated by at most one basis vector and hence is principal. -/
lemma finite_free_ideal_isPrincipal_of_isDomain
    [IsDomain A] (I : Ideal A) [Module.Finite A I] [Module.Free A I] :
    I.IsPrincipal := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex A I) A I := Module.Free.chooseBasis A I
  letI : Finite (Module.Free.ChooseBasisIndex A I) := Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex A I) := Fintype.ofFinite _
  have hcard_le :
      Fintype.card (Module.Free.ChooseBasisIndex A I) ≤ 1 := by
    -- Compare the finite rank of the ideal with the finite rank of the ambient rank-one module `A`.
    have hfinrank_le : Module.finrank A I ≤ 1 := by
      simpa [Module.finrank_self A] using (Submodule.finrank_le (R := A) (M := A) I)
    rw [Module.finrank_eq_card_chooseBasisIndex A I] at hfinrank_le
    exact hfinrank_le
  have hsub :
      Subsingleton (Module.Free.ChooseBasisIndex A I) :=
    (Fintype.card_le_one_iff_subsingleton).1 hcard_le
  by_cases hnonempty : Nonempty (Module.Free.ChooseBasisIndex A I)
  · letI : Subsingleton (Module.Free.ChooseBasisIndex A I) := hsub
    let i0 : Module.Free.ChooseBasisIndex A I := Classical.choice hnonempty
    -- In the singleton-basis case, every element of `I` is a scalar multiple of the unique basis
    -- vector, so that vector generates the ideal.
    refine (Submodule.isPrincipal_iff I).2 ?_
    refine ⟨(b i0 : I), ?_⟩
    apply le_antisymm
    · intro x hx
      let xI : I := ⟨x, hx⟩
      have hsingle :
          ∑ j, (b.repr xI) j • b j = (b.repr xI) i0 • b i0 := by
        refine Finset.sum_eq_single i0 ?_ ?_
        · intro j _ hj
          exfalso
          exact hj (Subsingleton.elim _ _)
        · intro hi0
          exfalso
          exact hi0 (Finset.mem_univ i0)
      have hx_eq :
          xI = (b.repr xI) i0 • b i0 := by
        calc
          xI = ∑ j, (b.repr xI) j • b j := by
            symm
            exact b.sum_repr xI
          _ = (b.repr xI) i0 • b i0 := hsingle
      rw [Submodule.mem_span_singleton]
      refine ⟨(b.repr xI) i0, ?_⟩
      simpa [smul_eq_mul] using (congrArg Subtype.val hx_eq).symm
    · refine Submodule.span_le.2 ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using (b i0).2
  · letI : IsEmpty (Module.Free.ChooseBasisIndex A I) := not_nonempty_iff.mp hnonempty
    have hIbot : I = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      change x = 0
      let xI : I := ⟨x, hx⟩
      have hx_zero : xI = 0 := by
        calc
          xI = ∑ j, (b.repr xI) j • b j := by
            symm
            exact b.sum_repr xI
          _ = 0 := by simp
      exact congrArg Subtype.val hx_zero
    simpa [hIbot] using (bot_isPrincipal : (⊥ : Ideal A).IsPrincipal)

/-- Helper for Lemma 15.105.18: in a nontrivial local ring whose finitely generated ideals are
flat, every finitely generated ideal is principal. -/
lemma fgIdeal_isPrincipal_of_isLocalRing_of_fgIdealFlat
    [IsLocalRing A] [Nontrivial A]
    (hfg : ∀ I : Ideal A, I.FG → Module.Flat A I)
    (I : Ideal A) (hI : I.FG) :
    I.IsPrincipal := by
  have hdom : IsDomain A :=
    isDomain_of_isLocalRing_of_fgIdealFlat (A := A) hfg
  letI : IsDomain A := hdom
  have hflat : Module.Flat A I := hfg I hI
  letI : Module.Flat A I := hflat
  letI : Module.Finite A I := Module.Finite.of_fg hI
  letI : Module.Free A I := Module.free_of_flat_of_isLocalRing
  -- The local flatness hypothesis makes `I` finite free, and inside the rank-one module `A` that
  -- forces `I` to have at most one basis vector.
  exact finite_free_ideal_isPrincipal_of_isDomain (A := A) I

/-- Helper for Lemma 15.105.18: a local ring whose finitely generated ideals are flat is a domain
and hence a valuation ring. -/
lemma valuationRing_of_isLocalRing_of_fgIdealFlat
    [IsLocalRing A] [Nontrivial A]
    (hfg : ∀ I : Ideal A, I.FG → Module.Flat A I) :
    ∃ (_ : IsDomain A), ValuationRing A := by
  have hdom : IsDomain A :=
    isDomain_of_isLocalRing_of_fgIdealFlat (A := A) hfg
  letI : IsDomain A := hdom
  have hprincipal : ∀ I : Ideal A, I.FG → I.IsPrincipal := by
    intro I hI
    -- The local flatness hypothesis upgrades every finitely generated ideal to a free rank-`≤ 1`
    -- submodule of `A`, hence to a principal ideal.
    exact fgIdeal_isPrincipal_of_isLocalRing_of_fgIdealFlat (A := A) hfg I hI
  have hvaluation : ValuationRing A := by
    -- Convert the source-facing “all finitely generated ideals are principal” criterion into the
    -- canonical valuation-ring owner.
    exact
      (valuationRing_iff_isLocalRing_and_fgIdeals_principal (A := A)).2
        ⟨inferInstance, hprincipal⟩
  exact ⟨hdom, hvaluation⟩

/-- Helper for Lemma 15.105.18: if every ideal of `A` is flat, then every prime localization of
`A` is a valuation ring. -/
lemma localizations_valuationRing_of_idealFlat
    (hideal : ∀ I : Ideal A, Module.Flat A I) :
    ∀ p : PrimeSpectrum A,
      ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
        ValuationRing (Localization.AtPrime p.asIdeal) := by
  intro p
  -- Route correction: localize clause `(2)` only far enough to recover flatness of finitely
  -- generated ideals of `Aₚ`, then apply the local source argument packaged above.
  -- TODO: show every finitely generated ideal of `Localization.AtPrime p.asIdeal` is the image of
  -- a finitely generated ideal of `A`, transport flatness across
  -- `Module.flat_iff_of_isLocalization`, and invoke
  -- `valuationRing_of_isLocalRing_of_fgIdealFlat` on `Aₚ`.
  let _ := hideal
  sorry

/-- Lemma 15.105.18: for a commutative ring `A`, the following are equivalent: `A` has weak
dimension at most `1`; every ideal of `A` is flat; every finitely generated ideal of `A` is flat;
every submodule of a flat `A`-module is flat; and every localization `Aₚ` at a prime ideal is a
valuation ring. -/
@[stacks 092S]
theorem weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae :
    List.TFAE
      [ HasWeakDimensionLE A 1
      , ∀ I : Ideal A, Module.Flat A I
      , ∀ I : Ideal A, I.FG → Module.Flat A I
      , ∀ (M : ModuleCat.{u} A) [Module.Flat A M] (N : Submodule A M),
          Module.Flat A N
      , ∀ p : PrimeSpectrum A,
          ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            ValuationRing (Localization.AtPrime p.asIdeal)
      ] := by
  tfae_have 1 → 2 := by
    intro hwd
    -- Route correction: the source proof factors through the isolated dimension-shift lemma and
    -- then finishes with the quotient-side flatness criterion.
    let _ : HasWeakDimensionLE A 1 := hwd
    exact ideal_flat_of_hasWeakDimensionLEOne (A := A)
  tfae_have 2 → 3 := by
    intro hideal I _
    -- Every finitely generated ideal is in particular an ideal, so clause `(2)` specializes
    -- directly to clause `(3)`.
    exact hideal I
  tfae_have 3 → 2 := by
    intro hfg
    -- The source proof writes every ideal as the filtered colimit of its finitely generated
    -- subideals and descends flatness from those stages.
    exact ideal_flat_of_fg_flat_via_filtered_colimit (A := A) hfg
  tfae_have 4 → 1 := by
    intro h4
    -- Route correction: clause `(4)` is now aligned with the owner universe `ModuleCat.{u} A`,
    -- so the source-proof projective-cover resolution can be used directly.
    exact hasWeakDimensionLEOne_of_submoduleFlat (A := A) h4
  tfae_have 2 → 5 := by
    intro hideal
    -- The source proof localizes clause `(2)` and then applies the local valuation-ring package.
    exact localizations_valuationRing_of_idealFlat (A := A) hideal
  tfae_have 5 → 3 := by
    intro hvaluation I _
    -- The stronger prime-local argument already yields flatness of every ideal, hence in
    -- particular of every finitely generated ideal.
    exact ideal_flat_of_localizations_valuationRing (A := A) hvaluation I
  tfae_have 5 → 4 := by
    intro hvaluation
    -- This is the prime-local valuation-ring criterion proved above.
    exact submodule_flat_of_localizations_valuationRing (A := A) hvaluation
  tfae_finish

end
