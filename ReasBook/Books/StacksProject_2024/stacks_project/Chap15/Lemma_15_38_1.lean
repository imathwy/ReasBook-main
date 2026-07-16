import StacksProject_2024.stacks_project.Chap10.Definition_10_141_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace RingHom

open IsLocalRing

/-
Domain-style sampling for Lemma 15.38.1:
- primary domain: infinitesimal lifting criteria for formal smoothness of local ring maps in
  maximal-ideal adic topology;
- inspected owner declarations of the same kind:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.FormallySmooth.exists_lift`,
  * `IsLocalRing.of_surjective'`,
  * `RingHom.IsSmallExtension.isLocalRingTarget`;
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner, while the local
  extension-map facts should be expressed through the canonical local-ring derivation owners
  `IsLocalRing.of_surjective'` and `IsSmallExtension.isLocalRingTarget`; in particular, the target
  local structure for a square-zero surjection or small extension is derived internally rather than
  stored as extra theorem-level data. The lift itself is the same derived payload as in
  `RingHom.FormallySmooth.exists_lift`;
- primitive data on the right-hand side: the chosen square-zero surjection or small extension
  `π : A' →+* A`, the local map `g : S →+* A`, the nilpotence of `maximalIdeal A'`, the
  residue-field bijectivity, and the commutative square;
- derived API: the existential lift payload, and the locality of any lift `S →+* A`, which should
  not be primitive public data in this bridge theorem.

Source/core/bridge triage:
- `source-facing`: the local lifting criteria against square-zero and small extensions;
- `core/canonical`: `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the equivalences below, which compare the owner predicate with those lifting
  criteria.
-/

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

private abbrev maximalIdealAdic_liftPayload
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (f : R →+* S) (π : A' →+* A) (g : S →+* A) (g0 : R →+* A') : Prop :=
  ∃ gLift : S →+* A', π.comp gLift = g ∧ gLift.comp f = g0

private theorem maximalIdealAdic_nontrivialTarget_of_squareZero
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsq : RingHom.ker π ^ 2 = ⊥) : Nontrivial A := by
  classical
  by_contra hA
  letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
  have hker : RingHom.ker π = ⊤ := by
    ext x
    simp [RingHom.mem_ker, Subsingleton.elim (π x) 0]
  have h1sq : (1 : A') ∈ RingHom.ker π ^ 2 := by
    rw [pow_two, hker]
    simpa using Ideal.mul_mem_mul (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
      (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
  have h1 : (1 : A') = 0 := by
    have hmem : (1 : A') ∈ (⊥ : Ideal A') := by
      exact hπsq ▸ h1sq
    exact hmem
  let _ : Nontrivial A' := IsLocalRing.toNontrivial
  exact one_ne_zero h1

private abbrev maximalIdealAdic_residueFieldMapBijective
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
  letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
  Function.Bijective (ResidueField.map g)

private theorem maximalIdealAdic_isLocalRingTargetOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [hπ : IsSmallExtension π] : IsLocalRing A := by
  let _ : Nontrivial A := hπ.instNontrivialTarget
  exact IsLocalRing.of_surjective' π hπ.surjective

private abbrev maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := inferInstance
  letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
  Function.Bijective (ResidueField.map g)

/-- Helper for Lemma 15.38.1: a local map into a local ring whose maximal ideal is nilpotent is
continuous from the maximal-ideal adic topology to the discrete topology. -/
private theorem continuous_of_isLocalHom_to_discrete_of_nilpotent_maximalIdeal
    {A : Type w} [CommRing A] [IsLocalRing A]
    (g : S →+* A) [IsLocalHom g] (hA : IsNilpotent (maximalIdeal A)) :
    letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
    letI : TopologicalSpace A := ⊥
    Continuous g := by
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  letI : TopologicalSpace A := Ideal.adicTopology (⊥ : Ideal A)
  have hAdic : IsAdic (⊥ : Ideal A) := rfl
  letI : DiscreteTopology A := (is_bot_adic_iff).mp hAdic
  rcases hA with ⟨n, hn⟩
  have hcont : Continuous g := by
    -- Some power of the source maximal ideal maps to `0`, which is the adic continuity criterion.
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨n, ?_⟩
    calc
      Ideal.map g (maximalIdeal S ^ n) = Ideal.map g (maximalIdeal S) ^ n := by
        rw [Ideal.map_pow]
      _ ≤ maximalIdeal A ^ n := Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le g) n
      _ = ⊥ := hn
  have hbotA : (inferInstance : TopologicalSpace A) = ⊥ := DiscreteTopology.eq_bot
  change @Continuous S A (Ideal.adicTopology (maximalIdeal S)) ⊥ ⇑g
  change @Continuous S A (Ideal.adicTopology (maximalIdeal S))
    (inferInstance : TopologicalSpace A) ⇑g at hcont
  rw [hbotA] at hcont
  exact hcont

/-- Helper for Lemma 15.38.1: a surjective local homomorphism sends a nilpotent maximal ideal to a
nilpotent maximal ideal on the target. -/
private theorem nilpotent_maximalIdeal_of_surjective_of_nilpotent_maximalIdeal
    {A' : Type*} {A : Type*} [CommRing A'] [CommRing A] [IsLocalRing A'] [IsLocalRing A]
    [Nontrivial A] (π : A' →+* A) (hπsurj : Function.Surjective π)
    (hA' : IsNilpotent (maximalIdeal A')) :
    IsNilpotent (maximalIdeal A) := by
  letI : IsLocalHom π := IsLocalHom.of_surjective π hπsurj
  rcases hA' with ⟨n, hn⟩
  have hmap :
      Ideal.map π (maximalIdeal A') = maximalIdeal A := by
    apply le_antisymm
    · exact IsLocalRing.map_maximalIdeal_le π
    · intro y hy
      rcases hπsurj y with ⟨x, rfl⟩
      have hx : x ∈ maximalIdeal A' := by
        rw [IsLocalRing.mem_maximalIdeal]
        rw [IsLocalRing.mem_maximalIdeal] at hy
        exact fun hxUnit ↦ hy (hxUnit.map π)
      exact Ideal.mem_map_of_mem π hx
  refine ⟨n, ?_⟩
  calc
    maximalIdeal A ^ n = Ideal.map π (maximalIdeal A') ^ n := by
      rw [← hmap]
    _ = Ideal.map π (maximalIdeal A' ^ n) := by
      rw [Ideal.map_pow]
    _ = Ideal.map π (⊥ : Ideal A') := by
      simpa [hn]
    _ = ⊥ := by
      simpa using (Ideal.map_bot π)

/-- Helper for Lemma 15.38.1: formal smoothness for the maximal-ideal adic topology solves every
surjective square-zero lifting problem once the target local ring has nilpotent maximal ideal. -/
private theorem liftPayload_of_formally_smooth_for_adic_of_surjective_square_zero
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (f : R →+* S) (hf : f.formally_smooth_for_adic (maximalIdeal S))
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    [IsLocalRing A] [Nontrivial A] (hA' : IsNilpotent (maximalIdeal A'))
    (g : S →+* A) [IsLocalHom g] (g0 : R →+* A')
    (hcomm : π.comp g0 = g.comp f) :
    maximalIdealAdic_liftPayload f π g g0 := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace A' := ⊥
  letI : DiscreteTopology A' := ⟨rfl⟩
  letI : DiscreteTopology (A' ⧸ RingHom.ker π) := by
    refine ⟨?_⟩
    ext s
    rfl
  let e : A' ⧸ RingHom.ker π ≃+* A := RingHom.quotientKerEquivOfSurjective hπsurj
  let gQ : S →+* A' ⧸ RingHom.ker π := e.symm.toRingHom.comp g
  have hA : IsNilpotent (maximalIdeal A) :=
    nilpotent_maximalIdeal_of_surjective_of_nilpotent_maximalIdeal π hπsurj hA'
  have hg : Continuous g :=
    continuous_of_isLocalHom_to_discrete_of_nilpotent_maximalIdeal g hA
  have hgQ : Continuous gQ := by
    -- Transport the continuity of `g` across the quotient-kernel equivalence.
    have he : Continuous e.symm.toRingHom := continuous_of_discreteTopology
    exact he.comp hg
  have hg0 : Continuous g0 := continuous_of_discreteTopology
  have hfTop : f.FormallySmoothTopologically :=
    (RingHom.formally_smooth_for_adic_iff f (maximalIdeal S)).mp hf
  have hqker_symm :
      e.symm.toRingHom.comp π = Ideal.Quotient.mk (RingHom.ker π) := by
    -- The inverse quotient-kernel equivalence is the canonical quotient map.
    ext x
    simpa [e] using e.symm_apply_apply ((Ideal.Quotient.mk (RingHom.ker π)) x)
  have hqker :
      e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker π)) = π := by
    -- The forward quotient-kernel equivalence recovers the original surjection.
    ext x
    rfl
  have hcommQ : (Ideal.Quotient.mk (RingHom.ker π)).comp g0 = gQ.comp f := by
    -- Rewrite the commutative square through the quotient-kernel equivalence.
    calc
      (Ideal.Quotient.mk (RingHom.ker π)).comp g0 = (e.symm.toRingHom.comp π).comp g0 := by
        rw [hqker_symm]
      _ = e.symm.toRingHom.comp (π.comp g0) := by
        rw [RingHom.comp_assoc]
      _ = e.symm.toRingHom.comp (g.comp f) := by
        rw [hcomm]
      _ = gQ.comp f := by
        rfl
  obtain ⟨gLift, -, hgLift, hgLift0⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hfTop (RingHom.ker π) hπsq gQ hgQ g0 hg0
      hcommQ
  refine ⟨gLift, ?_, hgLift0⟩
  -- Push the lifted quotient equality back along the quotient-kernel equivalence.
  calc
    π.comp gLift = (e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker π))).comp gLift := by
      rw [hqker]
    _ = e.toRingHom.comp ((Ideal.Quotient.mk (RingHom.ker π)).comp gLift) := by
      rw [RingHom.comp_assoc]
    _ = e.toRingHom.comp gQ := by
      rw [hgLift]
    _ = g := by
      ext x
      simpa [gQ] using e.apply_symm_apply (g x)

/-- The square-zero local lifting condition appearing in Lemma 15.38.1. The target local-ring
structure is derived canonically from the surjective map `π : A' → A`, so it is not part of the
public data of the condition. -/
abbrev maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (_ : IsNilpotent (maximalIdeal A')) (g : S →+* A),
      let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
      letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijective π hπsurj hπsq g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

/-- The small-extension local lifting condition appearing in the Noetherian refinement of Lemma
15.38.1. The target local-ring structure is derived canonically from the owner predicate
`IsSmallExtension π`, so only the actual extension and residue-field data remain visible. -/
abbrev maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A),
      letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension π g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

/-- Helper for Lemma 15.38.1: a small extension has square-zero kernel, and its source maximal
ideal is nilpotent. -/
private theorem smallExtension_has_squareZero_kernel_and_nilpotent_maximalIdeal
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [hπ : IsSmallExtension π] :
    RingHom.ker π ^ 2 = ⊥ ∧ IsNilpotent (maximalIdeal A') := by
  constructor
  · -- The kernel has length `1`, hence is simple; over a local ring its annihilator is the
    -- maximal ideal, so the maximal ideal kills the kernel and therefore the kernel squares to `0`.
    have hsimple : IsSimpleModule A' (RingHom.ker π) := by
      exact (Module.length_eq_one_iff.mp hπ.ker_length)
    have hannEq : Module.annihilator A' (RingHom.ker π) = maximalIdeal A' := by
      let _ : IsSimpleModule A' (RingHom.ker π) := hsimple
      exact IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
    have hker_le : RingHom.ker π ≤ maximalIdeal A' := by
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hsqle : RingHom.ker π ^ 2 ≤ ⊥ := by
      rw [pow_two]
      calc
        RingHom.ker π * RingHom.ker π ≤ maximalIdeal A' * RingHom.ker π := by
          simpa [Ideal.mul_comm] using (mul_le_mul_left hker_le (RingHom.ker π))
        _ = Module.annihilator A' (RingHom.ker π) * RingHom.ker π := by
          rw [hannEq]
        _ = ⊥ := by
          simpa using (Submodule.annihilator_mul (RingHom.ker π))
    exact le_bot_iff.mp hsqle
  · -- The source of a small extension is Artinian local, so its maximal ideal is nilpotent.
    have hNoeth : IsNoetherian A' A' := by
      exact
        ((IsArtinianRing.tfae A' A').out 2 1).mp
          (show IsArtinian A' A' from inferInstance)
    exact
      (@isArtinianRing_iff_isNilpotent_maximalIdeal A' _
          (show IsNoetherianRing A' from hNoeth) _).mp inferInstance

/-- Helper for Lemma 15.38.1: positive powers of the maximal ideal of a local ring remain proper.
-/
private theorem maximalIdeal_pow_ne_top (n : ℕ) (hn : n ≠ 0) :
    maximalIdeal S ^ n ≠ (⊤ : Ideal S) := by
  -- A positive power still lies in the maximal ideal, so it cannot be the unit ideal.
  have hpow_le : maximalIdeal S ^ n ≤ maximalIdeal S := Ideal.pow_le_self hn
  intro htop
  have htop_le : (⊤ : Ideal S) ≤ maximalIdeal S := by
    simpa [htop] using hpow_le
  have hmax : Ideal.IsMaximal (maximalIdeal S) := inferInstance
  exact hmax.ne_top (le_antisymm le_top htop_le)

/-- Helper for Lemma 15.38.1: quotienting a local ring by a proper ideal preserves the
local-ring structure. -/
private theorem quotient_isLocalRing_of_ne_top {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) : IsLocalRing (A ⧸ I) := by
  -- The quotient is nontrivial because the ideal is proper, and surjectivity of the quotient map
  -- then transports locality.
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.38.1: the kernel of the canonical quotient-of-quotient map is the image
of the smaller ideal in the larger quotient. -/
private theorem ker_quotientMap_mk_eq_map {A : Type*} [CommRing A]
    (I J : Ideal A) :
    RingHom.ker
        (Ideal.quotientMap (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I)
          Ideal.le_comap_map) =
      Ideal.map (Ideal.Quotient.mk J) I := by
  -- This is the canonical kernel description for quotienting first by `J` and then by the image
  -- of `I` in `A ⧸ J`.
  simpa using (Ideal.ker_quotientMap_mk (I := I) (J := J))

/-- Helper for Lemma 15.38.1: the canonical quotient-of-quotient map is surjective. -/
private theorem quotientMap_mk_surjective {A : Type*} [CommRing A]
    (I J : Ideal A) :
    Function.Surjective
      (Ideal.quotientMap (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I)
        Ideal.le_comap_map) := by
  intro y
  rcases Ideal.Quotient.mk_surjective y with ⟨a, rfl⟩
  rcases Ideal.Quotient.mk_surjective a with ⟨x, rfl⟩
  refine ⟨Ideal.Quotient.mk J x, ?_⟩
  rfl

/-- Helper for Lemma 15.38.1: a codimension-one subquotient gives a small extension for the
canonical quotient-of-quotient map. -/
private theorem smallExtension_of_codimension_one_quotient {A : Type*} [CommRing A]
    [IsLocalRing A] [IsArtinianRing A]
    (I J : Ideal A) (hJ : J ≠ ⊤)
    [Nontrivial ((A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J)]
    (hlen : Module.length (A ⧸ J) (Ideal.map (Ideal.Quotient.mk J) I) = 1) :
    IsSmallExtension
      (Ideal.quotientMap (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I)
        Ideal.le_comap_map) := by
  let φ : A ⧸ J →+* (A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J :=
    Ideal.quotientMap (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I)
      Ideal.le_comap_map
  letI : IsLocalRing (A ⧸ J) := quotient_isLocalRing_of_ne_top (A := A) J hJ
  have hφsurj : Function.Surjective φ := quotientMap_mk_surjective (I := I) (J := J)
  have hkerlen : Module.length (A ⧸ J) (RingHom.ker φ) = 1 := by
    -- Rewriting the kernel exposes the codimension-one hypothesis in the exact owner form.
    rw [ker_quotientMap_mk_eq_map (I := I) (J := J)]
    exact hlen
  exact
    { surjective := hφsurj
      ker_length := hkerlen }

/-- Helper for Lemma 15.38.1: if an ideal lies in the kernel of `π0`, then `π0` factors through
the quotient by that ideal. -/
private noncomputable def quotientMapToTargetOfLeKer
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B]
    (π0 : A0 →+* B) (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    A0 ⧸ I →+* B :=
  Ideal.Quotient.lift I π0 fun x hx ↦ RingHom.mem_ker.mp (hI hx)

/-- Helper for Lemma 15.38.1: the quotient-factor map agrees with the original map after
precomposing with the quotient map. -/
private theorem quotientMapToTargetOfLeKer_comp_quotient_mk
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B]
    (π0 : A0 →+* B) (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    (quotientMapToTargetOfLeKer (π0 := π0) I hI).comp (Ideal.Quotient.mk I) = π0 := by
  -- The quotient-factor map was defined by lifting `π0`, so it reduces to `π0` on representatives.
  ext x
  rfl

/-- Helper for Lemma 15.38.1: the quotient-factor map stays surjective when `π0` is surjective. -/
private theorem quotientMapToTargetOfLeKer_surjective
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0)
    (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    Function.Surjective (quotientMapToTargetOfLeKer (π0 := π0) I hI) := by
  -- Lift a target element along `π0`, then take its quotient class.
  intro b
  rcases hπ0surj b with ⟨a, rfl⟩
  exact ⟨Ideal.Quotient.mk I a, rfl⟩

/-- Helper for Lemma 15.38.1: the kernel of the quotient-factor map is the image of the original
kernel in the quotient source. -/
private theorem ker_quotientMapToTargetOfLeKer_eq_map
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B]
    (π0 : A0 →+* B) (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    RingHom.ker (quotientMapToTargetOfLeKer (π0 := π0) I hI) =
      Ideal.map (Ideal.Quotient.mk I) (RingHom.ker π0) := by
  -- The quotient-factor map is the canonical lift of `π0`, so its kernel is exactly the image of
  -- `RingHom.ker π0` in the quotient.
  simpa [quotientMapToTargetOfLeKer] using Ideal.ker_quotient_lift (I := I) π0 hI

/-- Helper for Lemma 15.38.1: a quotient inside `ker π0` stays proper as soon as the target of the
factored map is nontrivial and `π0` is surjective. -/
private theorem quotient_ideal_ne_top_of_surjective_to_nontrivial
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B] [Nontrivial B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0)
    (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    I ≠ ⊤ := by
  have hφsurj :
      Function.Surjective (quotientMapToTargetOfLeKer (π0 := π0) I hI) :=
    quotientMapToTargetOfLeKer_surjective (π0 := π0) hπ0surj I hI
  -- A surjection from the quotient to the nontrivial target forces the quotient to be nontrivial.
  intro hItop
  have hQsub : Subsingleton (A0 ⧸ I) := (Ideal.Quotient.subsingleton_iff).2 hItop
  rcases exists_pair_ne B with ⟨b0, b1, hb01⟩
  rcases hφsurj b0 with ⟨x0, rfl⟩
  rcases hφsurj b1 with ⟨x1, rfl⟩
  exact hb01 (congrArg (quotientMapToTargetOfLeKer (π0 := π0) I hI) (Subsingleton.elim x0 x1))

/-- Helper for Lemma 15.38.1: after quotienting by an ideal inside `ker π0`, the source remains a
local ring whenever the original source was local and the target is nontrivial. -/
private theorem quotient_isLocalRing_of_le_ker_surjective
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B] [IsLocalRing A0] [Nontrivial B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0)
    (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    IsLocalRing (A0 ⧸ I) := by
  -- The quotient ideal is proper by surjectivity onto a nontrivial target, so locality descends.
  exact
    quotient_isLocalRing_of_ne_top (A := A0) I
      (quotient_ideal_ne_top_of_surjective_to_nontrivial (π0 := π0) hπ0surj I hI)

/-- Helper for Lemma 15.38.1: quotienting first by `I ≤ ker π0` and then by the image of
`ker π0` yields the same target as the original surjection `π0`. -/
private noncomputable def codimension_one_subquotient_target_equiv
    {A0 : Type*} {B : Type*} [CommRing A0] [CommRing B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0)
    (I : Ideal A0) (hI : I ≤ RingHom.ker π0) :
    ((A0 ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) (RingHom.ker π0)) ≃+* B := by
  let K : Ideal A0 := RingHom.ker π0
  let φ : A0 ⧸ K →+*
      ((A0 ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) K) :=
    Ideal.quotientMap (Ideal.map (Ideal.Quotient.mk I) K) (Ideal.Quotient.mk I)
      Ideal.le_comap_map
  have hφsurj : Function.Surjective φ := by
    -- This is the canonical quotient-of-quotient map, hence surjective.
    simpa [φ, K] using quotientMap_mk_surjective (A := A0) (I := I) (J := K)
  have hφker : RingHom.ker φ = ⊥ := by
    -- Because `I ≤ K = ker π0`, the intermediate quotient contributes no extra kernel on `A0 ⧸ K`.
    rw [ker_quotientMap_mk_eq_map (A := A0) (I := I) (J := K)]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    simpa [K] using hI
  have hφbij : Function.Bijective φ := by
    refine ⟨(RingHom.injective_iff_ker_eq_bot φ).2 hφker, hφsurj⟩
  -- First invert the quotient-of-quotient identification `A0 ⧸ K ≃ ((A0 ⧸ I) ⧸ K/I)`, then use
  -- the quotient-kernel equivalence for the original surjection `π0`.
  exact
    (RingEquiv.ofBijective φ hφbij).symm.trans
      (RingHom.quotientKerEquivOfSurjective hπ0surj)

/-- Helper for Lemma 15.38.1: if an ideal lies in the kernel, the map factors through the quotient
and lands in the range subring. -/
private noncomputable def quotientToRangeOfLeKer {A : Type*} [CommRing A]
    (g : S →+* A) (I : Ideal S) (hI : I ≤ RingHom.ker g) : S ⧸ I →+* g.range :=
  Ideal.Quotient.lift I g.rangeRestrict <| by
    intro x hx
    ext
    exact RingHom.mem_ker.mp (hI hx)

/-- Helper for Lemma 15.38.1: the quotient-to-range factor map is surjective. -/
private theorem quotientToRangeOfLeKer_surjective {A : Type*} [CommRing A]
    (g : S →+* A) (I : Ideal S) (hI : I ≤ RingHom.ker g) :
    Function.Surjective (quotientToRangeOfLeKer (g := g) I hI) := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨x, rfl⟩
  refine ⟨Ideal.Quotient.mk I x, rfl⟩

/-- Helper for Lemma 15.38.1: the range of a continuous map from the maximal-ideal-adic topology
to a discrete nontrivial ring is a local ring. -/
private theorem range_isLocalRing_of_continuous_to_discrete
    {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [Nontrivial A]
    (g : S →+* A)
    (hg : letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g) :
    IsLocalRing g.range := by
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal S) (hI := rfl) (φ := g) hg with
    ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have htopker : (⊤ : Ideal S) ≤ RingHom.ker g := by
      simpa [hn0] using hn
    have hker_one : (1 : S) ∈ RingHom.ker g := htopker (by simp)
    have hzero : (1 : A) = 0 := by
      simpa using (RingHom.mem_ker.mp hker_one)
    exact one_ne_zero hzero
  let Q := S ⧸ maximalIdeal S ^ n
  let _ : Nontrivial Q :=
    Ideal.Quotient.nontrivial_iff.2 (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  letI : IsLocalRing Q :=
    quotient_isLocalRing_of_ne_top (A := S) (maximalIdeal S ^ n)
      (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  let qRange : Q →+* g.range := quotientToRangeOfLeKer (g := g) (maximalIdeal S ^ n) hn
  have hqRange_surj : Function.Surjective qRange :=
    quotientToRangeOfLeKer_surjective (g := g) (maximalIdeal S ^ n) hn
  exact IsLocalRing.of_surjective' qRange hqRange_surj

/-- Helper for Lemma 15.38.1: the range of a continuous map from the maximal-ideal-adic topology
to a discrete nontrivial ring has nilpotent maximal ideal. -/
private theorem range_nilpotent_maximalIdeal_of_continuous_to_discrete
    {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [Nontrivial A]
    (g : S →+* A)
    (hg : letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g) :
    letI : IsLocalRing g.range := range_isLocalRing_of_continuous_to_discrete (g := g) hg
    IsNilpotent (maximalIdeal g.range) := by
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal S) (hI := rfl) (φ := g) hg with
    ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have htopker : (⊤ : Ideal S) ≤ RingHom.ker g := by
      simpa [hn0] using hn
    have hker_one : (1 : S) ∈ RingHom.ker g := htopker (by simp)
    have hzero : (1 : A) = 0 := by
      simpa using (RingHom.mem_ker.mp hker_one)
    exact one_ne_zero hzero
  let Q := S ⧸ maximalIdeal S ^ n
  let _ : Nontrivial Q :=
    Ideal.Quotient.nontrivial_iff.2 (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  letI : IsLocalRing Q :=
    quotient_isLocalRing_of_ne_top (A := S) (maximalIdeal S ^ n)
      (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  let _ : IsLocalRing g.range := range_isLocalRing_of_continuous_to_discrete (g := g) hg
  let qRange : Q →+* g.range := quotientToRangeOfLeKer (g := g) (maximalIdeal S ^ n) hn
  have hqRange_surj : Function.Surjective qRange :=
    quotientToRangeOfLeKer_surjective (g := g) (maximalIdeal S ^ n) hn
  have hnilQ : IsNilpotent (maximalIdeal Q) := by
    -- The quotient kills the chosen positive power of the maximal ideal.
    refine ⟨n, ?_⟩
    have hmap :
        Ideal.map (Ideal.Quotient.mk (maximalIdeal S ^ n)) (maximalIdeal S) =
          maximalIdeal Q := by
      simpa [Q] using
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk (maximalIdeal S ^ n)) Ideal.Quotient.mk_surjective
    calc
      maximalIdeal Q ^ n =
          Ideal.map (Ideal.Quotient.mk (maximalIdeal S ^ n)) (maximalIdeal S) ^ n := by
        rw [← hmap]
      _ = Ideal.map (Ideal.Quotient.mk (maximalIdeal S ^ n)) (maximalIdeal S ^ n) := by
        rw [Ideal.map_pow]
      _ = ⊥ := by
        apply le_antisymm
        · refine Ideal.map_le_iff_le_comap.mpr ?_
          intro x hx
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
        · exact bot_le
  -- Transfer nilpotence across the surjective map `Q → g.range`.
  exact
    nilpotent_maximalIdeal_of_surjective_of_nilpotent_maximalIdeal
      (A' := Q) (A := ↥g.range) (π := qRange) (hπsurj := hqRange_surj) hnilQ

/-- Helper for Lemma 15.38.1: under the Noetherian hypothesis on `S`, the range of a local map
into a local ring with nilpotent maximal ideal is Artinian. -/
private theorem range_isArtinianRing_of_localHom_to_nilpotent_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing S]
    (g : S →+* A) [IsLocalHom g] (hA : IsNilpotent (maximalIdeal A)) :
    IsArtinianRing g.range := by
  let _ : Nontrivial A := IsLocalRing.toNontrivial
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have hg :
      letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g :=
    continuous_of_isLocalHom_to_discrete_of_nilpotent_maximalIdeal (g := g) hA
  letI : IsLocalRing g.range := range_isLocalRing_of_continuous_to_discrete (g := g) hg
  have hnil : IsNilpotent (maximalIdeal g.range) :=
    range_nilpotent_maximalIdeal_of_continuous_to_discrete (g := g) hg
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal S) (hI := rfl) (φ := g) hg with
    ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have htopker : (⊤ : Ideal S) ≤ RingHom.ker g := by
      simpa [hn0] using hn
    have hker_one : (1 : S) ∈ RingHom.ker g := htopker (by simp)
    have hzero : (1 : A) = 0 := by
      simpa using (RingHom.mem_ker.mp hker_one)
    exact one_ne_zero hzero
  let Q := S ⧸ maximalIdeal S ^ n
  let _ : Nontrivial Q :=
    Ideal.Quotient.nontrivial_iff.2 (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  letI : IsLocalRing Q :=
    quotient_isLocalRing_of_ne_top (A := S) (maximalIdeal S ^ n)
      (maximalIdeal_pow_ne_top (n := n) hn_ne_zero)
  letI : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing (maximalIdeal S ^ n)
  let qRange : Q →+* g.range := quotientToRangeOfLeKer (g := g) (maximalIdeal S ^ n) hn
  have hqRange_surj : Function.Surjective qRange :=
    quotientToRangeOfLeKer_surjective (g := g) (maximalIdeal S ^ n) hn
  let e : Q ⧸ RingHom.ker qRange ≃+* g.range := RingHom.quotientKerEquivOfSurjective hqRange_surj
  letI : IsNoetherianRing (Q ⧸ RingHom.ker qRange) :=
    Ideal.Quotient.isNoetherianRing (RingHom.ker qRange)
  letI : IsNoetherianRing g.range := isNoetherianRing_of_ringEquiv _ e
  -- With both locality and Noetherianity available, the nilpotent maximal ideal criterion
  -- upgrades the range ring to an Artinian ring.
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal g.range).mpr hnil

/-- Helper for Lemma 15.38.1: in the source-style preimage-range reduction, the induced maps
`gB : S →+* g.range`, `π0 : A0 →+* g.range`, and `g0A0 : R →+* A0` satisfy the expected
surjectivity and commutativity relations. -/
private theorem preimage_range_square_zero_map_data
    {A : Type w} [CommRing A] (f : R →+* S) (J : Ideal A)
    (g : S →+* A ⧸ J) (g0 : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    let B : Subring (A ⧸ J) := g.range
    let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
    let gB : S →+* B := g.rangeRestrict
    let π0 : A0 →+* B :=
      RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
    let g0A0 : R →+* A0 :=
      RingHom.codRestrict g0 A0 fun x ↦ by
        change (Ideal.Quotient.mk J) (g0 x) ∈ B
        refine ⟨f x, ?_⟩
        simpa using (congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm).symm
    Function.Surjective gB ∧ Function.Surjective π0 ∧
      π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0 := by
  classical
  let B : Subring (A ⧸ J) := g.range
  let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
  let gB : S →+* B := g.rangeRestrict
  let π0 : A0 →+* B :=
    RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
  let g0A0 : R →+* A0 :=
    RingHom.codRestrict g0 A0 fun x ↦ by
      change (Ideal.Quotient.mk J) (g0 x) ∈ B
      refine ⟨f x, ?_⟩
      simpa using (congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm).symm
  change Function.Surjective gB ∧ Function.Surjective π0 ∧
      π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0
  constructor
  · -- The range restriction is surjective by construction.
    intro b
    rcases b with ⟨b, ⟨s, rfl⟩⟩
    exact ⟨s, rfl⟩
  constructor
  · -- Surjectivity of `π0` comes from choosing any representative in the quotient.
    intro b
    rcases Ideal.Quotient.mk_surjective b.1 with ⟨a, ha⟩
    refine ⟨⟨a, ?_⟩, ?_⟩
    · change (Ideal.Quotient.mk J) a ∈ B
      simpa [ha] using b.2
    · apply Subtype.ext
      simpa [π0, ha]
  constructor
  · -- The square remains commutative after corestricting to `A0` and the range `B`.
    ext x
    change (Ideal.Quotient.mk J) (g0 x) = g (f x)
    simpa using congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm
  · -- Forgetting the `A0`-structure recovers the original map `g0`.
    ext x
    rfl

/-- Helper for Lemma 15.38.1: in the source-style preimage-range reduction, the kernel of
`π0 : A0 →+* g.range` is square-zero. -/
private theorem preimage_range_square_zero_kernel
    {A : Type w} [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J) :
    let B : Subring (A ⧸ J) := g.range
    let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
    let π0 : A0 →+* B :=
      RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
    RingHom.ker π0 ^ 2 = ⊥ := by
  let B : Subring (A ⧸ J) := g.range
  let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
  let π0 : A0 →+* B :=
    RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
  change RingHom.ker π0 ^ 2 = ⊥
  apply le_antisymm
  · rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    -- Elements of the kernel lift to elements of `J`, so their product lands in `J² = 0`.
    have hx0 : ((Ideal.Quotient.mk J) (x : A) : A ⧸ J) = 0 := by
      exact congrArg Subtype.val (RingHom.mem_ker.mp hx)
    have hy0 : ((Ideal.Quotient.mk J) (y : A) : A ⧸ J) = 0 := by
      exact congrArg Subtype.val (RingHom.mem_ker.mp hy)
    have hxJ : (x : A) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx0
    have hyJ : (y : A) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy0
    have hxy : ((x : A) * (y : A)) ∈ J ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hxJ hyJ
    have hxy0 : ((x : A) * (y : A)) = 0 := by
      have : ((x : A) * (y : A)) ∈ (⊥ : Ideal A) := by
        simpa [hJ] using hxy
      simpa using this
    change x * y = 0
    apply Subtype.ext
    simpa using hxy0
  · exact bot_le

/-- Helper for Lemma 15.38.1: a surjective map with square-zero kernel reflects units. -/
private theorem isUnit_of_surjective_squareZero
    {A' : Type*} {A : Type*} [CommRing A'] [CommRing A]
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    {x : A'} (hx : IsUnit (π x)) :
    IsUnit x := by
  obtain ⟨u, hxu, _⟩ := isUnit_iff_exists.mp hx
  rcases hπsurj u with ⟨y, rfl⟩
  let k : A' := 1 - x * y
  have hk_mem : k ∈ RingHom.ker π := by
    -- The chosen lift `y` makes `x * y` congruent to `1`, so `k` lies in the kernel.
    change π (1 - x * y) = 0
    simpa [map_sub, hxu]
  have hk_sq_zero : k ^ 2 = 0 := by
    -- A kernel element squares to zero because `ker π` is square-zero.
    have hk2 : k ^ 2 ∈ RingHom.ker π ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hk_mem hk_mem
    have : k ^ 2 ∈ (⊥ : Ideal A') := by
      simpa [hπsq] using hk2
    simpa using this
  have hxy_unit : IsUnit (x * y) := by
    -- The element `x * y = 1 - k` is invertible with inverse `1 + k`.
    have hkxy : x * y = 1 - k := by
      dsimp [k]
      ring
    refine isUnit_iff_exists.mpr ?_
    refine ⟨1 + k, ?_, ?_⟩
    · calc
        x * y * (1 + k) = (1 - k) * (1 + k) := by rw [hkxy]
        _ = 1 - k ^ 2 := by ring
        _ = 1 := by simp [hk_sq_zero]
    · calc
        (1 + k) * (x * y) = (1 + k) * (1 - k) := by rw [hkxy]
        _ = 1 - k ^ 2 := by ring
        _ = 1 := by simp [hk_sq_zero]
  -- Once `x * y` is a unit, so is the left factor `x`.
  exact isUnit_of_mul_isUnit_left hxy_unit

/-- Helper for Lemma 15.38.1: a surjective square-zero map onto a local ring has local source. -/
private theorem isLocalRing_of_surjective_squareZero
    {A' : Type*} {A : Type*} [CommRing A'] [CommRing A] [IsLocalRing A]
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥) :
    IsLocalRing A' := by
  letI : Nontrivial A := IsLocalRing.toNontrivial
  letI : Nontrivial A' := π.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  -- Reflect the target unit dichotomy across the surjective square-zero map.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (π x) with hx | hx
  · left
    exact isUnit_of_surjective_squareZero (π := π) hπsurj hπsq hx
  · right
    have hx' : IsUnit (π (1 - x)) := by
      simpa [map_sub] using hx
    exact isUnit_of_surjective_squareZero (π := π) hπsurj hπsq hx'

/-- Helper for Lemma 15.38.1: in the source-style preimage-range reduction, the induced maps
`gB : S →+* g.range`, `π0 : A0 →+* g.range`, and `g0A0 : R →+* A0` satisfy the expected
surjectivity, square-zero, and commutativity relations. -/
private theorem preimage_range_square_zero_maps
    {A : Type w} [CommRing A] (f : R →+* S) (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J) (g0 : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    let B : Subring (A ⧸ J) := g.range
    let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
    let gB : S →+* B := g.rangeRestrict
    let π0 : A0 →+* B :=
      RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
    let g0A0 : R →+* A0 :=
      RingHom.codRestrict g0 A0 fun x ↦ by
        change (Ideal.Quotient.mk J) (g0 x) ∈ B
        refine ⟨f x, ?_⟩
        simpa using (congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm).symm
    Function.Surjective gB ∧ Function.Surjective π0 ∧ RingHom.ker π0 ^ 2 = ⊥ ∧
      π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0 := by
  -- Route correction: split the old bundled preimage/range package into exact map-data and
  -- kernel-square lemmas, then reassemble the conjunction needed by the source proof.
  have hdata :=
    preimage_range_square_zero_map_data (f := f) (J := J) (g := g) (g0 := g0) hcomm
  have hker := preimage_range_square_zero_kernel (J := J) (hJ := hJ) (g := g)
  dsimp at hdata hker ⊢
  rcases hdata with ⟨hgBsurj, hπ0surj, hcomp, hsubtype⟩
  exact ⟨hgBsurj, hπ0surj, hker, hcomp, hsubtype⟩

/-- Helper for Lemma 15.38.1: for a square-zero surjection `π : A' → A`, restricting the target to
`g.range` and the source to its preimage produces the source-style reduced square-zero problem. -/
private theorem preimage_range_square_zero_subring_maps
    {A' : Type*} {A : Type*} [CommRing A'] [CommRing A]
    (f : R →+* S) (π : A' →+* A) (hπsurj : Function.Surjective π)
    (hπsq : RingHom.ker π ^ 2 = ⊥)
    (g : S →+* A) (g0 : R →+* A')
    (hcomm : π.comp g0 = g.comp f) :
    let B : Subring A := g.range
    let A0 : Subring A' := Subring.comap π B
    let gB : S →+* B := g.rangeRestrict
    let π0 : A0 →+* B := RingHom.codRestrict (π.comp A0.subtype) B fun x ↦ x.2
    let g0A0 : R →+* A0 :=
      RingHom.codRestrict g0 A0 fun x ↦ by
        change π (g0 x) ∈ B
        refine ⟨f x, ?_⟩
        simpa using (congrArg (fun φ : R →+* A => φ x) hcomm).symm
    Function.Surjective gB ∧ Function.Surjective π0 ∧ RingHom.ker π0 ^ 2 = ⊥ ∧
      π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0 := by
  classical
  let B : Subring A := g.range
  let A0 : Subring A' := Subring.comap π B
  let gB : S →+* B := g.rangeRestrict
  let π0 : A0 →+* B := RingHom.codRestrict (π.comp A0.subtype) B fun x ↦ x.2
  let g0A0 : R →+* A0 :=
    RingHom.codRestrict g0 A0 fun x ↦ by
      change π (g0 x) ∈ B
      refine ⟨f x, ?_⟩
      simpa using (congrArg (fun φ : R →+* A => φ x) hcomm).symm
  change Function.Surjective gB ∧ Function.Surjective π0 ∧ RingHom.ker π0 ^ 2 = ⊥ ∧
      π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0
  constructor
  · -- The range restriction is surjective by construction.
    intro b
    rcases b with ⟨b, ⟨s, rfl⟩⟩
    exact ⟨s, rfl⟩
  constructor
  · -- Surjectivity of `π0` follows from surjectivity of `π` on the chosen range representatives.
    intro b
    rcases b with ⟨b, ⟨s, rfl⟩⟩
    rcases hπsurj (g s) with ⟨a, ha⟩
    refine ⟨⟨a, ?_⟩, ?_⟩
    · change π a ∈ B
      refine ⟨s, ?_⟩
      exact ha.symm
    · apply Subtype.ext
      exact ha
  constructor
  · -- The reduced kernel still lies over the original square-zero kernel.
    apply le_antisymm
    · rw [pow_two, Ideal.mul_le]
      intro x hx y hy
      have hx0 : π (x : A') = 0 := by
        exact congrArg Subtype.val (RingHom.mem_ker.mp hx)
      have hy0 : π (y : A') = 0 := by
        exact congrArg Subtype.val (RingHom.mem_ker.mp hy)
      have hxker : (x : A') ∈ RingHom.ker π := RingHom.mem_ker.mpr hx0
      have hyker : (y : A') ∈ RingHom.ker π := RingHom.mem_ker.mpr hy0
      have hxy : ((x : A') * (y : A')) ∈ RingHom.ker π ^ 2 := by
        simpa [pow_two] using Ideal.mul_mem_mul hxker hyker
      have hxy0 : ((x : A') * (y : A')) = 0 := by
        have : ((x : A') * (y : A')) ∈ (⊥ : Ideal A') := by
          simpa [hπsq] using hxy
        simpa using this
      change x * y = 0
      apply Subtype.ext
      simpa using hxy0
    · exact bot_le
  constructor
  · -- The square remains commutative after the range/preimage corestrictions.
    ext x
    change π (g0 x) = g (f x)
    simpa using congrArg (fun φ : R →+* A => φ x) hcomm
  · -- Forgetting the `A0`-structure recovers the original source map.
    ext x
    rfl

/-- Helper for Lemma 15.38.1: a surjective square-zero local map lifts nilpotence of the target
maximal ideal back to the source maximal ideal. -/
private theorem nilpotent_maximalIdeal_of_surjective_squareZero_of_nilpotent_target
    {A' : Type*} {A : Type*} [CommRing A'] [CommRing A] [IsLocalRing A'] [IsLocalRing A]
    [Nontrivial A] (π : A' →+* A) (hπsurj : Function.Surjective π)
    (hπsq : RingHom.ker π ^ 2 = ⊥) (hA : IsNilpotent (maximalIdeal A)) :
    IsNilpotent (maximalIdeal A') := by
  letI : IsLocalHom π := IsLocalHom.of_surjective π hπsurj
  rcases hA with ⟨n, hn⟩
  have hmap :
      Ideal.map π (maximalIdeal A') = maximalIdeal A :=
    IsLocalRing.map_maximalIdeal_of_surjective π hπsurj
  have hpow_le_ker : maximalIdeal A' ^ n ≤ RingHom.ker π := by
    apply (Ideal.map_eq_bot_iff_le_ker π).mp
    calc
      Ideal.map π (maximalIdeal A' ^ n) = Ideal.map π (maximalIdeal A') ^ n := by
        rw [Ideal.map_pow]
      _ = maximalIdeal A ^ n := by rw [hmap]
      _ = ⊥ := hn
  refine ⟨n + n, le_antisymm ?_ bot_le⟩
  calc
    maximalIdeal A' ^ (n + n) = maximalIdeal A' ^ n * maximalIdeal A' ^ n := by
      rw [pow_add]
    _ ≤ RingHom.ker π * RingHom.ker π := by
      rw [Ideal.mul_le]
      intro r hr s hs
      exact Ideal.mul_mem_mul (hpow_le_ker hr) (hpow_le_ker hs)
    _ = ⊥ := by simpa [sq] using hπsq

/-- Helper for Lemma 15.38.1: a surjective local homomorphism induces a bijection on residue
fields. -/
private theorem residueField_bijective_of_surjective_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Nontrivial B] (φ : A →+* B) (hφsurj : Function.Surjective φ) [IsLocalHom φ] :
    Function.Bijective (IsLocalRing.ResidueField.map φ) := by
  let hField : Field (IsLocalRing.ResidueField B) := inferInstance
  let _ : Nontrivial (IsLocalRing.ResidueField B) := by
    exact hField.toNontrivial
  constructor
  · -- The residue-field map is injective because its source is a field and its target is
    -- nontrivial.
    exact RingHom.injective (IsLocalRing.ResidueField.map φ)
  · -- Surjectivity follows by lifting a residue class to `B` and then lifting that element
    -- further to `A` along the surjective map `φ`.
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    rcases hφsurj b with ⟨a, rfl⟩
    refine ⟨IsLocalRing.residue A a, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue φ a

/-- Helper for Lemma 15.38.1: a lift through a square-zero quotient is continuous once the
quotient map is continuous for the maximal-ideal adic topology. -/
private theorem continuous_of_square_zero_lift_of_continuous_quotient
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J)
    (hg : letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g)
    (φ : S →+* A) (hφ : (Ideal.Quotient.mk J).comp φ = g) :
    letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
    Continuous φ := by
  letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
  have hmadic : IsAdic (maximalIdeal S) := rfl
  rcases
      RingHom.pow_le_ker_of_continuous_to_discrete_quotient
        (I := maximalIdeal S) (hI := hmadic) (φ := g) hg with
    ⟨n, hn⟩
  have hmapJ : Ideal.map φ (maximalIdeal S ^ n) ≤ J := by
    -- Any source element killed modulo `J` is sent by the lift into `J`.
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx
    have hxzero : g x = 0 := RingHom.mem_ker.mp (hn hx)
    have hxquot : Ideal.Quotient.mk J (φ x) = 0 := by
      have hxquot' : Ideal.Quotient.mk J (φ x) = g x := DFunLike.congr_fun hφ x
      rw [hxzero] at hxquot'
      exact hxquot'
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hxquot
  have hmapBot : Ideal.map φ (maximalIdeal S ^ (n * 2)) ≤ ⊥ := by
    -- Squaring the killed power forces the lift into `J² = 0`.
    calc
      Ideal.map φ (maximalIdeal S ^ (n * 2)) =
          Ideal.map φ ((maximalIdeal S ^ n) ^ 2) := by
        rw [pow_mul]
      _ = Ideal.map φ (maximalIdeal S ^ n) ^ 2 := by
        rw [Ideal.map_pow]
      _ ≤ J ^ 2 := Ideal.pow_right_mono hmapJ 2
      _ = ⊥ := hJ
  have hkerφ : maximalIdeal S ^ (n * 2) ≤ RingHom.ker φ := by
    -- Rewriting `Ideal.map φ (...) ≤ ⊥` as a kernel containment gives the adic continuity
    -- criterion for the lift.
    simpa [RingHom.ker_eq_comap_bot] using
      (Ideal.map_le_iff_le_comap.mp hmapBot :
        maximalIdeal S ^ (n * 2) ≤ Ideal.comap φ ⊥)
  have hopen : IsOpen (((maximalIdeal S ^ (n * 2) : Ideal S)) : Set S) := by
    exact (isAdic_iff.mp hmadic).1 (n * 2)
  exact RingHom.continuous_of_open_ideal_le_ker φ (maximalIdeal S ^ (n * 2)) hopen hkerφ

/-- Helper for Lemma 15.38.1: the source-style preimage/range lift over `A0 → g.range` produces
the required continuous lift into `A`. -/
private theorem preimage_range_liftPayload_to_topological_lift
    {A : Type w} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J)
    (hg : letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g)
    (g0 : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    let B : Subring (A ⧸ J) := g.range
    let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
    let gB : S →+* B := g.rangeRestrict
    let π0 : A0 →+* B :=
      RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
    let g0A0 : R →+* A0 :=
      RingHom.codRestrict g0 A0 fun x ↦ by
        change (Ideal.Quotient.mk J) (g0 x) ∈ B
        refine ⟨f x, ?_⟩
        simpa using (congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm).symm
    maximalIdealAdic_liftPayload f π0 gB g0A0 →
      ∃ φ : S →+* A,
        (letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
         Continuous φ) ∧
          (Ideal.Quotient.mk J).comp φ = g ∧ φ.comp f = g0 := by
  classical
  let B : Subring (A ⧸ J) := g.range
  let A0 : Subring A := Subring.comap (Ideal.Quotient.mk J) B
  let gB : S →+* B := g.rangeRestrict
  let π0 : A0 →+* B :=
    RingHom.codRestrict ((Ideal.Quotient.mk J).comp A0.subtype) B fun x ↦ x.2
  let g0A0 : R →+* A0 :=
    RingHom.codRestrict g0 A0 fun x ↦ by
      change (Ideal.Quotient.mk J) (g0 x) ∈ B
      refine ⟨f x, ?_⟩
      simpa using (congrArg (fun φ : R →+* A ⧸ J => φ x) hcomm).symm
  change maximalIdealAdic_liftPayload f π0 gB g0A0 →
      ∃ φ : S →+* A,
        (letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
         Continuous φ) ∧
          (Ideal.Quotient.mk J).comp φ = g ∧ φ.comp f = g0
  intro hlift
  rcases hlift with ⟨gLift, hgLift, hgLift0⟩
  let φ : S →+* A := A0.subtype.comp gLift
  have hπ0_desc :
      B.subtype.comp π0 = (Ideal.Quotient.mk J).comp A0.subtype := by
    -- The restricted quotient map `π0` is just the ambient quotient map with codomain restricted
    -- to the range subring `B`.
    ext x
    rfl
  have hgB_desc : B.subtype.comp gB = g := by
    -- Forgetting the range corestriction recovers the original quotient map `g`.
    ext x
    rfl
  have hquot : (Ideal.Quotient.mk J).comp φ = g := by
    -- Postcompose the `A0`-lift with the ambient quotient map and then simplify through `π0`.
    calc
      (Ideal.Quotient.mk J).comp φ = ((Ideal.Quotient.mk J).comp A0.subtype).comp gLift := by
        rfl
      _ = (B.subtype.comp π0).comp gLift := by
        rw [hπ0_desc]
      _ = B.subtype.comp (π0.comp gLift) := by
        rw [RingHom.comp_assoc]
      _ = B.subtype.comp gB := by
        rw [hgLift]
      _ = g := hgB_desc
  have hg0A0_desc : A0.subtype.comp g0A0 = g0 := by
    -- Forgetting the preimage-subring corestriction recovers `g0`.
    ext x
    rfl
  have hcomp0 : φ.comp f = g0 := by
    -- The lifted map agrees with `g0` after restricting and then forgetting the `A0`-structure.
    calc
      φ.comp f = (A0.subtype.comp gLift).comp f := by
        rfl
      _ = A0.subtype.comp (gLift.comp f) := by
        rw [RingHom.comp_assoc]
      _ = A0.subtype.comp g0A0 := by
        rw [hgLift0]
      _ = g0 := hg0A0_desc
  have hcontφ :
      letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous φ :=
    continuous_of_square_zero_lift_of_continuous_quotient
      (J := J) (hJ := hJ) (g := g) (hg := hg) (φ := φ) hquot
  exact ⟨φ, hcontφ, hquot, hcomp0⟩

/-- Helper for Lemma 15.38.1: once the reduced preimage/range square-zero problem
`π0 : A0 →+* B` has been fixed, the assumed square-zero lifting criterion applies directly to it. -/
private theorem preimage_range_payload_of_squareZero_lifting
    (f : R →+* S)
    (hsq : maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition.{u, v, w} f)
    {A0 : Type w} {B : Type w} [CommRing A0] [CommRing B] [IsLocalRing A0]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0) (hπ0sq : RingHom.ker π0 ^ 2 = ⊥)
    (hA0nil : IsNilpotent (maximalIdeal A0)) (gB : S →+* B) (g0A0 : R →+* A0) :
    let _ : Nontrivial B := maximalIdealAdic_nontrivialTarget_of_squareZero π0 hπ0sq
    letI : IsLocalRing B := IsLocalRing.of_surjective' π0 hπ0surj
    ∀ [IsLocalHom gB] (_ : maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB)
      (_ : π0.comp g0A0 = gB.comp f),
      maximalIdealAdic_liftPayload f π0 gB g0A0 := by
  intro hBnontrivial hgBLocal hresB hcomm
  -- This helper is only the source-proof adapter step: apply the assumed square-zero lifting
  -- criterion to the already prepared reduced problem `(π0, gB, g0A0)`.
  let _ : Nontrivial B := hBnontrivial
  letI : IsLocalHom gB := hgBLocal
  exact hsq π0 hπ0surj hπ0sq hA0nil gB g0A0 hresB hcomm

/-- Helper for Lemma 15.38.1: after naming the source-style reduced data
`A0 = (Ideal.Quotient.mk J)⁻¹(g.range)` and `B = g.range`, the local square-zero lifting
criterion applies directly to that reduced problem. -/
private theorem preimage_range_square_zero_reduction_payload
    (f : R →+* S)
    (hsq : maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition.{u, v, w} f)
    {A0 : Type w} {B : Type w} [CommRing A0] [CommRing B] [IsLocalRing A0] [IsLocalRing B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0) (hπ0sq : RingHom.ker π0 ^ 2 = ⊥)
    (hA0nil : IsNilpotent (maximalIdeal A0))
    (gB : S →+* B) [IsLocalHom gB] (g0A0 : R →+* A0)
    (hresB : maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB)
    (hπ0comm : π0.comp g0A0 = gB.comp f) :
    maximalIdealAdic_liftPayload f π0 gB g0A0 := by
  -- Route correction: keep the source reduction on the explicit named data `(A0, B, π0, gB)`,
  -- and use the square-zero lifting criterion only at that reduced level.
  let _ : Nontrivial B := maximalIdealAdic_nontrivialTarget_of_squareZero π0 hπ0sq
  have hpayload :=
    preimage_range_payload_of_squareZero_lifting
      (f := f) (hsq := hsq) (π0 := π0) (hπ0surj := hπ0surj) (hπ0sq := hπ0sq)
      (hA0nil := hA0nil) (gB := gB) (g0A0 := g0A0)
  -- The payload theorem already packages the reduced lift exactly in the required shape.
  exact hpayload hresB hπ0comm

/-- Helper for Lemma 15.38.1: a lift over the reduced source-style subring map `π0 : A0 →+* B`
produces a lift over the original surjection `π : A' →+* A`. -/
private theorem preimage_range_subring_liftPayload_to_lift
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (f : R →+* S) (π : A' →+* A) (g : S →+* A) (g0 : R →+* A')
    (hcomm : π.comp g0 = g.comp f) :
    let B : Subring A := g.range
    let A0 : Subring A' := Subring.comap π B
    let gB : S →+* B := g.rangeRestrict
    let π0 : A0 →+* B := RingHom.codRestrict (π.comp A0.subtype) B fun x ↦ x.2
    let g0A0 : R →+* A0 :=
      RingHom.codRestrict g0 A0 fun x ↦ by
        change π (g0 x) ∈ B
        refine ⟨f x, ?_⟩
        simpa using (congrArg (fun φ : R →+* A => φ x) hcomm).symm
    maximalIdealAdic_liftPayload f π0 gB g0A0 →
      maximalIdealAdic_liftPayload f π g g0 := by
  classical
  let B : Subring A := g.range
  let A0 : Subring A' := Subring.comap π B
  let gB : S →+* B := g.rangeRestrict
  let π0 : A0 →+* B := RingHom.codRestrict (π.comp A0.subtype) B fun x ↦ x.2
  let g0A0 : R →+* A0 :=
    RingHom.codRestrict g0 A0 fun x ↦ by
      change π (g0 x) ∈ B
      refine ⟨f x, ?_⟩
      simpa using (congrArg (fun φ : R →+* A => φ x) hcomm).symm
  change maximalIdealAdic_liftPayload f π0 gB g0A0 →
      maximalIdealAdic_liftPayload f π g g0
  intro hlift
  rcases hlift with ⟨gLift, hgLift, hgLift0⟩
  let φ : S →+* A' := A0.subtype.comp gLift
  have hπ0_desc : B.subtype.comp π0 = π.comp A0.subtype := by
    -- Forgetting the codomain restriction on `π0` recovers the original map `π`.
    ext x
    rfl
  have hgB_desc : B.subtype.comp gB = g := by
    -- Forgetting the range restriction on `gB` recovers `g`.
    ext x
    rfl
  have hg0A0_desc : A0.subtype.comp g0A0 = g0 := by
    -- Forgetting the preimage-subring restriction on `g0A0` recovers `g0`.
    ext x
    rfl
  refine ⟨φ, ?_, ?_⟩
  · -- Postcompose the reduced lift with the subtype maps to recover the original square over `A`.
    calc
      π.comp φ = (π.comp A0.subtype).comp gLift := by
        rfl
      _ = (B.subtype.comp π0).comp gLift := by
        rw [hπ0_desc.symm]
      _ = B.subtype.comp (π0.comp gLift) := by
        rw [RingHom.comp_assoc]
      _ = B.subtype.comp gB := by
        rw [hgLift]
      _ = g := hgB_desc
  · -- The reduced lift still agrees with the chosen source map after forgetting the `A0`-structure.
    calc
      φ.comp f = (A0.subtype.comp gLift).comp f := by
        rfl
      _ = A0.subtype.comp (gLift.comp f) := by
        rw [RingHom.comp_assoc]
      _ = A0.subtype.comp g0A0 := by
        rw [hgLift0]
      _ = g0 := hg0A0_desc

/-- Helper for Lemma 15.38.1: in the nontrivial quotient case of the topological lifting problem,
the source-style preimage/range reduction turns the problem into the local square-zero lifting
criterion and then reconstructs a continuous lift to the ambient ring. -/
private theorem reduced_square_zero_lifting_data
    {A0 : Type w} {B : Type w} [CommRing A0] [CommRing B] [IsLocalRing B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0) (hπ0sq : RingHom.ker π0 ^ 2 = ⊥)
    (gB : S →+* B) (hgBsurj : Function.Surjective gB) [IsLocalHom gB]
    (hBnil : IsNilpotent (maximalIdeal B)) :
    letI : IsLocalRing A0 := isLocalRing_of_surjective_squareZero (π := π0) hπ0surj hπ0sq
    IsNilpotent (maximalIdeal A0) ∧
      maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB := by
  let _ : Nontrivial B := IsLocalRing.toNontrivial
  letI : IsLocalRing A0 := isLocalRing_of_surjective_squareZero (π := π0) hπ0surj hπ0sq
  have hA0nil : IsNilpotent (maximalIdeal A0) :=
    -- Nilpotence lifts back across the reduced square-zero surjection.
    nilpotent_maximalIdeal_of_surjective_squareZero_of_nilpotent_target
      (π := π0) (hπsurj := hπ0surj) (hπsq := hπ0sq) hBnil
  have hresB : maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB := by
    -- The reduced target map is still surjective and local, so it induces the residue-field
    -- bijection required by the owner criterion.
    simpa [maximalIdealAdic_residueFieldMapBijective] using
      residueField_bijective_of_surjective_localHom (φ := gB) hgBsurj
  exact ⟨hA0nil, hresB⟩

/-- Helper for Lemma 15.38.1: in the nontrivial quotient case of the topological lifting problem,
the source-style preimage/range reduction turns the problem into the local square-zero lifting
criterion and then reconstructs a continuous lift to the ambient ring. -/
private theorem topological_lift_of_preimage_range_square_zero_condition
    (f : R →+* S)
    (hsq : maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition.{u, v, w} f)
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J : Ideal A) [DiscreteTopology (A ⧸ J)] [Nontrivial (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J)
    (hg : letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous g)
    (g0 : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    ∃ φ : S →+* A,
      (letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
       Continuous φ) ∧
        (Ideal.Quotient.mk J).comp φ = g ∧ φ.comp f = g0 := by
  -- TODO: the source-faithful proof still runs through the explicit reduced data
  -- `B := g.range`, `A0 := (Ideal.Quotient.mk J)⁻¹(B)`, the payload adapter
  -- `preimage_range_payload_of_squareZero_lifting`, and then the ambient reconstruction.
  -- The current blocker is the same owner-level `whnf`/instance-search blowup on theorem-local
  -- reduced data; the next pivot should hide that application behind a transport-stable theorem.
  sorry

/-- Helper for Lemma 15.38.1: after the source-style preimage/range reduction, the remaining
Artinian square-zero lifting problem is exactly the Noetherian converse over an Artinian target.
This is the point where the source proof filters `RingHom.ker π0` by
`((maximalIdeal A0) ^ i) * RingHom.ker π0` and reduces to codimension-one small extensions. -/
private theorem square_zero_lift_of_smallExtension_lifting_of_artinian_target
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S]
    (hsmall : maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition.{u, v, w} f)
    {A0 : Type w} {B : Type w} [CommRing A0] [CommRing B]
    [IsLocalRing A0] [IsLocalRing B] [IsArtinianRing B]
    (π0 : A0 →+* B) (hπ0surj : Function.Surjective π0) (hπ0sq : RingHom.ker π0 ^ 2 = ⊥)
    (hA0nil : IsNilpotent (maximalIdeal A0))
    (gB : S →+* B) [IsLocalHom gB] (g0A0 : R →+* A0)
    (hresB : maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB)
    (hπ0comm : π0.comp g0A0 = gB.comp f) :
    maximalIdealAdic_liftPayload f π0 gB g0A0 := by
  -- Route correction: the public theorem should stop at the reduced Artinian problem.
  -- The remaining source-faithful work is the Artinian devissage on `RingHom.ker π0`, not a
  -- second reconstruction inside the ambient square-zero extension.
  -- TODO: first prove the base case `maximalIdeal A0 * RingHom.ker π0 = ⊥` by the product of
  -- codimension-one quotients supplied by `hsmall`, then run the filtration
  -- `((maximalIdeal A0) ^ i) * RingHom.ker π0`.
  sorry

/-- Helper for Lemma 15.38.1: under the Noetherian hypothesis, the small-extension lifting
criterion reduces a general square-zero problem to the source-style Artinian target devissage over
`A0 = π⁻¹(g.range)`. -/
private theorem square_zero_lift_of_smallExtension_lifting
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S]
    (hsmall : maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition.{u, v, w} f) :
    maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition.{u, v, w} f := by
  dsimp [maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition]
  intro A' A _ _ _ π hπsurj hπsq hA' g
  let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
  letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  intro hgLocal g0 hres hcomm
  letI : IsLocalHom g := hgLocal
  have hA : IsNilpotent (maximalIdeal A) :=
    nilpotent_maximalIdeal_of_surjective_of_nilpotent_maximalIdeal π hπsurj hA'
  let B : Subring A := g.range
  let A0 : Subring A' := Subring.comap π B
  let gB : S →+* B := g.rangeRestrict
  let π0 : A0 →+* B := RingHom.codRestrict (π.comp A0.subtype) B fun x ↦ x.2
  let g0A0 : R →+* A0 :=
    RingHom.codRestrict g0 A0 fun x ↦ by
      change π (g0 x) ∈ B
      refine ⟨f x, ?_⟩
      simpa using (congrArg (fun φ : R →+* A => φ x) hcomm).symm
  have hmapData :
      Function.Surjective gB ∧ Function.Surjective π0 ∧ RingHom.ker π0 ^ 2 = ⊥ ∧
        π0.comp g0A0 = gB.comp f ∧ A0.subtype.comp g0A0 = g0 := by
    -- This is the direct square-zero analogue of the earlier quotient-side range/preimage package.
    simpa [B, A0, gB, π0, g0A0] using
      preimage_range_square_zero_subring_maps
        (f := f) (π := π) (hπsurj := hπsurj) (hπsq := hπsq) (g := g) (g0 := g0) hcomm
  rcases hmapData with ⟨hgBsurj, hπ0surj, hπ0sq, hπ0comm, hg0A0_subtype⟩
  have hBLocal : IsLocalRing B :=
    range_isLocalRing_of_continuous_to_discrete
      (g := g)
      (continuous_of_isLocalHom_to_discrete_of_nilpotent_maximalIdeal (g := g) hA)
  letI : IsLocalRing B := hBLocal
  have hBArt : IsArtinianRing B := by
    -- The Noetherian hypothesis on `S` turns `B = g.range` into the Artinian target used in the
    -- source proof.
    simpa [B] using
      range_isArtinianRing_of_localHom_to_nilpotent_maximalIdeal (S := S) (g := g) hA
  have hA0Local : IsLocalRing A0 :=
    isLocalRing_of_surjective_squareZero (π := π0) hπ0surj hπ0sq
  letI : IsLocalRing A0 := hA0Local
  have hBnil : IsNilpotent (maximalIdeal B) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp hBArt
  have hA0nil : IsNilpotent (maximalIdeal A0) :=
    nilpotent_maximalIdeal_of_surjective_squareZero_of_nilpotent_target
      (π := π0) (hπsurj := hπ0surj) (hπsq := hπ0sq) hBnil
  haveI : IsLocalHom gB := IsLocalHom.of_surjective gB hgBsurj
  have hresB : maximalIdealAdic_residueFieldMapBijective π0 hπ0surj hπ0sq gB := by
    -- The reduced target map is still surjective and local, so it has the same residue-field
    -- bijectivity shape needed for the Artinian devissage.
    simpa [maximalIdealAdic_residueFieldMapBijective] using
      residueField_bijective_of_surjective_localHom (φ := gB) hgBsurj
  have hA0Lift : maximalIdealAdic_liftPayload f π0 gB g0A0 := by
    -- The remaining source-faithful work is now isolated in the Artinian target lemma.
    exact
      square_zero_lift_of_smallExtension_lifting_of_artinian_target
        (f := f) hsmall (π0 := π0) (hπ0surj := hπ0surj) (hπ0sq := hπ0sq)
        (hA0nil := hA0nil) (gB := gB) (g0A0 := g0A0) hresB hπ0comm
  -- Once the reduced Artinian problem is solved, forget the subring wrappers to recover a lift
  -- for the original square-zero extension.
  rcases hA0Lift with ⟨gLift, hgLift, hgLift0⟩
  let φ : S →+* A' := A0.subtype.comp gLift
  have hπ0_desc : B.subtype.comp π0 = π.comp A0.subtype := by
    -- Forgetting the codomain restriction on `π0` recovers `π`.
    ext x
    rfl
  have hgB_desc : B.subtype.comp gB = g := by
    -- Forgetting the range restriction on `gB` recovers `g`.
    ext x
    rfl
  have hg0A0_desc : A0.subtype.comp g0A0 = g0 := by
    -- Forgetting the preimage-subring restriction on `g0A0` recovers `g0`.
    ext x
    rfl
  refine ⟨φ, ?_, ?_⟩
  · -- Postcompose the reduced lift through the subtype maps to recover the original square.
    calc
      π.comp φ = (π.comp A0.subtype).comp gLift := by
        rfl
      _ = (B.subtype.comp π0).comp gLift := by
        rw [hπ0_desc.symm]
      _ = B.subtype.comp (π0.comp gLift) := by
        rw [RingHom.comp_assoc]
      _ = B.subtype.comp gB := by
        rw [hgLift]
      _ = g := hgB_desc
  · -- The reduced lift still restricts to the original source map `g0`.
    calc
      φ.comp f = (A0.subtype.comp gLift).comp f := by
        rfl
      _ = A0.subtype.comp (gLift.comp f) := by
        rw [RingHom.comp_assoc]
      _ = A0.subtype.comp g0A0 := by
        rw [hgLift0]
      _ = g0 := hg0A0_desc

/-- Helper for Lemma 15.38.1: a subsingleton target ring admits the unique ring homomorphism
from any source semiring. -/
private def ringHomToSubsingletonTarget
    {A : Type*} {B : Type*} [NonAssocSemiring A] [NonAssocSemiring B] [Subsingleton B] :
    A →+* B :=
  { toFun := fun _ ↦ 0
    map_one' := Subsingleton.elim _ _
    map_mul' := fun _ _ ↦ Subsingleton.elim _ _
    map_zero' := rfl
    map_add' := fun _ _ ↦ Subsingleton.elim _ _ }

/-- Helper for Lemma 15.38.1: if the square-zero quotient `A ⧸ J` is trivial, then `A` is
trivial as well, so the unique map `S → A` is the required continuous lift. -/
private theorem lift_of_square_zero_subsingleton_quotient
    (f : R →+* S)
    {A : Type w} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J) (g0 : R →+* A)
    (hQ : Subsingleton (A ⧸ J)) :
    ∃ φ : S →+* A,
      (letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
       Continuous φ) ∧
        (Ideal.Quotient.mk J).comp φ = g ∧ φ.comp f = g0 := by
  letI : Subsingleton (A ⧸ J) := hQ
  have h1J : (1 : A) ∈ J := by
    -- In the trivial quotient, `1` maps to `0`, so `1 ∈ J`.
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim _ _)
  have hA_subsingleton : Subsingleton A := by
    -- Square-zero then forces `1 = 0`, which collapses the entire ring.
    have h1J2 : (1 : A) ∈ J ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul h1J h1J
    have h10 : (1 : A) = 0 := by
      have h10mem : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [← hJ]
        exact h1J2
      exact h10mem
    refine ⟨fun x y ↦ ?_⟩
    calc
      x = x * 1 := by simp
      _ = x * 0 := by rw [h10]
      _ = 0 := by simp
      _ = y * 0 := by simp
      _ = y * 1 := by rw [h10]
      _ = y := by simp
  letI : Subsingleton A := hA_subsingleton
  let φ : S →+* A := ringHomToSubsingletonTarget
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- The unique map to a trivial target is constant, hence continuous.
    letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
    simpa [φ, ringHomToSubsingletonTarget] using
      (continuous_const : Continuous fun _ : S ↦ (0 : A))
  · -- Any two maps into the trivial quotient agree.
    ext x
    exact Subsingleton.elim _ _
  · -- Any two maps into the trivial ring agree.
    ext x
    exact Subsingleton.elim _ _

-- Proof sketch: use Lemma `15.37.2` to identify formal smoothness for the maximal-ideal-adic
-- topology with the discrete-source lifting property, then restrict the test objects to local
-- square-zero extensions with nilpotent maximal ideal and residue-field isomorphism. For the
-- converse, replace an arbitrary square-zero lifting problem by the inverse-image local subring
-- generated by the image of `S` in `A ⧸ J`, exactly as in the Stacks argument. The lifted ring
-- hom is automatically local because its composite with the quotient map is `g`.
/-- Lemma 15.38.1: a local homomorphism `f : R →+* S` is formally smooth for the maximal-ideal-adic
topology on `S` if and only if every square-zero lifting problem against a local ring `A` with
nilpotent maximal ideal and residue-field isomorphism `S → A ⧸ J` admits a lift
(hence automatically a local lift). -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_square_zero_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition.{u, v, w} f := by
  constructor
  · intro hf
    dsimp [maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition]
    intro A' A _ _ _ π hπsurj hπsq hA g
    let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
    letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
    intro hgLocal g0 _ hcomm
    letI : IsLocalHom g := hgLocal
    -- Solve the local square-zero problem by translating it to the quotient-kernel lifting owner.
    exact
      liftPayload_of_formally_smooth_for_adic_of_surjective_square_zero
        (f := f) (hf := hf) (π := π) (hπsurj := hπsurj) (hπsq := hπsq)
        (hA' := hA) (g := g) (g0 := g0) (hcomm := hcomm)
  · -- TODO: reduce a general topological square-zero lifting problem to the local range/preimage
    -- setup from the source proof, then apply the assumed local lifting criterion there.
    intro hsq
    exact (RingHom.formally_smooth_for_adic_iff f (maximalIdeal S)).mpr <| by
      letI : TopologicalSpace R := ⊥
      letI : DiscreteTopology R := ⟨rfl⟩
      letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      refine
        { toContinuous := continuous_of_discreteTopology
          lift_condition := ?_ }
      intro A _ _ _ J _ hJ g hg g0 _ hcomm
      classical
      by_cases hQ : Nontrivial (A ⧸ J)
      · letI : Nontrivial (A ⧸ J) := hQ
        -- The nontrivial quotient case is exactly the source-style preimage/range reduction.
        exact
          topological_lift_of_preimage_range_square_zero_condition
            (f := f) (hsq := hsq) (A := A) (J := J) (hJ := hJ) (g := g) (hg := hg) (g0 := g0)
            (hcomm := hcomm)
      · exact
          lift_of_square_zero_subsingleton_quotient
            (f := f) (J := J) (hJ := hJ) (g := g) (g0 := g0)
            (not_nontrivial_iff_subsingleton.mp hQ)

-- Proof sketch: the forward implication is the main equivalence above. For the converse under the
-- Noetherian hypothesis on `S`, devissage through the filtration of `J` by one-dimensional
-- residue-field quotients reduces the square-zero criterion to the case where `A → A ⧸ J` is a
-- small extension, and then the assumed lifting property supplies the required lift, which is
-- again automatically local.
/-- The Noetherian refinement of the local lifting criterion: it is enough to test liftings only
against small extensions `A → A ⧸ J` with the same residue-field condition, asking only for a
lift in the conclusion since locality is derived. -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_smallExtension_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition.{u, v, w} f := by
  constructor
  · intro hf
    dsimp [maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition]
    intro A' A _ _ π hπsmall g
    letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
    intro hgLocal g0 hres hcomm
    letI : IsLocalHom g := hgLocal
    let hπ : IsSmallExtension π := hπsmall
    rcases
        smallExtension_has_squareZero_kernel_and_nilpotent_maximalIdeal (π := π) with
      ⟨hπsq, hA'⟩
    -- Any small extension is already an admissible square-zero test object for the first
    -- equivalence, so the main theorem immediately supplies the lift.
    exact
      (formally_smooth_for_maximalIdeal_adic_iff_local_square_zero_residueFieldIso_lifting
          (f := f)).mp hf π hπ.surjective hπsq hA' g g0
        (by
          -- The residue-field hypothesis is the same owner-level datum after unfolding the
          -- canonical target-local-ring wrapper coming from surjectivity.
          simpa [maximalIdealAdic_residueFieldMapBijective,
            maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension,
            maximalIdealAdic_isLocalRingTargetOfSmallExtension] using hres)
        hcomm
  · -- Route correction: the source proof does not factor a general square-zero kernel into an
    -- arbitrary chain of small extensions. It first reduces to the case
    -- `maximalIdeal A * J = ⊥`, and only then uses the family of codimension-one quotients of
    -- `J` to assemble a lift.
    intro hsmall
    have hsq :
        maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition (R := R) (S := S) f :=
      square_zero_lift_of_smallExtension_lifting.{u, v, w} (f := f) hsmall
    -- Once the Noetherian converse is proved for the square-zero criterion, the public small-
    -- extension equivalence is just the previous theorem applied to that derived criterion.
    exact
      (formally_smooth_for_maximalIdeal_adic_iff_local_square_zero_residueFieldIso_lifting.{u, v, w}
          (f := f)).mpr
        hsq

end

end RingHom
