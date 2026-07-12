import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Chap09.Proposition_9_9_4_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GaloisPowerAction
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GammaSubgroupAction
import LinearRepresentations_Serre_1977.Chap12.CyclicGeneratorFieldOrbitSum
import LinearRepresentations_Serre_1977.Chap12.CyclicCharacterFourier
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_4

open scoped Representation SubgroupInduction

noncomputable section

universe u v w

namespace Representation

open CategoryTheory

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
/- Faithfulness sync (§12.7, cf. Lemma 16 = Lemma_12_12_7_4): Serre's coefficient ring `A = ℤ[μ_m]`
is integrally closed; the cyclic-descent reconstruction here realizes `K`-valued data inside
`A ⊗ R_K(C)`, which requires `A` integrally closed (false for non-maximal orders such as
`ℤ[2i] ⊂ ℚ(i)`). -/
variable [IsIntegrallyClosed A]

local notation "CycSub" => { H : Subgroup G // IsCyclic H }
local notation "ΓK" => Γ[K](G)

private local instance : Fintype CycSub := Fintype.ofFinite CycSub
private local instance : DecidableEq { H : Subgroup G // IsCyclic H } := Classical.decEq _

/-- Helper for Infra 12 7 CyclicDescent: the direct-sum induction map
`⨁_{H cyclic} (A ⊗ R_K(H)) → A ⊗ R_K(G)` used in the denominator-clearing descent step. -/
def cyclicSubgroupInductionOverAlgebra :
    (Π₀ H : CycSub, A ⊗R[K](H.1)) →ₗ[A] A ⊗R[K](G) :=
  open Classical in
  DFinsupp.lsum A fun H ↦ H.1.characterRingOverFieldAlgebraScalarExtensionInduction

/-- Helper for Infra 12 7 CyclicDescent: pointwise membership in the principal ideal `|G|A`
produces a global quotient function by `|G|`. -/
lemma exists_group_order_pointwise_quotient
    (f : G → A)
    (hfg : ∀ s : G, f s ∈ Ideal.span ({(Nat.card G : A)} : Set A)) :
    ∃ g : G → A, ∀ s : G, f s = (Nat.card G : A) * g s := by
  classical
  -- Rewrite the pointwise principal-ideal hypothesis as explicit divisibility by `|G|`.
  let g : G → A := fun s ↦
    Classical.choose (by simpa [Ideal.mem_span_singleton, -Nat.card_eq_fintype_card] using hfg s)
  refine ⟨g, ?_⟩
  intro s
  exact Classical.choose_spec
    (by simpa [Ideal.mem_span_singleton, -Nat.card_eq_fintype_card] using hfg s)

/-- Helper for Infra 12 7 CyclicDescent: once `f = |G| • g` pointwise, `Γ[K](G)`-constancy of `f`
descends to the quotient function `g`. -/
lemma group_order_pointwise_quotient_isConstantOnGaloisPowerClasses
    {f g : G → A}
    (hf : IsConstantOnGaloisPowerClasses (Γ[K](G)) f)
    (hfg : ∀ s : G, f s = (Nat.card G : A) * g s) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) g := by
  refine ⟨?_⟩
  intro s t hst
  -- Cancel the nonzero scalar `|G|` inside the domain `A`.
  have hcardK : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardA : (Nat.card G : A) ≠ 0 := by
    intro hzero
    exact hcardK <| by
      simpa using congrArg (algebraMap A K) hzero
  have hft : f s = f t := hf.eq_of_mk_eq hst
  rw [hfg s, hfg t] at hft
  exact mul_left_cancel₀ hcardA hft

/-- Helper for Infra 12 7 CyclicDescent: composing a `Γ[K](G)`-constant `A`-valued function with
the fraction-field map preserves `Γ[K](G)`-constancy. -/
lemma algebraMap_comp_isConstantOnGaloisPowerClasses
    {g : G → A}
    (hg : IsConstantOnGaloisPowerClasses (Γ[K](G)) g) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) ((algebraMap A K) ∘ g) := by
  refine ⟨?_⟩
  intro s t hst
  -- The quotient relation is checked pointwise, so functoriality of `algebraMap` is enough.
  simpa using congrArg (algebraMap A K) (hg.eq_of_mk_eq hst)

/-- Helper for Infra 12 7 CyclicDescent: induction commutes with multiplying by an ambient class
function after restricting that function to the subgroup. -/
lemma induced_mul_eq_induced_mul_restrict_of_isClassFunction
    (H : Subgroup G) (ψ : H → K) {φ : G → K}
    (hφ : _root_.IsClassFunction φ) :
    Ind[H](fun h : H ↦ ψ h * φ h) = Ind[H](ψ) * φ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  -- This is the same pointwise induction/product identity as in `Theorem_12_12_5_1`; the only
  -- input is conjugacy invariance of the ambient factor `φ`.
  ext x
  have hxeq :
      ((Ind[H](ψ) * φ) x : K) = (Ind[H](fun h : H ↦ ψ h * φ h) x : K) := by
    simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
    rw [mul_assoc, Finset.sum_mul]
    have hterms :
        ∀ s ∈ (Finset.univ : Finset G),
          ((if hs : s⁻¹ * x * s ∈ H then ψ ⟨s⁻¹ * x * s, hs⟩ else 0 : K) * φ x) =
            (if hs : s⁻¹ * x * s ∈ H then
              ψ ⟨s⁻¹ * x * s, hs⟩ * φ (s⁻¹ * x * s) else 0 : K) := by
      intro s hs
      by_cases hsx : s⁻¹ * x * s ∈ H
      · have hsconj_eq : s * (s⁻¹ * x * s) * s⁻¹ = x := by
          group
        have hsconj : IsConj (s⁻¹ * x * s) x := isConj_iff.2 ⟨s, hsconj_eq⟩
        have hφconj : φ (s⁻¹ * x * s) = φ x := hφ.eq_of_isConj hsconj
        simp [hsx, hφconj]
      · simp [hsx]
    exact congrArg (fun z : K ↦ ((Nat.card H : K)⁻¹) * z) (Finset.sum_congr rfl hterms)
  exact congrArg ((↑) : K → L) hxeq.symm

/-- Helper for Infra 12 7 CyclicDescent: each value of the cyclic denominator-cleared `θ`-summand
already lies in the image of `A → K`. -/
lemma cyclic_theta_mul_quotient_apply_mem_range
    (H : CycSub) {g : G → A} (h : H.1) :
    ((θ[H.1] : H.1 → K) h * algebraMap A K (g h)) ∈
      Set.range (algebraMap A K) := by
  by_cases hgen : Subgroup.zpowers h = ⊤
  · refine ⟨(Nat.card H.1 : A) * g h, ?_⟩
    -- On a generator, `θ[H]` is the group order, so the value is visibly `A`-valued.
    rw [map_mul]
    have htheta : (θ[H.1] : H.1 → K) h = (Nat.card H.1 : K) := by
      simp [Representation.cyclicGroupTheta, hgen]
    rw [htheta]
    simp
  · refine ⟨0, ?_⟩
    -- Away from generators, `θ[H]` vanishes.
    have htheta : (θ[H.1] : H.1 → K) h = 0 := by
      simp [Representation.cyclicGroupTheta, hgen]
    rw [htheta]
    simp

/-- Helper for Infra 12 7 CyclicDescent: the exponent of `⟨x⟩` divides the ambient exponent of
`G`, so ambient exponent units can be reduced modulo `exp(⟨x⟩)`. -/
lemma exponent_zpowers_dvd_ambient_local
    (x : G) :
    Monoid.exponent (Subgroup.zpowers x) ∣ Monoid.exponent G := by
  -- This is the concrete arithmetic bridge from the cyclic factor back to the ambient group.
  simpa [Subgroup.exponent_toSubmonoid] using
    Monoid.exponent_submonoid_dvd (Subgroup.zpowers x).toSubmonoid

/-- Helper for Infra 12 7 CyclicDescent: on `C = ⟨x⟩`, use the reduction of the ambient arithmetic
subgroup `Γ[K](G)` rather than an unavailable literal intrinsic `Γ[K](C)`. -/
def reducedAmbientGammaSubgroupOnZpowers
    (x : G) :
    Subgroup (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ :=
  Subgroup.map (ZMod.unitsMap (exponent_zpowers_dvd_ambient_local (G := G) x)) ΓK

/-- Helper for Infra 12 7 CyclicDescent: the denominator-cleared cyclic source on `C = ⟨x⟩`
attached to the ambient quotient function `g`. -/
def cyclic_theta_quotient_source
    (x : G) (g : G → A) :
    Subgroup.zpowers x → A :=
  open Classical in
    fun c ↦ if Subgroup.zpowers c = ⊤ then (Nat.card (Subgroup.zpowers x) : A) * g c else 0

/-- Helper for Infra 12 7 CyclicDescent: the `θ`-weighted summand on `⟨x⟩` is exactly the
scalar-extension of the explicit denominator-cleared source. -/
lemma cyclic_theta_mul_quotient_eq_algebraMap_cyclic_theta_quotient_source
    (x : G) {g : G → A} :
    (fun c : Subgroup.zpowers x ↦
      (θ[Subgroup.zpowers x] : Subgroup.zpowers x → K) c * algebraMap A K (g c)) =
        (algebraMap A K) ∘ cyclic_theta_quotient_source (A := A) x g := by
  classical
  -- Rewrite `θ[C]` by cases on whether `c` generates the whole cyclic subgroup `C = ⟨x⟩`.
  funext c
  by_cases hc : Subgroup.zpowers c = ⊤
  · rw [Function.comp_apply, cyclic_theta_quotient_source, if_pos hc, map_mul]
    have htheta :
        (θ[Subgroup.zpowers x] : Subgroup.zpowers x → K) c =
          (Nat.card (Subgroup.zpowers x) : K) := by
      simp [Representation.cyclicGroupTheta, hc]
    rw [htheta]
    simp
  · rw [Function.comp_apply, cyclic_theta_quotient_source, if_neg hc]
    have htheta : (θ[Subgroup.zpowers x] : Subgroup.zpowers x → K) c = 0 := by
      simp [Representation.cyclicGroupTheta, hc]
    rw [htheta, zero_mul, map_zero]

/-- Helper for Infra 12 7 CyclicDescent: composing two arithmetic power maps multiplies their
exponent units. -/
lemma gamma_pow_mul_aux
    {H : Type*} [Group H] [Finite H]
    {ΓH : Subgroup (ZMod (Monoid.exponent H))ˣ}
    (y : H) (t u : ΓH) :
    (y ^ t) ^ Representation.galoisPowerExponentUnit
        (t := (u : (ZMod (Monoid.exponent H))ˣ)) =
      y ^ (t * u) := by
  -- Normalize both subgroup powers to natural-number exponents and compare modulo `exp(H)`.
  rw [Representation.pow_subgroup_eq_pow_nat, ← pow_mul, Representation.pow_subgroup_eq_pow_nat]
  rw [Monoid.pow_eq_mod_exponent]
  congr
  exact
    (ZMod.val_mul
      (((t : (ZMod (Monoid.exponent H))ˣ) : ZMod (Monoid.exponent H)))
      (((u : (ZMod (Monoid.exponent H))ˣ) : ZMod (Monoid.exponent H)))).symm

/-- Helper for Infra 12 7 CyclicDescent: an arithmetic power followed by the inverse power returns
the original element. -/
lemma gamma_pow_inv_aux
    {H : Type*} [Group H] [Finite H]
    {ΓH : Subgroup (ZMod (Monoid.exponent H))ˣ}
    (y : H) (t : ΓH) :
    (y ^ t) ^ Representation.galoisPowerExponentUnit
        (t := ((t⁻¹ : ΓH) : (ZMod (Monoid.exponent H))ˣ)) = y := by
  -- The inverse unit cancels the original exponent-unit action inside the finite cyclic exponent.
  calc
    (y ^ t) ^ Representation.galoisPowerExponentUnit
        (t := ((t⁻¹ : ΓH) : (ZMod (Monoid.exponent H))ˣ)) =
        y ^ (t * t⁻¹) := gamma_pow_mul_aux y t t⁻¹
    _ = y ^ (1 : ΓH) := by simp
    _ = y := by
      rw [Representation.pow_subgroup_eq_pow_nat]
      change y ^ ((1 : ZMod (Monoid.exponent H)).val) = y
      rw [ZMod.val_one_eq_one_mod]
      calc
        y ^ (1 % Monoid.exponent H) = y ^ 1 := by
          simpa using (Eq.symm (@Monoid.pow_eq_mod_exponent H _ 1 y))
        _ = y := by simp

/-- Helper for Infra 12 7 CyclicDescent: arithmetic powers preserve the generated subgroup in any
finite group. -/
lemma zpowers_pow_eq_zpowers_aux
    {H : Type*} [Group H] [Finite H]
    {ΓH : Subgroup (ZMod (Monoid.exponent H))ˣ}
    (y : H) (t : ΓH) :
    Subgroup.zpowers (y ^ t : H) = Subgroup.zpowers y := by
  -- Each direction comes from expressing one generator as a power of the other via `t` and `t⁻¹`.
  apply le_antisymm
  · refine Subgroup.zpowers_le.2 ?_
    rw [Representation.pow_subgroup_eq_pow_nat]
    exact Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) _
  · refine Subgroup.zpowers_le.2 ?_
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨(Representation.galoisPowerExponentUnit
          (t := ((t⁻¹ : ΓH) : (ZMod (Monoid.exponent H))ˣ)) : ℤ),
        by
          change (y ^ t) ^
              ((Representation.galoisPowerExponentUnit
                (t := ((t⁻¹ : ΓH) : (ZMod (Monoid.exponent H))ˣ)) : ℤ)) = y
          rw [zpow_natCast]
          exact gamma_pow_inv_aux (ΓH := ΓH) y t⟩

/-- Helper for Infra 12 7 CyclicDescent: any reduced ambient arithmetic power on `⟨x⟩` is
realized by an ambient `Γ[K](G)`-power after coercing back to `G`. -/
lemma zpowers_pow_eq_ambient_gamma_pow_of_mem_reducedAmbient_local
    (x : G) (c : Subgroup.zpowers x)
    (u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) :
    ∃ t : ΓK, ((c ^ u : Subgroup.zpowers x) : G) = (c : G) ^ t := by
  let hdiv : Monoid.exponent (Subgroup.zpowers x) ∣ Monoid.exponent G :=
    exponent_zpowers_dvd_ambient_local (G := G) x
  rcases Subgroup.mem_map.mp u.2 with ⟨t, ht, hu⟩
  let tΓ : ΓK := ⟨t, ht⟩
  refine ⟨tΓ, ?_⟩
  -- Compare the intrinsic and ambient power exponents through the common residue class modulo
  -- `exp(⟨x⟩)`.
  have hmod :
      Representation.galoisPowerExponentUnit
          (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) ≡
        Representation.galoisPowerExponentUnit
          (t := (t : (ZMod (Monoid.exponent G))ˣ))
          [MOD Monoid.exponent (Subgroup.zpowers x)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((Representation.galoisPowerExponentUnit
            (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) : ℕ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) =
        (((u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) :
            (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simp [Representation.galoisPowerExponentUnit]
      _ =
        (((ZMod.unitsMap hdiv (t : (ZMod (Monoid.exponent G))ˣ)) :
            (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            rw [hu]
      _ =
        ((((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).cast) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simpa using (ZMod.unitsMap_val hdiv (t : (ZMod (Monoid.exponent G))ˣ)).symm
      _ =
        ((Representation.galoisPowerExponentUnit (t := (t : (ZMod (Monoid.exponent G))ˣ)) : ℕ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simp [Representation.galoisPowerExponentUnit]
  simpa [Representation.pow_subgroup_eq_pow_nat] using
    (pow_eq_pow_of_modEq hmod (Subgroup.pow_exponent_eq_one (H := Subgroup.zpowers x) c.2) :
      (c : G) ^
          Representation.galoisPowerExponentUnit
            (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) =
        (c : G) ^
          Representation.galoisPowerExponentUnit
            (t := (t : (ZMod (Monoid.exponent G))ˣ)))

/-- Helper for Infra 12 7 CyclicDescent: the denominator-cleared cyclic source on `⟨x⟩` is
constant on the reduced ambient arithmetic power classes coming from `Γ[K](G)`. -/
lemma cyclic_theta_quotient_source_isConstantOnReducedAmbientClasses
    (x : G) {g : G → A}
    (hg : IsConstantOnGaloisPowerClasses ΓK g) :
    IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
      (cyclic_theta_quotient_source (A := A) x g) := by
  letI : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  have hsourceClass : _root_.IsClassFunction (cyclic_theta_quotient_source (A := A) x g) := by
    refine ⟨?_⟩
    intro c d hcd
    -- On the cyclic factor `⟨x⟩`, conjugacy is trivial, so the source depends only on the point.
    have hEq : c = d := by
      rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcd) with ⟨a, ha⟩
      have hd_val : (d : G) = c := by
        have hcomm :
            ((a : Subgroup.zpowers x) : G) * c = (c : G) * a := by
          exact setLike_mul_comm a.2 c.2
        calc
          (d : G) = ((a : G) * c) * (a⁻¹ : G) := by
            exact congrArg Subtype.val ha.symm
          _ = ((c : G) * a) * (a⁻¹ : G) := by rw [hcomm]
          _ = (c : G) * ((a : G) * (a⁻¹ : G)) := by rw [mul_assoc]
          _ = c := by simp
      exact (Subtype.ext hd_val).symm
    cases hEq
    rfl
  refine (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hsourceClass).2 ?_
  intro c u
  -- Route correction: keep Serre's source on `⟨x⟩` and compare reduced ambient powers with actual
  -- ambient `Γ[K](G)`-powers before asking for any owner-membership statement.
  obtain ⟨t, ht⟩ :=
    zpowers_pow_eq_ambient_gamma_pow_of_mem_reducedAmbient_local
      (K := K) (G := G) x c u
  have hgpow :
      g (((c ^ u : Subgroup.zpowers x) : G)) = g c := by
    have hpow :
        ∀ s : G, ∀ v : ΓK, g s = g (s ^ v) :=
      (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hg.isClassFunction).1 hg
    calc
      g (((c ^ u : Subgroup.zpowers x) : G)) = g ((c : G) ^ t) := by rw [ht]
      _ = g c := (hpow (c : G) t).symm
  have hgen :
      Subgroup.zpowers (c ^ u : Subgroup.zpowers x) = Subgroup.zpowers c := by
    simpa using
      (zpowers_pow_eq_zpowers_aux
        (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c u)
  by_cases hc : Subgroup.zpowers c = ⊤
  · have hcu : Subgroup.zpowers (c ^ u : Subgroup.zpowers x) = ⊤ := by
      rw [hgen]
      exact hc
    rw [cyclic_theta_quotient_source, cyclic_theta_quotient_source, if_pos hcu, if_pos hc, hgpow]
  · have hcu : Subgroup.zpowers (c ^ u : Subgroup.zpowers x) ≠ ⊤ := by
      intro hcu
      exact hc <| by rw [← hgen]; exact hcu
    rw [cyclic_theta_quotient_source, cyclic_theta_quotient_source, if_neg hcu, if_neg hc]

/-- Helper for Infra 12 7 CyclicDescent: on a single cyclic direct-sum summand, the total owner
map agrees with the corresponding subgroup induction map. -/
lemma cyclicSubgroupInduction_single_overAlgebra
    (H : CycSub) (χ : A ⊗R[K](H.1)) :
    cyclicSubgroupInductionOverAlgebra (K := K) (A := A) (G := G) (DFinsupp.single H χ) =
      H.1.characterRingOverFieldAlgebraScalarExtensionInduction χ := by
  classical
  -- This is the defining `DFinsupp.single` evaluation rule for the direct-sum induction map.
  rw [cyclicSubgroupInductionOverAlgebra, DFinsupp.lsum]
  exact DFinsupp.sumAddHom_single
    (fun J ↦ (J.1.characterRingOverFieldAlgebraScalarExtensionInduction).toAddMonoidHom) H χ

/-- Helper for Infra 12 7 CyclicDescent: the explicit owner map built from `DFinsupp.lsum`
evaluates on a single summand as the corresponding subgroup induction function. -/
lemma explicit_cyclicSubgroupInduction_single_overAlgebra
    (H : CycSub) (χ : A ⊗R[K](H.1)) :
    (((A ⊗R[K](G)).subtype.comp
        (DFinsupp.lsum A fun J : CycSub ↦
          J.1.characterRingOverFieldAlgebraScalarExtensionInduction))
      (DFinsupp.single H χ)) =
        (H.1.characterRingOverFieldAlgebraScalarExtensionInduction χ : G → K) := by
  -- Unfold the explicit owner map and evaluate the `DFinsupp.single` input.
  rw [LinearMap.comp_apply, DFinsupp.lsum]
  simp

/-- Helper for Infra 12 7 CyclicDescent: Serre's cyclic-subgroup `θ`-identity rewritten using the
current file's owner index `CycSub`. -/
lemma cyclicSubgroup_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one_local :
    ∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K)) = (Nat.card G : K) • (1 : G → K) := by
  classical
  -- Reindex the Chapter 9 cyclic-subgroup sum through the subtype used by the direct-sum owner.
  calc
    ∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K))
        = ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            symm
            refine Finset.sum_subtype (M := G → K) (s := Subgroup.cyclicSubgroups G) ?_
              (fun H ↦ Ind[H](θ[H]))
            intro H
            exact
              (Subgroup.mem_cyclicSubgroups : H ∈ Subgroup.cyclicSubgroups G ↔ IsCyclic H)
    _ = (Nat.card G : K) • (1 : G → K) := by
          exact sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := K)

/-- Helper for Infra 12 7 CyclicDescent: the reduced-ambient quotient of `C = ⟨x⟩` is finite, so
its quotient classes can be summed over explicitly. -/
local instance reducedAmbient_galoisPowerClass_finite (x : G) :
    Finite
      (GaloisPowerClass (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)) :=
  Finite.of_surjective _
    (galoisPowerClassMk_surjective (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x))

/-- Helper for Infra 12 7 CyclicDescent: choose the canonical finite-indexing structure on the
reduced-ambient quotient of `C = ⟨x⟩`. -/
local instance reducedAmbient_galoisPowerClass_fintype (x : G) :
    Fintype
      (GaloisPowerClass (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)) :=
  Fintype.ofFinite _

/-- Helper for Infra 12 7 CyclicDescent: quotient classes on the reduced-ambient quotient of
`C = ⟨x⟩` have decidable equality. -/
local instance reducedAmbient_galoisPowerClass_decidableEq (x : G) :
    DecidableEq
      (GaloisPowerClass (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)) :=
  Classical.decEq _

/-- Helper for Infra 12 7 CyclicDescent: restricting an ambient `Γ[K](G)`-constant function to the
cyclic factor `C = ⟨x⟩` preserves constancy for the reduced ambient arithmetic subgroup on `C`. -/
lemma ambient_restriction_isConstantOnReducedAmbientClasses
    (x : G) {g : G → A}
    (hg : IsConstantOnGaloisPowerClasses ΓK g) :
    IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
      (fun c : Subgroup.zpowers x ↦ g c) := by
  letI : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  have hrestrictClass : _root_.IsClassFunction (fun c : Subgroup.zpowers x ↦ g c) := by
    refine ⟨?_⟩
    intro c d hcd
    -- On the cyclic factor `⟨x⟩`, conjugacy is trivial, so restriction depends only on the point.
    have hEq : c = d := by
      rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcd) with ⟨a, ha⟩
      have hd_val : (d : G) = c := by
        have hcomm :
            ((a : Subgroup.zpowers x) : G) * c = (c : G) * a := by
          exact setLike_mul_comm a.2 c.2
        calc
          (d : G) = ((a : G) * c) * (a⁻¹ : G) := by
            exact congrArg Subtype.val ha.symm
          _ = ((c : G) * a) * (a⁻¹ : G) := by rw [hcomm]
          _ = (c : G) * ((a : G) * (a⁻¹ : G)) := by rw [mul_assoc]
          _ = c := by simp
      exact (Subtype.ext hd_val).symm
    simpa [hEq]
  refine (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hrestrictClass).2 ?_
  intro c u
  -- Compare the reduced-ambient power on `C` with an actual ambient `Γ[K](G)`-power on `G`.
  obtain ⟨t, ht⟩ :=
    zpowers_pow_eq_ambient_gamma_pow_of_mem_reducedAmbient_local
      (K := K) (G := G) x c u
  have hgpow :
      ∀ s : G, ∀ v : ΓK, g s = g (s ^ v) :=
    (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hg.isClassFunction).1 hg
  calc
    g c = g ((c : G) ^ t) := hgpow (c : G) t
    _ = g (((c ^ u : Subgroup.zpowers x) : G)) := by rw [ht]

/-- Helper for Infra 12 7 CyclicDescent: the reduced-ambient quotient class `q` on `C = ⟨x⟩`
supports the source basis function that is `|C|` exactly on generator points in that class. -/
def reducedAmbient_class_indicator_source
    (x : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)) :
    Subgroup.zpowers x → A :=
  open Classical in
    fun c ↦
      if Subgroup.zpowers c = ⊤ ∧
          galoisPowerClassMk (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q
      then
        (Nat.card (Subgroup.zpowers x) : A)
      else
        0

/-- Helper for Infra 12 7 CyclicDescent: fixing a representative `cq` of a reduced-ambient
quotient class on `C = ⟨x⟩` gives the corresponding orbit-supported cyclic source centered at
that representative. -/
def reducedAmbient_orbit_supported_source
    (x : G) (cq : Subgroup.zpowers x) :
    Subgroup.zpowers x → A :=
  open Classical in
    fun c ↦
      if ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u then
        (Nat.card (Subgroup.zpowers x) : A)
      else
        0

/-- Helper for Infra 12 7 CyclicDescent: inside the cyclic factor `C = ⟨x⟩`, equality of
reduced-ambient quotient classes means that one representative is obtained from the other by a
reduced-ambient arithmetic power. -/
lemma exists_reducedAmbient_power_of_galoisPowerClass_eq
    (x : G) {c cq : Subgroup.zpowers x}
    (hcq :
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c =
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq) :
    ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u := by
  classical
  let _ : CommGroup (Subgroup.zpowers x) := IsCyclic.commGroup
  -- Unpack quotient equality into the explicit reduced-ambient orbit relation on `C`.
  have horbit :
      MulAction.orbitRel
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
        (ConjClasses (Subgroup.zpowers x)) (ConjClasses.mk c) (ConjClasses.mk cq) :=
    Quotient.exact hcq
  rw [MulAction.orbitRel_apply] at horbit
  rcases horbit with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  -- In the commutative cyclic group `C`, equality of conjugacy classes is actual equality.
  have hmk : ConjClasses.mk (cq ^ u : Subgroup.zpowers x) = ConjClasses.mk c := by
    simpa using hu
  exact (isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)).symm

/-- Helper for Infra 12 7 CyclicDescent: if a reduced-ambient quotient class is represented by a
nongenerator of `C = ⟨x⟩`, then the corresponding class indicator source vanishes identically. -/
lemma reducedAmbient_class_indicator_source_eq_zero_of_not_generator_representative
    (x : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x))
    (cq : Subgroup.zpowers x)
    (hcq :
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq = q)
    (hgen : Subgroup.zpowers cq ≠ ⊤) :
    reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q = 0 := by
  classical
  ext c
  by_cases hc :
      Subgroup.zpowers c = ⊤ ∧
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q
  · -- Any element in the same reduced-ambient class as a nongenerator has the same generated
    -- subgroup, so the generator branch is impossible.
    have hclass :
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c =
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq := by
      simpa [hcq] using hc.2
    obtain ⟨u, hu⟩ :=
      exists_reducedAmbient_power_of_galoisPowerClass_eq
        (K := K) (G := G) x hclass
    have hzpow :
        Subgroup.zpowers c = Subgroup.zpowers cq := by
      calc
        Subgroup.zpowers c = Subgroup.zpowers (cq ^ u : Subgroup.zpowers x) := by rw [hu]
        _ = Subgroup.zpowers cq := by
              simpa using
                (zpowers_pow_eq_zpowers_aux
                  (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq u)
    have hfalse :
        ¬ (Subgroup.zpowers c = ⊤ ∧
            galoisPowerClassMk (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q) := by
      intro hpair
      exact hgen <| by simpa [hzpow] using hpair.1
    simp [reducedAmbient_class_indicator_source, hfalse]
  · -- Outside the defining support predicate, the class indicator is zero by definition.
    simp [reducedAmbient_class_indicator_source, hc]

/-- Helper for Infra 12 7 CyclicDescent: if `cq` is a generator representing the reduced-ambient
quotient class `q`, then the class indicator is exactly the orbit-supported cyclic source centered
at `cq`. -/
lemma reducedAmbient_class_indicator_source_eq_orbit_supported_of_generator_representative
    (x : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x))
    (cq : Subgroup.zpowers x)
    (hcq :
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq = q)
    (hgen : Subgroup.zpowers cq = ⊤) :
    reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q =
      reducedAmbient_orbit_supported_source K x cq := by
  classical
  ext c
  by_cases hc :
      Subgroup.zpowers c = ⊤ ∧
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q
  · -- On the supported class, quotient equality gives an explicit reduced-ambient power from
    -- the representative `cq` to `c`.
    have hclass :
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c =
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq := by
      simpa [hcq] using hc.2
    obtain ⟨u, hu⟩ :=
      exists_reducedAmbient_power_of_galoisPowerClass_eq
        (K := K) (G := G) x hclass
    have hsupp :
        ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u :=
      ⟨u, hu⟩
    -- Both sources take the generator value `|C|` on the represented orbit.
    rw [reducedAmbient_class_indicator_source, if_pos hc]
    rw [reducedAmbient_orbit_supported_source, if_pos hsupp]
  · have hsupp_false :
        ¬ ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u := by
      rintro ⟨u, hu⟩
      have hzpow :
          Subgroup.zpowers c = Subgroup.zpowers cq := by
        calc
          Subgroup.zpowers c = Subgroup.zpowers (cq ^ u : Subgroup.zpowers x) := by rw [hu]
          _ = Subgroup.zpowers cq := by
                simpa using
                  (zpowers_pow_eq_zpowers_aux
                    (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq u)
      have hclass :
          galoisPowerClassMk (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q := by
        rw [hu]
        have hpowclass :
            galoisPowerClassMk (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
              (cq ^ u : Subgroup.zpowers x) =
            galoisPowerClassMk (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq := by
          apply Quotient.sound
          change
            MulAction.orbitRel
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
              (ConjClasses (Subgroup.zpowers x))
              (ConjClasses.mk (cq ^ u : Subgroup.zpowers x))
              (ConjClasses.mk cq)
          rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
          refine ⟨u, ?_⟩
          change ((u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) • ConjClasses.mk cq) =
            ConjClasses.mk (cq ^ u : Subgroup.zpowers x)
          change
            ConjClasses.pow
              (Representation.galoisPowerExponentUnit
                (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)))
              (ConjClasses.mk cq) =
            ConjClasses.mk (cq ^ u : Subgroup.zpowers x)
          rw [pow_subgroup_eq_pow_nat]
          exact ConjClasses.pow_mk
            (Representation.galoisPowerExponentUnit
              (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ))) cq
        simpa [hcq] using hpowclass
      exact hc ⟨by simpa [hgen] using hzpow, hclass⟩
    -- Away from the orbit of a generator representative, both functions vanish.
    rw [reducedAmbient_class_indicator_source, if_neg hc]
    rw [reducedAmbient_orbit_supported_source, if_neg hsupp_false]

/-- Helper for Infra 12 7 CyclicDescent: the representative-centered reduced-ambient orbit source
on `C = ⟨x⟩` is constant on the reduced-ambient arithmetic power classes inherited from `Γ[K](G)`.
-/
lemma reducedAmbientOrbitSupportedSource_isConstantOnReducedAmbientClasses
    (x : G) (cq : Subgroup.zpowers x) :
    IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
      (reducedAmbient_orbit_supported_source (K := K) (A := A) (G := G) x cq) := by
  letI : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  have hsourceClass :
      _root_.IsClassFunction
        (reducedAmbient_orbit_supported_source (K := K) (A := A) (G := G) x cq) := by
    refine ⟨?_⟩
    intro c d hcd
    -- On the cyclic factor `⟨x⟩`, conjugacy is trivial, so the source depends only on the point.
    have hEq : c = d := by
      rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcd) with ⟨a, ha⟩
      have hd_val : (d : G) = c := by
        have hcomm :
            ((a : Subgroup.zpowers x) : G) * c = (c : G) * a := by
          exact setLike_mul_comm a.2 c.2
        calc
          (d : G) = ((a : G) * c) * (a⁻¹ : G) := by
            exact congrArg Subtype.val ha.symm
          _ = ((c : G) * a) * (a⁻¹ : G) := by rw [hcomm]
          _ = (c : G) * ((a : G) * (a⁻¹ : G)) := by rw [mul_assoc]
          _ = c := by simp
      exact (Subtype.ext hd_val).symm
    simpa [hEq]
  refine (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hsourceClass).2 ?_
  intro c u
  -- Compare the representative-support predicate before and after a reduced-ambient power map.
  have hsupp_iff :
      (∃ v : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ v) ↔
        ∃ v : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c ^ u = cq ^ v := by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v * u, ?_⟩
      calc
        c ^ u = (cq ^ v) ^ u := by rw [hv]
        _ = cq ^ (v * u) := by
              simpa using
                (gamma_pow_mul_aux
                  (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq v u)
    · rintro ⟨v, hv⟩
      refine ⟨v * u⁻¹, ?_⟩
      calc
        c = (c ^ u) ^ u⁻¹ := by
              simpa using
                (gamma_pow_inv_aux
                  (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c u).symm
        _ = (cq ^ v) ^ u⁻¹ := by rw [hv]
        _ = cq ^ (v * u⁻¹) := by
              simpa using
                (gamma_pow_mul_aux
                  (ΓH := reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq v u⁻¹)
  by_cases hsupp :
      ∃ v : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ v
  · have hsupp_pow :
        ∃ v : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c ^ u = cq ^ v :=
      hsupp_iff.1 hsupp
    rw [reducedAmbient_orbit_supported_source, if_pos hsupp]
    rw [reducedAmbient_orbit_supported_source, if_pos hsupp_pow]
  · have hsupp_pow :
        ¬ ∃ v : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c ^ u = cq ^ v := by
      intro hsupp_pow
      exact hsupp (hsupp_iff.2 hsupp_pow)
    rw [reducedAmbient_orbit_supported_source, if_neg hsupp]
    rw [reducedAmbient_orbit_supported_source, if_neg hsupp_pow]

/-- Helper for Infra 12 7 CyclicDescent: the representative-centered reduced-ambient orbit source
on `C = ⟨x⟩` only takes the values `0` and `|C|`, so every value lies in the principal ideal
generated by `|C|`. -/
lemma reducedAmbientOrbitSupportedSource_mem_span_card
    (x : G) (cq c : Subgroup.zpowers x) :
    reducedAmbient_orbit_supported_source K x cq c ∈
      Ideal.span ({(Nat.card (Subgroup.zpowers x) : A)} : Set A) := by
  classical
  by_cases hsupp :
      ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u
  · -- On the supported orbit, the source takes the generator value `|C|`.
    rw [reducedAmbient_orbit_supported_source, if_pos hsupp]
    exact Ideal.subset_span (by simp)
  · -- Away from the supported orbit, the source vanishes by definition.
    rw [reducedAmbient_orbit_supported_source, if_neg hsupp]
    exact zero_mem (Ideal.span ({(Nat.card (Subgroup.zpowers x) : A)} : Set A))

/-- Helper for Infra 12 7 CyclicDescent: if `cq` generates `C = ⟨x⟩`, then every element of `C`
is an integral power of `cq`. -/
lemma exists_zpow_eq_of_zpowers_eq_top
    (x : G) {cq c : Subgroup.zpowers x}
    (hcq : Subgroup.zpowers cq = ⊤) :
    ∃ n : ℤ, c = cq ^ n := by
  have hc_mem : c ∈ Subgroup.zpowers cq := by
    simpa [hcq] using (show c ∈ (⊤ : Subgroup (Subgroup.zpowers x)) from by simp)
  rcases Subgroup.mem_zpowers_iff.mp hc_mem with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Helper for Infra 12 7 CyclicDescent: taking a reduced-ambient arithmetic power does not change
the reduced-ambient quotient class on `C = ⟨x⟩`. -/
lemma galoisPowerClassMk_eq_of_reducedAmbient_power
    (x : G) (c : Subgroup.zpowers x)
    (u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) :
    galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
        (c ^ u : Subgroup.zpowers x) =
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c := by
  -- Unpack the quotient relation using the defining reduced-ambient power action on `C`.
  apply Quotient.sound
  change
    MulAction.orbitRel
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
      (ConjClasses (Subgroup.zpowers x))
      (ConjClasses.mk (c ^ u : Subgroup.zpowers x))
      (ConjClasses.mk c)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨u, ?_⟩
  change ((u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) • ConjClasses.mk c) =
    ConjClasses.mk (c ^ u : Subgroup.zpowers x)
  change
    ConjClasses.pow
      (Representation.galoisPowerExponentUnit
        (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)))
      (ConjClasses.mk c) =
    ConjClasses.mk (c ^ u : Subgroup.zpowers x)
  rw [pow_subgroup_eq_pow_nat]
  exact ConjClasses.pow_mk
    (Representation.galoisPowerExponentUnit
      (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ))) c

/-- Helper for Infra 12 7 CyclicDescent: on the generator branch, the representative-centered
reduced-ambient orbit source is exactly the pullback of the single reduced-ambient quotient class
of `cq`. -/
lemma reducedAmbientOrbitSupportedSource_eq_singleClassPullback
    (x : G) (cq : Subgroup.zpowers x)
    (hcq : Subgroup.zpowers cq = ⊤) :
    reducedAmbient_orbit_supported_source (K := K) (A := A) (G := G) x cq =
      fun c : Subgroup.zpowers x ↦
        if galoisPowerClassMk (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c =
            galoisPowerClassMk (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq
        then (Nat.card (Subgroup.zpowers x) : A)
        else 0 := by
  classical
  ext c
  by_cases hclass :
      galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c =
        galoisPowerClassMk (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq
  · -- Quotient equality gives an explicit reduced-ambient power from the representative `cq`.
    obtain ⟨u, hu⟩ :=
      exists_reducedAmbient_power_of_galoisPowerClass_eq
        (K := K) (G := G) x hclass
    rw [reducedAmbient_orbit_supported_source, if_pos ⟨u, hu⟩, if_pos hclass]
  · have hsupp :
        ¬ ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u := by
      rintro ⟨u, hu⟩
      exact hclass <| by
        simpa [hu] using
          galoisPowerClassMk_eq_of_reducedAmbient_power
            (K := K) (G := G) x cq u
    -- Away from that single quotient class, both descriptions vanish.
    rw [reducedAmbient_orbit_supported_source, if_neg hsupp, if_neg hclass]

/-- Helper for Infra 12 7 CyclicDescent: the pullback of one reduced-ambient quotient class on
`C = ⟨y⟩` depends only on that reduced-ambient quotient class. -/
lemma reducedAmbientSingleClassPullback_isConstantOnReducedAmbientClasses_local
    (y : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers y)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y)) :
    IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y)
      (fun c : Subgroup.zpowers y ↦
        if galoisPowerClassMk (G := Subgroup.zpowers y)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
        then (Nat.card (Subgroup.zpowers y) : A)
        else 0) := by
  classical
  refine ⟨?_⟩
  intro c d hcd
  -- The pullback only tests the quotient-class label, so equal labels give equal values.
  by_cases hc :
      galoisPowerClassMk (G := Subgroup.zpowers y)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
  · have hd :
        galoisPowerClassMk (G := Subgroup.zpowers y)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) d = q := by
      simpa [hcd] using hc
    simp [hc, hd]
  · have hd :
        ¬ galoisPowerClassMk (G := Subgroup.zpowers y)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) d = q := by
      intro hd
      exact hc <| hcd.trans hd
    simp [hc, hd]

/-- Helper for Infra 12 7 CyclicDescent: every value of a single reduced-ambient quotient-class
pullback on `C = ⟨y⟩` lies in the principal ideal generated by `|C|`. -/
lemma reducedAmbientSingleClassPullback_mem_span_card_local
    (y : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers y)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y))
    (c : Subgroup.zpowers y) :
    (if galoisPowerClassMk (G := Subgroup.zpowers y)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
      then (Nat.card (Subgroup.zpowers y) : A)
      else 0) ∈
        Ideal.span ({(Nat.card (Subgroup.zpowers y) : A)} : Set A) := by
  classical
  -- The pullback takes only the values `|C|` and `0`, both inside the principal ideal.
  by_cases hclass :
      galoisPowerClassMk (G := Subgroup.zpowers y)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
  · exact Ideal.subset_span (by simp [hclass])
  · simpa [hclass] using
      (zero_mem (Ideal.span ({(Nat.card (Subgroup.zpowers y) : A)} : Set A)))

/-- Helper for Infra 12 7 CyclicDescent: on the cyclic factor `C = ⟨y⟩`, reduced-ambient
quotient constancy together with pointwise `|C|A`-valuedness is enough to descend into
`A ⊗ R_K(C)`. -/
lemma reducedAmbientPointwiseSpanCardQuotient_local
    (y : G) {f : Subgroup.zpowers y → A}
    (hconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) f)
    (hspan : ∀ c : Subgroup.zpowers y,
      f c ∈ Ideal.span ({(Nat.card (Subgroup.zpowers y) : A)} : Set A)) :
    ∃ g : Subgroup.zpowers y → A,
      (∀ c : Subgroup.zpowers y, f c = (Nat.card (Subgroup.zpowers y) : A) * g c) ∧
      IsConstantOnGaloisPowerClasses
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g := by
  obtain ⟨g, hg⟩ :=
    exists_group_order_pointwise_quotient (G := Subgroup.zpowers y) (A := A) f hspan
  refine ⟨g, hg, ?_⟩
  refine ⟨?_⟩
  intro c d hcd
  -- The quotient function inherits reduced-ambient constancy by canceling the nonzero scalar
  -- `|C|` inside the domain `A`.
  have hcardK : (Nat.card (Subgroup.zpowers y) : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardA : (Nat.card (Subgroup.zpowers y) : A) ≠ 0 := by
    intro hzero
    exact hcardK <| by
      simpa using congrArg (algebraMap A K) hzero
  have hfd : f c = f d := hconst.eq_of_mk_eq hcd
  rw [hg c, hg d] at hfd
  exact mul_left_cancel₀ hcardA hfd

/-- Helper for Infra 12 7 CyclicDescent (Fourier S4): for a reduced-ambient-constant `g`, the
algebraic-closure Fourier coefficient `∑ c, (g c) · (β c)⁻¹` is invariant under twisting `β` by a
`Γ_K`-power.  Proved by reindexing the sum along the bijection `c ↦ c ^ k_t` (which is a bijection
since `k_t` is coprime to `|C|`), absorbing the reindexing into `g` via reduced-ambient constancy. -/
theorem fourierCoeff_linearCharacter_twist_eq
    (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) (t : ΓK) :
    (∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
        (((linearCharacter_twist (G := G) (K := K) (x := y) β t c :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹)
      = ∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹ := by
  classical
  set k : ℕ := galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) with hk
  -- `k` is coprime to `|C| = orderOf y`, so `c ↦ c ^ k` is a bijection of `C = ⟨y⟩`.
  have hcop : (Nat.card (Subgroup.zpowers y)).Coprime k := by
    rw [Nat.card_zpowers]
    exact (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent y)
      (ZMod.val_coe_unit_coprime (t : (ZMod (Monoid.exponent G))ˣ))).symm
  let e : Subgroup.zpowers y ≃ Subgroup.zpowers y := powCoprime hcop
  have he : ∀ c : Subgroup.zpowers y, e c = c ^ k := fun c => rfl
  -- `g` is invariant under `c ↦ c ^ k` because that power is a reduced-ambient action.
  have hgk : ∀ c : Subgroup.zpowers y, g (c ^ k) = g c := by
    intro c
    set u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y :=
      ⟨ZMod.unitsMap (exponent_zpowers_dvd_ambient_local (G := G) y)
          (t : (ZMod (Monoid.exponent G))ˣ),
        Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩⟩ with hu
    have hmod :
        Representation.galoisPowerExponentUnit
            (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers y)))ˣ)) ≡ k
          [MOD Monoid.exponent (Subgroup.zpowers y)] := by
      rw [← ZMod.natCast_eq_natCast_iff, hk]
      calc
        ((Representation.galoisPowerExponentUnit
              (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers y)))ˣ)) : ℕ) :
            ZMod (Monoid.exponent (Subgroup.zpowers y))) =
          (((u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) :
              (ZMod (Monoid.exponent (Subgroup.zpowers y)))ˣ) :
            ZMod (Monoid.exponent (Subgroup.zpowers y))) := by
              simp [Representation.galoisPowerExponentUnit]
        _ = ((((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).cast) :
            ZMod (Monoid.exponent (Subgroup.zpowers y))) := by
              simpa [hu] using
                (ZMod.unitsMap_val (exponent_zpowers_dvd_ambient_local (G := G) y)
                  (t : (ZMod (Monoid.exponent G))ˣ)).symm
        _ = ((Representation.galoisPowerExponentUnit
              (t := (t : (ZMod (Monoid.exponent G))ˣ)) : ℕ) :
            ZMod (Monoid.exponent (Subgroup.zpowers y))) := by
              simp [Representation.galoisPowerExponentUnit]
    have hcu : (c ^ k : Subgroup.zpowers y) = c ^ u := by
      apply Subtype.ext
      rw [Representation.pow_subgroup_eq_pow_nat, SubmonoidClass.coe_pow]
      exact pow_eq_pow_of_modEq hmod.symm
        (Subgroup.pow_exponent_eq_one (H := Subgroup.zpowers y) c.2)
    rw [hcu]
    exact ((isConstantOnGaloisPowerClasses_iff_forall_pow_eq hgconst.isClassFunction).1
      hgconst c u).symm
  -- Reindex the twisted-coefficient sum along `e`.
  rw [← Equiv.sum_comp e (fun c : Subgroup.zpowers y =>
    algebraMap A (AlgebraicClosure K) (g c) * (((β c : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K))⁻¹)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [he, hgk, linearCharacter_twist_apply_local (G := G) (K := K) (x := y) β t c, ← hk, map_pow]

/-- Helper for Infra 12 7 CyclicDescent (Fourier S6 core): the algebraic-closure Fourier
coefficient `∑ c, (g c) · (β c)⁻¹` of a reduced-ambient-constant `g` lies in the image of `A`.
It is integral over `A` (each term is an `A`-image times a root of unity), and it is fixed by
every `K`-automorphism of the closure (the Galois action permutes `β` by a `Γ_K`-twist, under
which the coefficient is invariant), hence lies in `K`; integral closedness pulls it back to `A`. -/
theorem fourierCoeff_mem_range_algebraMap_local
    (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) :
    ∃ a : A, algebraMap A (AlgebraicClosure K) a =
      ∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹ := by
  classical
  letI : CommGroup (Subgroup.zpowers y) :=
    { (inferInstance : Group (Subgroup.zpowers y)) with
      mul_comm := fun a b => by
        apply Subtype.ext
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add, ← zpow_add, add_comm] }
  have hint : IsIntegral A
      (∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) :=
    cyclicFourier_coeff_isIntegral g β
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      σ (∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
          (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) =
        ∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
          (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹ := by
    intro σ
    have hroot : σ (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) ∈
        (minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K))).aroots (AlgebraicClosure K) :=
      (isConjRoot_iff_mem_minpoly_aroots
        (generatorField_generator_isAlgebraic (K := K) (x := y) β).isIntegral).mp
        (isConjRoot_of_algEquiv _ σ)
    obtain ⟨tσ, htσ⟩ :=
      gammaSubgroup_exists_twist_of_generator_root_local (K := K) (x := y) β hroot
    have hσβ : ∀ c : Subgroup.zpowers y,
        σ (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) =
          (((linearCharacter_twist (G := G) (K := K) (x := y) β tσ c :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) := by
      intro c
      rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
      have hc : c = (zpowers_generator (x := y)) ^ n := by
        apply Subtype.ext; simpa using hn.symm
      have hβpow : ((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
          ((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K) ^ n := by
        rw [hc, map_zpow, Units.val_zpow_eq_zpow_val]
      have htpow : ((linearCharacter_twist (G := G) (K := K) (x := y) β tσ c :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
          ((linearCharacter_twist (G := G) (K := K) (x := y) β tσ
            (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ n := by
        rw [hc, map_zpow, Units.val_zpow_eq_zpow_val]
      rw [hβpow, htpow, map_zpow₀, htσ]
    calc
      σ (∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
            (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹)
          = ∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
              (((linearCharacter_twist (G := G) (K := K) (x := y) β tσ c :
                (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹ := by
            rw [map_sum]
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [map_mul, map_inv₀, hσβ c]
            congr 1
            rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), σ.commutes]
      _ = ∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
              (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹ :=
            fourierCoeff_linearCharacter_twist_eq (K := K) (A := A) y hgconst β tσ
  have hmem :
      (∑ c : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) ∈
        (⊥ : IntermediateField K (AlgebraicClosure K)) :=
    (InfiniteGalois.mem_bot_iff_fixed _).mpr hfix
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hmem
  have hwint : IsIntegral A w := by
    have hint' : IsIntegral A (algebraMap K (AlgebraicClosure K) w) := by rw [hw]; exact hint
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K (AlgebraicClosure K))
      (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K))).mp hint'
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hwint
  refine ⟨a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), ha, hw]

/-- Helper for Infra 12 7 CyclicDescent: a linear character of the cyclic group `C = ⟨y⟩` is
determined by its value on the distinguished generator. -/
theorem linearCharacter_zpowers_eq_of_generator_eq_local
    (y : G) (β₁ β₂ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (hgen : β₁ (zpowers_generator (x := y)) = β₂ (zpowers_generator (x := y))) :
    β₁ = β₂ := by
  ext c
  rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
  have hc : c = (zpowers_generator (x := y)) ^ n := by
    apply Subtype.ext; simpa using hn.symm
  rw [hc, map_zpow, map_zpow, hgen]

section
-- Classical `DecidableEq (C →* Ωˣ)` throughout this section, matching the orbit-sum
-- (`CyclicGeneratorFieldOrbitSum`) and Fourier (`CyclicCharacterFourier`) image instances.
attribute [local instance] Classical.propDecidable

-- Part 1: the S5 orbit sum.
theorem block_S5 (y : G) (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (c : Subgroup.zpowers y) :
    (∑ β ∈ Finset.univ.image (fun t : Γ[K](G) =>
        linearCharacter_twist (G := G) (K := K) (x := y) β₀ t),
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) =
    algebraMap (↥K) (AlgebraicClosure K)
      ((generatorField_linearCharacter_representation (K := K) (x := y) β₀).character c) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp c.2
  have hc : c = (zpowers_generator (x := y)) ^ n := by
    apply Subtype.ext; simpa using hn.symm
  rw [hc]
  exact generatorField_character_eq_sum_twistOrbit_on_generator_powers (K := K) (x := y) β₀ n

-- Part 2: factoring out the orbit-constant coefficient (S4).
theorem block_factor (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (c : Subgroup.zpowers y) (a : A)
    (ha : algebraMap A (AlgebraicClosure K) a =
      ∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β₀ c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) :
    (∑ β ∈ Finset.univ.image (fun t : Γ[K](G) =>
        linearCharacter_twist (G := G) (K := K) (x := y) β₀ t),
      (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) =
    algebraMap A (AlgebraicClosure K) a *
      (∑ β ∈ Finset.univ.image (fun t : Γ[K](G) =>
        linearCharacter_twist (G := G) (K := K) (x := y) β₀ t),
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hβ
  rw [← ht, fourierCoeff_linearCharacter_twist_eq (K := K) (A := A) y hgconst β₀ t, ← ha]

-- Combined block.
theorem fourier_orbit_block_local'
    (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (c : Subgroup.zpowers y) (a : A)
    (ha : algebraMap A (AlgebraicClosure K) a =
      ∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β₀ c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) :
    (∑ β ∈ Finset.univ.image (fun t : Γ[K](G) =>
        linearCharacter_twist (G := G) (K := K) (x := y) β₀ t),
      (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) =
    algebraMap A (AlgebraicClosure K) a *
      algebraMap (↥K) (AlgebraicClosure K)
        ((generatorField_linearCharacter_representation (K := K) (x := y) β₀).character c) := by
  rw [block_factor (K := K) y hgconst β₀ c a ha, block_S5 (K := K) y β₀ c]

-- Classical-DecidableEq re-proof of the fiber lemma (so it matches S5/block's image instance).
theorem fiber_minpoly_eq_twistOrbit_local'
    (y : G) (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) :
    Finset.univ.filter (fun β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ =>
        minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) =
          minpoly K (((β₀ (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K))) =
      Finset.univ.image (fun t : Γ[K](G) =>
        linearCharacter_twist (G := G) (K := K) (x := y) β₀ t) := by
  ext β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hmp
    have hroot : ((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K) ∈
        (minpoly K (((β₀ (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K))).aroots (AlgebraicClosure K) := by
      rw [Polynomial.mem_aroots]
      refine ⟨minpoly.ne_zero
        (generatorField_generator_isAlgebraic (K := K) (x := y) β₀).isIntegral, ?_⟩
      rw [← hmp]
      exact minpoly.aeval K _
    obtain ⟨t, ht⟩ :=
      gammaSubgroup_exists_twist_of_generator_root_local (K := K) (x := y) β₀ hroot
    exact ⟨t, linearCharacter_zpowers_eq_of_generator_eq_local (K := K) y
      (linearCharacter_twist (G := G) (K := K) (x := y) β₀ t) β (Units.ext ht)⟩
  · rintro ⟨t, rfl⟩
    exact ((isConjRoot_iff_mem_minpoly_aroots
      (generatorField_generator_isAlgebraic (K := K) (x := y) β₀).isIntegral).mpr
      (gammaSubgroup_generator_value_mem_K_aroots_local (K := K) (x := y) β₀ t)).symm

-- Lemma A: the minpoly-fiber sum descends to A·χ (fiber = twist orbit, then block).
theorem orbit_fiber_descent (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (c : Subgroup.zpowers y) (a : A)
    (ha : algebraMap A (AlgebraicClosure K) a =
      ∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β₀ c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) :
    (∑ β ∈ Finset.univ.filter (fun β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ =>
        minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) =
          minpoly K (((β₀ (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K))),
      (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) =
    algebraMap A (AlgebraicClosure K) a *
      algebraMap (↥K) (AlgebraicClosure K)
        ((generatorField_linearCharacter_representation (K := K) (x := y) β₀).character c) := by
  calc (∑ β ∈ Finset.univ.filter (fun β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ =>
          minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)) =
            minpoly K (((β₀ (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K))),
        (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
          (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)))
      = (∑ β ∈ Finset.univ.image (fun t : Γ[K](G) =>
          linearCharacter_twist (G := G) (K := K) (x := y) β₀ t),
        (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
          (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) :=
        Finset.sum_congr (fiber_minpoly_eq_twistOrbit_local' (K := K) y β₀) (fun _ _ => rfl)
    _ = _ := fourier_orbit_block_local' (K := K) y hgconst β₀ c a ha

-- Per-orbit: the descended contribution `aOf β₀ • χ(β₀)` (applied at c, lifted to Ω) equals the
-- minpoly-fiber sum.  (β₀ is a plain variable, so writing `.character` is cheap here.)
theorem contrib_eq_fiber_sum (y : G) {g : Subgroup.zpowers y → A}
    (hgconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) g)
    (β₀ : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ)
    (c : Subgroup.zpowers y) :
    algebraMap (↥K) (AlgebraicClosure K)
      ((((fourierCoeff_mem_range_algebraMap_local (K := K) (A := A) y hgconst β₀).choose) •
        (generatorField_linearCharacter_representation (K := K) (x := y) β₀).character) c) =
    ∑ β ∈ Finset.univ.filter (fun β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ =>
        minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) =
          minpoly K (((β₀ (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K))),
      (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
        (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) := by
  rw [Pi.smul_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  exact (orbit_fiber_descent (K := K) y hgconst β₀ c _
    (fourierCoeff_mem_range_algebraMap_local (K := K) (A := A) y hgconst β₀).choose_spec).symm

/-- Helper for Infra 12 7 CyclicDescent: on the cyclic factor `C = ⟨y⟩`, reduced-ambient
quotient constancy together with pointwise `|C|A`-valuedness is enough to descend into
`A ⊗ R_K(C)`. -/
lemma reducedAmbientConstancySpanCard_descent_local
    (y : G) {f : Subgroup.zpowers y → A}
    (hconst : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) f)
    (hspan : ∀ c : Subgroup.zpowers y,
      f c ∈ Ideal.span ({(Nat.card (Subgroup.zpowers y) : A)} : Set A)) :
    ((algebraMap A K) ∘ f) ∈
      A ⊗R[K](Subgroup.zpowers y) := by
  classical
  obtain ⟨g, hg, hgconst⟩ :=
    reducedAmbientPointwiseSpanCardQuotient_local
      (K := K) (A := A) (G := G) y hconst hspan
  letI : CommGroup (Subgroup.zpowers y) :=
    { (inferInstance : Group (Subgroup.zpowers y)) with
      mul_comm := fun a b => by
        apply Subtype.ext
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add, ← zpow_add, add_comm] }
  -- The minpoly map whose fibers are the Γ_K-twist orbits.
  set m : (Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) → Polynomial K :=
    fun β => minpoly K (((β (zpowers_generator (x := y)) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K)) with hm_def
  -- For each character, the descended Fourier coefficient in `A` and the K-rational character.
  set aOf : (Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) → A :=
    fun β => (fourierCoeff_mem_range_algebraMap_local (K := K) (A := A) y hgconst β).choose
    with haOf_def
  set contrib : (Subgroup.zpowers y →* (AlgebraicClosure K)ˣ) → (Subgroup.zpowers y → K) :=
    fun β => (aOf β) •
      (generatorField_linearCharacter_representation (K := K) (x := y) β).character
    with hcontrib_def
  -- The descended element: one orbit contribution per minpoly value.
  have heq : ((algebraMap A K) ∘ f) =
      ∑ p ∈ (Finset.univ.image m).attach, contrib ((Finset.mem_image.mp p.2).choose) := by
    funext c
    simp only [Function.comp_apply, Finset.sum_apply]
    apply (algebraMap (↥K) (AlgebraicClosure K)).injective
    rw [map_sum]
    -- LHS chain: ι(alg(f c)) → |C|·alg(g c) → ∑_β coeff → ∑_{p∈image} ∑_{fiber} → ∑_{attach} ∑_{fiber}.
    rw [← IsScalarTower.algebraMap_apply A (↥K) (AlgebraicClosure K) (f c), hg c, map_mul,
      map_natCast, cyclicFourier_inversion (fun c => algebraMap A (AlgebraicClosure K) (g c)) c,
      ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image m) (g := m)
        (fun β _ => Finset.mem_image_of_mem m (Finset.mem_univ β))
        (fun β => (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
            (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
          (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))),
      ← Finset.sum_attach (Finset.univ.image m)
        (fun p => ∑ β ∈ Finset.univ.filter (fun β => m β = p),
          (∑ c' : Subgroup.zpowers y, algebraMap A (AlgebraicClosure K) (g c') *
              (((β c' : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))⁻¹) *
            (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)))]
    -- Per minpoly value: the fiber sum equals the descended contribution.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [hcontrib_def, haOf_def]
    have hp_eq : m ((Finset.mem_image.mp p.2).choose) = ↑p :=
      (Finset.mem_image.mp p.2).choose_spec.2
    have hfilt : Finset.univ.filter
          (fun β : Subgroup.zpowers y →* (AlgebraicClosure K)ˣ => m β = ↑p)
        = Finset.univ.filter (fun β => m β = m ((Finset.mem_image.mp p.2).choose)) := by
      rw [hp_eq]
    rw [hfilt]
    simp only [hm_def]
    exact (contrib_eq_fiber_sum (K := K) y hgconst ((Finset.mem_image.mp p.2).choose) c).symm
  rw [heq]
  refine Submodule.sum_mem _ (fun p _ => ?_)
  exact Submodule.smul_mem _ _
    (generatorFieldCharacter_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) y ((Finset.mem_image.mp p.2).choose))

end

/-- Helper for Infra 12 7 CyclicDescent: a single reduced-ambient quotient-class basis vector on
`C = ⟨y⟩`, scaled by `|C|`, should belong to `A ⊗ R_K(C)`. -/
lemma reducedAmbientSingleClassPullback_mem_characterRingOverFieldAlgebraScalarExtension_local
    (y : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers y)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y)) :
    ((algebraMap A K) ∘
      (fun c : Subgroup.zpowers y ↦
        if galoisPowerClassMk (G := Subgroup.zpowers y)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
        then (Nat.card (Subgroup.zpowers y) : A)
        else 0)) ∈
      A ⊗R[K](Subgroup.zpowers y) := by
  let f : Subgroup.zpowers y → A := fun c : Subgroup.zpowers y ↦
    if galoisPowerClassMk (G := Subgroup.zpowers y)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c = q
    then (Nat.card (Subgroup.zpowers y) : A)
    else 0
  have hconst :
      IsConstantOnGaloisPowerClasses
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) f := by
    -- The single-class pullback is constant on the reduced-ambient quotient by construction.
    simpa [f] using
      reducedAmbientSingleClassPullback_isConstantOnReducedAmbientClasses_local
        (K := K) (A := A) (G := G) y q
  have hspan :
      ∀ c : Subgroup.zpowers y,
        f c ∈ Ideal.span ({(Nat.card (Subgroup.zpowers y) : A)} : Set A) := by
    intro c
    -- Each value is either `|C|` or `0`, so it lies in the principal ideal `|C|A`.
    simpa [f] using
      reducedAmbientSingleClassPullback_mem_span_card_local
        (K := K) (A := A) (G := G) y q c
  -- Route correction: the missing seam is now the cyclic descent theorem specialized to `⟨y⟩`.
  simpa [Function.comp, f] using
    reducedAmbientConstancySpanCard_descent_local
      (K := K) (A := A) (G := G) y hconst hspan

/-- Helper for Infra 12 7 CyclicDescent: after applying `A → K`, each value of the
representative-centered reduced-ambient orbit-supported source still comes from `A`. -/
lemma algebraMap_comp_reducedAmbientOrbitSupportedSource_apply_mem_range
    (x : G) (cq c : Subgroup.zpowers x) :
    ((algebraMap A K) ∘ reducedAmbient_orbit_supported_source K x cq) c ∈
      Set.range (algebraMap A K) := by
  classical
  let supportPredicate : Prop :=
    ∃ a ∈ reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x,
      c = cq ^ Representation.galoisPowerExponentUnit
        (t := (a : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ))
  by_cases hsupp :
      ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u
  · -- On the supported orbit, the value is exactly the image of `|⟨x⟩|`.
    have hsupp' : supportPredicate := by
      rcases hsupp with ⟨u, hu⟩
      refine ⟨u.1, u.2, ?_⟩
      simpa [Representation.pow_subgroup_eq_pow_nat] using hu
    refine ⟨(Nat.card (Subgroup.zpowers x) : A), ?_⟩
    simp [Function.comp, reducedAmbient_orbit_supported_source, supportPredicate, hsupp']
  · -- Away from the orbit, the source is zero before and after applying the scalar map.
    have hsupp' : ¬ supportPredicate := by
      intro hsupp'
      rcases hsupp' with ⟨u, hu_mem, hu⟩
      exact hsupp ⟨⟨u, hu_mem⟩, by simpa [Representation.pow_subgroup_eq_pow_nat] using hu⟩
    refine ⟨0, ?_⟩
    simp [Function.comp, reducedAmbient_orbit_supported_source, supportPredicate, hsupp']

/-- Helper for Infra 12 7 CyclicDescent: if `cq` generates the cyclic factor `C = ⟨x⟩` as an
element of `Subgroup.zpowers x`, then its ambient cyclic subgroup is exactly `C`. -/
lemma ambient_zpowers_eq_of_generator_representative
    (x : G) (cq : Subgroup.zpowers x)
    (hcq : Subgroup.zpowers cq = ⊤) :
    Subgroup.zpowers (cq : G) = Subgroup.zpowers x := by
  apply le_antisymm
  · -- Every ambient power of `cq` stays inside the original cyclic factor `C = ⟨x⟩`.
    exact Subgroup.zpowers_le.2 cq.property
  · intro c hc
    let c' : Subgroup.zpowers x := ⟨c, hc⟩
    -- Because `cq` generates `C` internally, every element of `C` is an ambient power of `cq`.
    have hc'mem : c' ∈ Subgroup.zpowers cq := by
      simpa [hcq] using
        (show c' ∈ (⊤ : Subgroup (Subgroup.zpowers x)) from by simp)
    rcases Subgroup.mem_zpowers_iff.mp hc'mem with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩

/-- Helper for Infra 12 7 CyclicDescent: when a reduced-ambient power on `C = ⟨x⟩` is induced by
an ambient `Γ[K](G)`-exponent, coercing back to `G` gives the same ambient power. -/
lemma zpowers_pow_eq_ambient_gamma_pow_of_gamma
    (x : G) (c : Subgroup.zpowers x)
    (t : ΓK) :
    let u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x :=
      ⟨ZMod.unitsMap (exponent_zpowers_dvd_ambient_local (G := G) x)
          (t : (ZMod (Monoid.exponent G))ˣ),
        Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩⟩
    ((c ^ u : Subgroup.zpowers x) : G) = (c : G) ^ t := by
  let hdiv : Monoid.exponent (Subgroup.zpowers x) ∣ Monoid.exponent G :=
    exponent_zpowers_dvd_ambient_local (G := G) x
  let u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x :=
    ⟨ZMod.unitsMap hdiv (t : (ZMod (Monoid.exponent G))ˣ),
      Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩⟩
  -- Compare the reduced exponent-unit and the ambient exponent-unit modulo `exp(C)`.
  have hmod :
      Representation.galoisPowerExponentUnit
          (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) ≡
        Representation.galoisPowerExponentUnit
          (t := (t : (ZMod (Monoid.exponent G))ˣ))
          [MOD Monoid.exponent (Subgroup.zpowers x)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((Representation.galoisPowerExponentUnit
            (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) : ℕ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) =
        (((u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) :
            (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simp [Representation.galoisPowerExponentUnit]
      _ =
        (((ZMod.unitsMap hdiv (t : (ZMod (Monoid.exponent G))ˣ)) :
            (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            rfl
      _ =
        ((((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).cast) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simpa using (ZMod.unitsMap_val hdiv (t : (ZMod (Monoid.exponent G))ˣ)).symm
      _ =
        ((Representation.galoisPowerExponentUnit
            (t := (t : (ZMod (Monoid.exponent G))ˣ)) : ℕ) :
          ZMod (Monoid.exponent (Subgroup.zpowers x))) := by
            simp [Representation.galoisPowerExponentUnit]
  -- Once both exponents agree modulo `exp(C)`, the cyclic power actions agree on `C`.
  simpa [u, Representation.pow_subgroup_eq_pow_nat] using
    (pow_eq_pow_of_modEq hmod (Subgroup.pow_exponent_eq_one (H := Subgroup.zpowers x) c.2) :
      (c : G) ^
          Representation.galoisPowerExponentUnit
            (t := (u : (ZMod (Monoid.exponent (Subgroup.zpowers x)))ˣ)) =
        (c : G) ^
          Representation.galoisPowerExponentUnit
            (t := (t : (ZMod (Monoid.exponent G))ˣ)))

/-- Helper for Infra 12 7 CyclicDescent: the reduced-ambient orbit-supported source on
`C = ⟨x⟩` is the same source obtained by ranging over ordinary ambient `Γ[K](G)`-powers of the
chosen representative `cq`. -/
lemma reducedAmbientOrbitSupportedSource_eq_ambientGammaOrbitIndicator
    (x : G) (cq : Subgroup.zpowers x) :
    reducedAmbient_orbit_supported_source (K := K) (A := A) (G := G) x cq =
      (by
        classical
        exact fun c : Subgroup.zpowers x ↦
          if ∃ t : ΓK, (c : G) = (cq : G) ^ t
          then (Nat.card (Subgroup.zpowers x) : A)
          else 0) := by
  classical
  ext c
  have hsupp_iff :
      (∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u) ↔
        ∃ t : ΓK, (c : G) = (cq : G) ^ t := by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨t, ht⟩ :=
        zpowers_pow_eq_ambient_gamma_pow_of_mem_reducedAmbient_local
          (K := K) (G := G) x cq u
      -- A reduced-ambient support witness is realized by an actual ambient `Γ[K](G)`-power.
      exact ⟨t, by simpa [hu] using ht⟩
    · rintro ⟨t, ht⟩
      let u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x :=
        ⟨ZMod.unitsMap (exponent_zpowers_dvd_ambient_local (G := G) x)
            (t : (ZMod (Monoid.exponent G))ˣ),
          Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩⟩
      refine ⟨u, ?_⟩
      apply Subtype.ext
      have hu :
          ((cq ^ u : Subgroup.zpowers x) : G) = (cq : G) ^ t := by
        simpa [u] using
          zpowers_pow_eq_ambient_gamma_pow_of_gamma
            (K := K) (G := G) x cq t
      -- The mapped ambient exponent recovers the same cyclic source point.
      exact ht.trans hu.symm
  -- Rewrite the source support predicate through the ambient `Γ[K](G)`-orbit description.
  by_cases hsupp : ∃ u : reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x, c = cq ^ u
  · rw [reducedAmbient_orbit_supported_source, if_pos hsupp]
    rw [if_pos (hsupp_iff.mp hsupp)]
  · rw [reducedAmbient_orbit_supported_source, if_neg hsupp]
    rw [if_neg (mt hsupp_iff.mpr hsupp)]

/-- Helper for Infra 12 7 CyclicDescent: the ambient `Γ[K](G)`-orbit projector on the cyclic
subgroup `C = ⟨y⟩`, written before applying the scalar-extension map `A → K`. -/
def ambientGammaOrbitProjectorSource
    (y : G) :
    Subgroup.zpowers y → A :=
  open Classical in
    fun c ↦ if ∃ t : ΓK, (c : G) = y ^ t then (Nat.card (Subgroup.zpowers y) : A) else 0

/-- Helper for Infra 12 7 CyclicDescent: the ambient `Γ[K](G)`-orbit projector on `C = ⟨y⟩`
is the reduced-ambient single-class pullback at the canonical generator class. -/
lemma ambientGammaOrbitProjectorSource_eq_reducedAmbientSingleClassPullback_local
    (y : G) :
    ambientGammaOrbitProjectorSource (K := K) (A := A) (G := G) y =
      fun c : Subgroup.zpowers y ↦
        if galoisPowerClassMk (G := Subgroup.zpowers y)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c =
            galoisPowerClassMk (G := Subgroup.zpowers y)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y)
              (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y)
        then (Nat.card (Subgroup.zpowers y) : A)
        else 0 := by
  let cq : Subgroup.zpowers y := ⟨y, Subgroup.mem_zpowers y⟩
  have hcq : Subgroup.zpowers cq = ⊤ := by
    exact (subgroup_zpowers_eq_top_iff (Subgroup.zpowers y) cq).2 rfl
  -- Route correction: normalize the ambient projector through the existing reduced-ambient
  -- orbit-source rewrites so the missing owner statement is a single quotient-class basis vector.
  calc
    ambientGammaOrbitProjectorSource (K := K) (A := A) (G := G) y =
        reducedAmbient_orbit_supported_source (K := K) (A := A) (G := G) y cq := by
          symm
          rw [reducedAmbientOrbitSupportedSource_eq_ambientGammaOrbitIndicator
            (K := K) (A := A) (G := G) y cq]
          rfl
    _ =
        fun c : Subgroup.zpowers y ↦
          if galoisPowerClassMk (G := Subgroup.zpowers y)
                (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) c =
              galoisPowerClassMk (G := Subgroup.zpowers y)
                (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) cq
          then (Nat.card (Subgroup.zpowers y) : A)
          else 0 := by
            exact
              reducedAmbientOrbitSupportedSource_eq_singleClassPullback
                (K := K) (A := A) (G := G) y cq hcq

/-- Helper for Infra 12 7 CyclicDescent: the ambient `Γ[K](G)`-orbit projector on the cyclic
subgroup `C = ⟨y⟩` should already lie in `A ⊗ R_K(C)`. -/
lemma ambientGammaOrbitProjector_mem_characterRingOverFieldAlgebraScalarExtension_local
    (y : G) :
    ((algebraMap A K) ∘ ambientGammaOrbitProjectorSource (K := K) (A := A) (G := G) y) ∈
      A ⊗R[K](Subgroup.zpowers y) := by
  let cq : Subgroup.zpowers y := ⟨y, Subgroup.mem_zpowers y⟩
  -- Rewrite the ambient projector to the reduced-ambient single-class basis vector and close with
  -- the isolated single-class owner theorem.
  rw [ambientGammaOrbitProjectorSource_eq_reducedAmbientSingleClassPullback_local
    (K := K) (A := A) (G := G) y]
  simpa [Function.comp, cq] using
    reducedAmbientSingleClassPullback_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) (G := G) y
      (galoisPowerClassMk (G := Subgroup.zpowers y)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) y) cq)

/-- Helper for Infra 12 7 CyclicDescent: the representative-centered reduced-ambient orbit source
on `C = ⟨x⟩` should lie in `A ⊗ R_K(C)` on the generator branch; the remaining step is the
theorem-local cyclic descent from reduced-ambient quotient constancy and `|C|A`-valued source
control. -/
lemma reducedAmbientOrbitSupportedSource_mem_characterRingOverFieldAlgebraScalarExtension
    (x : G) (cq : Subgroup.zpowers x)
    (hcq : Subgroup.zpowers cq = ⊤) :
    ((algebraMap A K) ∘ reducedAmbient_orbit_supported_source K x cq) ∈
      A ⊗R[K](Subgroup.zpowers x) := by
  -- Route correction: on the generator branch, the source is already the reduced-ambient
  -- single-class pullback, so the only remaining blocker is that single quotient basis vector.
  rw [reducedAmbientOrbitSupportedSource_eq_singleClassPullback
    (K := K) (A := A) (G := G) x cq hcq]
  simpa [Function.comp] using
    reducedAmbientSingleClassPullback_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) (G := G) x
      (galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) cq)

/-- Helper for Infra 12 7 CyclicDescent: Serre's denominator-cleared cyclic source on
`C = ⟨x⟩` decomposes as the finite sum of reduced-ambient quotient-class indicators weighted by
the descended quotient values of `g`. -/
lemma cyclic_theta_quotient_source_eq_sum_reducedAmbient_class_indicators
    (x : G) {g : G → A}
    (hgrestrict : IsConstantOnGaloisPowerClasses
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
      (fun c : Subgroup.zpowers x ↦ g c)) :
    cyclic_theta_quotient_source (A := A) x g =
      ∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
          (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
        (hgrestrict.lift q) •
          reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q := by
  classical
  ext c
  have hsum_eval :
      ((∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          (hgrestrict.lift q) •
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q) c) =
        ∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          hgrestrict.lift q *
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q c := by
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hsum_eval]
  by_cases hc : Subgroup.zpowers c = ⊤
  · let q0 : GaloisPowerClass (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) :=
      galoisPowerClassMk (G := Subgroup.zpowers x)
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c
    have hsum :
        (∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          hgrestrict.lift q *
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q c) =
          hgrestrict.lift q0 *
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q0 c := by
      rw [Finset.sum_eq_single q0]
      · intro q _ hq
        have hfalse :
            ¬ (Subgroup.zpowers c = ⊤ ∧
                galoisPowerClassMk (G := Subgroup.zpowers x)
                  (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q) := by
          intro hpair
          exact hq (by simpa [q0] using hpair.2.symm)
        simp [reducedAmbient_class_indicator_source, hfalse]
      · intro hq0
        exact False.elim (hq0 (Finset.mem_univ q0))
    -- Route correction: the source is organized by quotient classes of reduced-ambient powers,
    -- so exactly the class of the current generator contributes to the sum.
    calc
      cyclic_theta_quotient_source (A := A) x g c = (Nat.card (Subgroup.zpowers x) : A) * g c := by
        simp [cyclic_theta_quotient_source, hc]
      _ = g c * (Nat.card (Subgroup.zpowers x) : A) := by rw [mul_comm]
      _ =
          hgrestrict.lift q0 *
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q0 c := by
          simp [q0, reducedAmbient_class_indicator_source, hc]
      _ =
          ∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
              (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
            hgrestrict.lift q *
              reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q c := by
          exact hsum.symm
  · have hsum :
        (∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          hgrestrict.lift q *
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q c) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro q _
      have hfalse :
          ¬ (Subgroup.zpowers c = ⊤ ∧
              galoisPowerClassMk (G := Subgroup.zpowers x)
                (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) c = q) := by
        intro hpair
        exact hc hpair.1
      simp [reducedAmbient_class_indicator_source, hfalse]
    -- Away from generators, both the cyclic source and every class indicator vanish.
    simp [cyclic_theta_quotient_source, hc, hsum]

/-- Helper for Infra 12 7 CyclicDescent: each reduced-ambient quotient-class indicator on
`C = ⟨x⟩` belongs to the scalar-extended owner once the generator branch is reduced to the
representative-centered orbit-supported source. -/
lemma reducedAmbient_class_indicator_mem_characterRingOverFieldAlgebraScalarExtension
    (x : G)
    (q : GaloisPowerClass (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)) :
    ((algebraMap A K) ∘
      reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q) ∈
        A ⊗R[K](Subgroup.zpowers x) := by
  classical
  obtain ⟨cq, hcq⟩ :=
    galoisPowerClassMk_surjective
      (G := Subgroup.zpowers x)
      (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x) q
  by_cases hgen : Subgroup.zpowers cq = ⊤
  · have hsource_eq :
        ((algebraMap A K) ∘
          reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q) =
          ((algebraMap A K) ∘ reducedAmbient_orbit_supported_source K x cq) := by
      -- Route correction: the quotient-class indicator is already identified with the single
      -- representative-centered orbit-supported source on the generator branch.
      simpa [Function.comp] using
        congrArg (fun f : Subgroup.zpowers x → A ↦ (algebraMap A K) ∘ f)
          (reducedAmbient_class_indicator_source_eq_orbit_supported_of_generator_representative
            (K := K) (A := A) (G := G) x q cq hcq hgen)
    have horbit_mem :
        ((algebraMap A K) ∘ reducedAmbient_orbit_supported_source K x cq) ∈
          A ⊗R[K](Subgroup.zpowers x) := by
      -- The remaining owner-membership statement is now isolated as a single theorem-local
      -- reduced-ambient orbit-source lemma.
      exact
        reducedAmbientOrbitSupportedSource_mem_characterRingOverFieldAlgebraScalarExtension
          (K := K) (A := A) (G := G) x cq hgen
    simpa [hsource_eq] using horbit_mem
  · have hzero :
        reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q = 0 :=
      reducedAmbient_class_indicator_source_eq_zero_of_not_generator_representative
        (K := K) (A := A) (G := G) x q cq hcq hgen
    -- On the nongenerator branch, the class indicator is zero, so it is trivially in the owner.
    simpa [hzero] using (zero_mem (A ⊗R[K](Subgroup.zpowers x)))

/-- Helper for Infra 12 7 CyclicDescent: the denominator-cleared cyclic `θ`-summand attached to a
cyclic subgroup belongs to the corresponding scalar-extended character ring. -/
lemma cyclic_theta_mul_quotient_mem_characterRingOverFieldAlgebraScalarExtension
    (H : CycSub) {g : G → A}
    (hg : IsConstantOnGaloisPowerClasses (Γ[K](G)) g) :
    (fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * algebraMap A K (g h)) ∈ A ⊗R[K](H.1) := by
  rcases H with ⟨H, hHcyc⟩
  have hrange :
      ∀ h : H,
        ((θ[H] : H → K) h * algebraMap A K (g h)) ∈
          Set.range (algebraMap A K) :=
    cyclic_theta_mul_quotient_apply_mem_range
      (K := K) (A := A) (G := G) ⟨H, hHcyc⟩
  obtain ⟨x, hxH⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 hHcyc
  have hsource_const :
      IsConstantOnGaloisPowerClasses
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
        (cyclic_theta_quotient_source (A := A) x g) :=
    cyclic_theta_quotient_source_isConstantOnReducedAmbientClasses
      (K := K) (A := A) (G := G) x hg
  have hsource_eq :
      (fun c : Subgroup.zpowers x ↦
        (θ[Subgroup.zpowers x] : Subgroup.zpowers x → K) c * algebraMap A K (g c)) =
          (algebraMap A K) ∘ cyclic_theta_quotient_source (A := A) x g :=
    cyclic_theta_mul_quotient_eq_algebraMap_cyclic_theta_quotient_source
      (K := K) (A := A) (G := G) x
  have hgrestrict :
      IsConstantOnGaloisPowerClasses
        (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x)
        (fun c : Subgroup.zpowers x ↦ g c) :=
    ambient_restriction_isConstantOnReducedAmbientClasses
      (K := K) (A := A) (G := G) x hg
  have hsource_decomp :
      cyclic_theta_quotient_source (A := A) x g =
        ∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          (hgrestrict.lift q) •
            reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q :=
    cyclic_theta_quotient_source_eq_sum_reducedAmbient_class_indicators
      (K := K) (A := A) (G := G) x hgrestrict
  -- TODO for Infra 12 7 CyclicDescent: after transporting along `hxH : Subgroup.zpowers x = H.1`,
  -- use `reducedAmbient_class_indicator_source_eq_zero_of_not_generator_representative` and
  -- `reducedAmbient_class_indicator_source_eq_orbit_supported_of_generator_representative` to
  -- replace each quotient-class indicator by either `0` or a representative-centered reduced-
  -- ambient orbit-supported source, prove that orbit-supported source lies in
  -- `A ⊗R[K](Subgroup.zpowers x)`, and then close with `Submodule.sum_mem` and
  -- `Submodule.smul_mem`.
  -- Route correction: the quotient-class decomposition and the representative rewrite are closed;
  -- the only remaining frontier is the owner-membership theorem for the reduced-ambient orbit-
  -- supported source on `⟨x⟩`.
  have _ := hrange
  have _ := hsource_const
  have hsourceK_decomp :
      ((algebraMap A K) ∘ cyclic_theta_quotient_source (A := A) x g) =
        ∑ q : GaloisPowerClass (G := Subgroup.zpowers x)
            (reducedAmbientGammaSubgroupOnZpowers (K := K) (G := G) x),
          (hgrestrict.lift q) •
            (((algebraMap A K) ∘
              reducedAmbient_class_indicator_source (K := K) (A := A) (G := G) x q) :
                Subgroup.zpowers x → K) := by
    -- Push the algebra map through the finite quotient-class decomposition pointwise.
    ext c
    simp [hsource_decomp, Pi.smul_apply, Algebra.smul_def, map_mul]
  have hsource_mem :
      ((algebraMap A K) ∘ cyclic_theta_quotient_source (A := A) x g) ∈
        A ⊗R[K](Subgroup.zpowers x) := by
    rw [hsourceK_decomp]
    refine Submodule.sum_mem _ ?_
    intro q hq
    -- Each quotient-class summand already lies in the owner.
    exact
      Submodule.smul_mem
        (A ⊗R[K](Subgroup.zpowers x))
        (hgrestrict.lift q)
        (reducedAmbient_class_indicator_mem_characterRingOverFieldAlgebraScalarExtension
          (K := K) (A := A) (G := G) x q)
  have htheta_mem :
      (fun c : Subgroup.zpowers x ↦
        (θ[Subgroup.zpowers x] : Subgroup.zpowers x → K) c * algebraMap A K (g c)) ∈
          A ⊗R[K](Subgroup.zpowers x) := by
    -- First rewrite the explicit cyclic source back to the original `θ`-weighted summand.
    simpa [hsource_eq] using hsource_mem
  -- Then substitute the identified cyclic subgroup so the target has the same carrier.
  subst H
  simpa using htheta_mem

/-- Helper for Infra 12 7 CyclicDescent: once the pointwise quotient `g` is fixed, Artin's cyclic
sum identity produces a direct-sum preimage of `(algebraMap A K) ∘ f`. -/
lemma exists_cyclicSubgroupInduction_preimage_of_principal_values
    (f : G → A) {g : G → A}
    (hfg : ∀ s : G, f s = (Nat.card G : A) * g s)
    (hg : IsConstantOnGaloisPowerClasses (Γ[K](G)) g) :
    (algebraMap A K) ∘ f ∈
      LinearMap.range ((A ⊗R[K](G)).subtype.comp
        (DFinsupp.lsum A fun H : CycSub ↦
          H.1.characterRingOverFieldAlgebraScalarExtensionInduction)) := by
  classical
  let gK : G → K := (algebraMap A K) ∘ g
  have hgK : IsConstantOnGaloisPowerClasses (Γ[K](G)) gK :=
    algebraMap_comp_isConstantOnGaloisPowerClasses (K := K) hg
  let χ : (H : CycSub) → A ⊗R[K](H.1) := fun H ↦
    ⟨fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * gK h,
      cyclic_theta_mul_quotient_mem_characterRingOverFieldAlgebraScalarExtension
        (K := K) (A := A) (G := G) H hg⟩
  let ξ : Π₀ H : CycSub, A ⊗R[K](H.1) := ∑ H : CycSub, DFinsupp.single H (χ H)
  refine ⟨ξ, ?_⟩
  ext s
  have hsK :
      (((A ⊗R[K](G)).subtype.comp
          (DFinsupp.lsum A fun H : CycSub ↦
            H.1.characterRingOverFieldAlgebraScalarExtensionInduction)) ξ) s =
        ((algebraMap A K) ∘ f) s := by
    -- Evaluate the explicit finite direct sum summand-by-summand.
    -- Route correction: evaluate the finite direct sum summand-by-summand, then apply Artin's
    -- identity `∑ Ind θ_H = |G| • 1` against the quotient function `gK`.
    calc
      (((A ⊗R[K](G)).subtype.comp
          (DFinsupp.lsum A fun H : CycSub ↦
            H.1.characterRingOverFieldAlgebraScalarExtensionInduction)) ξ) s
          = (((∑ H : CycSub, H.1.characterRingOverFieldAlgebraScalarExtensionInduction (χ H) :
            A ⊗R[K](G)) : A ⊗R[K](G)) : G → K) s := by
            rw [LinearMap.comp_apply]
            dsimp [ξ]
            rw [map_sum]
            simp [explicit_cyclicSubgroupInduction_single_overAlgebra]
      _ = (∑ H : CycSub, Ind[H.1]((χ H : H.1 → K)) s) := by
            simp
      _ = (∑ H : CycSub,
            (Ind[H.1](fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * gK h)) s) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            simp [χ, gK]
      _ = (∑ H : CycSub, (Ind[H.1]((θ[H.1] : H.1 → K)) * gK) s) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            rw [induced_mul_eq_induced_mul_restrict_of_isClassFunction
              (K := K) (G := G) H.1 (θ[H.1] : H.1 → K) hgK.isClassFunction]
      _ = (((∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K))) * gK) s) := by
            simp [Pi.mul_apply, Finset.sum_mul]
      _ = ((((Nat.card G : K) • (1 : G → K)) * gK) s) := by
            have htheta_sum :
                ∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K)) =
                  (Nat.card G : K) • (1 : G → K) :=
              cyclicSubgroup_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one_local
                (K := K) (G := G)
            simpa [Pi.mul_apply] using congrArg (fun z : G → K ↦ (z * gK) s) htheta_sum
      _ = ((algebraMap A K) ∘ f) s := by
            have hs :
                algebraMap A K (f s) = (Nat.card G : K) * algebraMap A K (g s) := by
              simpa [map_mul] using congrArg (algebraMap A K) (hfg s)
            simpa [gK, Function.comp, Pi.smul_apply, Pi.mul_apply, Algebra.smul_def] using hs.symm
  exact congrArg ((↑) : K → L) hsK

/-- Infra 12 7 CyclicDescent: Serre's denominator-clearing cyclic-descent step packages the
ambient class function `(algebraMap A K) ∘ f` as lying in the range of the total induction map
from cyclic subgroups. -/
theorem cyclicSubgroupInduction_descent_of_principal_values
    (f : G → A)
    (hf : IsConstantOnGaloisPowerClasses (Γ[K](G)) f)
    (hfg : ∀ s : G, f s ∈ Ideal.span ({(Nat.card G : A)} : Set A)) :
    (algebraMap A K) ∘ f ∈
      LinearMap.range ((A ⊗R[K](G)).subtype.comp
        (DFinsupp.lsum A fun H : { H : Subgroup G // IsCyclic H } ↦
          H.1.characterRingOverFieldAlgebraScalarExtensionInduction)) := by
  obtain ⟨g, hg⟩ :=
    exists_group_order_pointwise_quotient (G := G) (A := A) f hfg
  have hgconst :
      IsConstantOnGaloisPowerClasses (Γ[K](G)) g :=
    group_order_pointwise_quotient_isConstantOnGaloisPowerClasses
      (K := K) (G := G) (A := A) hf hg
  -- Once the quotient `g` is fixed, the only remaining work is the Artin cyclic-sum calculation.
  exact
    exists_cyclicSubgroupInduction_preimage_of_principal_values
      (K := K) (G := G) (A := A) f hg hgconst

end

end Representation
