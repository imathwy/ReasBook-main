import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GaloisPowerAction
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GammaSubgroupAction
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_5_1

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

local notation "CycSub" => { H : Subgroup G // IsCyclic H }
local notation "ΓK" => Γ[K](G)

local instance : Fintype CycSub := Fintype.ofFinite CycSub
local instance : DecidableEq { H : Subgroup G // IsCyclic H } := Classical.decEq _

/-- Helper for Infra 12 7 CyclicDescent: pointwise membership in the principal ideal `|G|A`
produces a global quotient function by `|G|`. -/
lemma exists_group_order_pointwise_quotient
    (f : G → A)
    (hfg : ∀ s : G, f s ∈ Ideal.span ({(Nat.card G : A)} : Set A)) :
    ∃ g : G → A, ∀ s : G, f s = (Nat.card G : A) * g s := by
  classical
  -- Rewrite the pointwise principal-ideal hypothesis as explicit divisibility by `|G|`.
  let g : G → A := fun s ↦
    Classical.choose (by simpa [Ideal.mem_span_singleton] using hfg s)
  refine ⟨g, ?_⟩
  intro s
  exact Classical.choose_spec (by simpa [Ideal.mem_span_singleton] using hfg s)

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
  -- Route correction: keep LinearRepresentations_Serre_1977's source on `⟨x⟩` and compare reduced ambient powers with actual
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
    cyclicSubgroupInduction (A := A) K G (DFinsupp.single H χ) =
      H.1.characterRingOverFieldAlgebraScalarExtensionInduction χ := by
  classical
  -- This is the defining `DFinsupp.single` evaluation rule for the direct-sum induction map.
  rw [cyclicSubgroupInduction, DFinsupp.lsum]
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

/-- Helper for Infra 12 7 CyclicDescent: LinearRepresentations_Serre_1977's cyclic-subgroup `θ`-identity rewritten using the
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

/-- Helper for Infra 12 7 CyclicDescent: LinearRepresentations_Serre_1977's denominator-cleared cyclic source on
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
      -- TODO for Infra 12 7 CyclicDescent: normalize the representative-centered source to the
      -- canonical cyclic orbit-supported source on `Subgroup.zpowers (cq : G)`, prove that
      -- canonical source belongs to `A ⊗R[K](Subgroup.zpowers (cq : G))`, and transport the
      -- result back along the generator equality `Subgroup.zpowers (cq : G) = Subgroup.zpowers x`.
      sorry
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

/-- Infra 12 7 CyclicDescent: LinearRepresentations_Serre_1977's denominator-clearing cyclic-descent step packages the
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
