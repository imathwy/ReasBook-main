import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_120_18
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3
import StacksProject_2024.stacks_project.Chap15.Example_15_40_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_5
import StacksProject_2024.stacks_project.Chap15.Remark_15_115_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open RingHom
open scoped TensorProduct

universe u v w x y

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

/- Domain-style sampling:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with formal smoothness on the localized branches;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `RingHom.formally_smooth_for_adic_baseChange`,
  `Localization.localRingHom`;
- best owner abstraction: the canonical owner is the reduced tensor-product integral closure
  `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, while the localized branch map
  `(A₁)_m → (B₁)_n` is the source-facing object of the statement.
-/

/-- Helper for Lemma 15.115.3: maximality of an ideal is preserved under a ring equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Map maximality through the surjective equivalence map.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le (f := e.toRingHom) e.surjective ?_
  simpa using (show (⊥ : Ideal R) ≤ q from bot_le)

/-- Helper for Lemma 15.115.3: a ring equivalence between local rings carries the maximal ideal of
the source to the maximal ideal of the target. -/
private theorem ringEquiv_map_maximalIdeal_eq
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    Ideal.map e.toRingHom (maximalIdeal R) = maximalIdeal S := by
  -- The image of the source maximal ideal is maximal, and a local ring has only one such ideal.
  exact IsLocalRing.eq_maximalIdeal <|
    ideal_map_isMaximal_of_ringEquiv e (maximalIdeal R)

/-- Helper for Lemma 15.115.3: formal smoothness of the source DVR extension forces separability
of the residue-field extension. -/
private theorem source_residueField_isSeparable
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
  -- Unpack Lemma `15.112.5` once and keep only the residue-field separability factor.
  exact
    (formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField
      (A := A) (B := B)).mp hfs |>.2

/-- Helper for Lemma 15.115.3: formal smoothness of the source DVR extension forces weak
unramifiedness. -/
private theorem source_weaklyUnramified
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    WeaklyUnramified A B := by
  -- The same criterion also records the maximal-ideal equality packaged as weak ramification.
  exact
    (formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField
      (A := A) (B := B)).mp hfs |>.1

/-- Helper for Lemma 15.115.3: for a finite extension of the fraction field of a discrete
valuation ring, the integral closure is not a field. -/
private theorem integralClosure_not_isField_of_fractionField_extension
    [FiniteDimensional K K1] :
    ¬ IsField A1 := by
  -- An integral field extension of a DVR would force the source DVR itself to be a field.
  let _ : Algebra.IsIntegral A A1 := IsIntegralClosure.isIntegral_algebra A K1
  have hinj : Function.Injective (algebraMap A A1) := by
    exact algebraMap_injective_of_field_isFractionRing
      (R := A) (S := A1) (K := K) (L := K1)
  intro hA1
  exact IsDiscreteValuationRing.not_isField A <|
    isField_of_isIntegral_of_isField hinj hA1

omit [IsDiscreteValuationRing A] in
/-- Helper for Lemma 15.115.3: finite-dimensionality over the chosen fraction field `K`
transports to finite generation over the canonical fraction ring `FractionRing A`. -/
private theorem fractionRing_transport_moduleFinite
    [FaithfulSMul A K1] [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
    [FiniteDimensional K K1] :
    Module.Finite (FractionRing A) K1 := by
  -- Compare the chosen fraction field `K` with `FractionRing A` and transport finiteness.
  let e₁ : K ≃+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv
  let e₂ : K1 ≃+* K1 := RingEquiv.refl _
  letI : Module.Finite K K1 := inferInstance
  let f : K1 ≃ₐ[A] K1 := AlgEquiv.refl
  have he :
      RingHom.comp (algebraMap (FractionRing A) K1) ↑e₁ =
        RingHom.comp ↑e₂ (algebraMap K K1) := by
    -- The transported scalar action agrees with the original one through the fraction-field
    -- equivalence.
    ext x
    simpa [e₁, e₂] using
      IsFractionRing.algEquiv_commutes ((FractionRing.algEquiv A K).symm) f x
  exact Module.Finite.of_equiv_equiv e₁ e₂ he

/-- Helper for Lemma 15.115.3: after transporting the fraction-field action to `FractionRing A`,
the integral closure `A₁` is a Dedekind domain. -/
private theorem integralClosure_isDedekindDomain_of_fractionField_extension
    [FiniteDimensional K K1] :
    IsDedekindDomain A1 := by
  -- First move to the canonical fraction field of `A`, then invoke the standard Dedekind-owner
  -- theorem for one-dimensional normal domains.
  let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
  let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
  let _ : IsScalarTower A (FractionRing A) K1 := FractionRing.isScalarTower_liftAlgebra A K1
  let _ : Module.Finite (FractionRing A) K1 :=
    fractionRing_transport_moduleFinite (A := A) (K := K) (K1 := K1)
  let _ : IsFractionRing A1 K1 := integralClosure.isFractionRing_of_finite_extension K K1
  exact integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (A := A) (L := K1)
    (hdim := IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_isField A))

/-- Helper for Lemma 15.115.3: every maximal localization of the finite integral closure `A₁`
is a discrete valuation ring. -/
private theorem integralClosure_localizationAtMaximal_isDiscreteValuationRing_of_fractionField_extension
    [FiniteDimensional K K1] (p : Ideal A1) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  -- Recover the Dedekind-domain owner on `A₁`, then localize at the chosen nonzero maximal ideal.
  let _ : IsDedekindDomain A1 :=
    integralClosure_isDedekindDomain_of_fractionField_extension (A := A) (K := K) (K1 := K1)
  have hcomap : Ideal.comap (algebraMap A A1) p = maximalIdeal A := by
    -- Integrality contracts any maximal ideal of `A₁` to the unique maximal ideal of the DVR `A`.
    let _ : Algebra.IsIntegral A A1 := IsIntegralClosure.isIntegral_algebra A K1
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)
  have hp : p ≠ ⊥ := by
    -- A zero maximal ideal would contract to zero, contradicting that a DVR is not a field.
    intro hbot
    have : maximalIdeal A = ⊥ := by
      calc
        maximalIdeal A = Ideal.comap (algebraMap A A1) p := hcomap.symm
        _ = ⊥ := by
          ext x
          rw [hbot]
          constructor
          · intro hx
            have hx0 : algebraMap A A1 x = algebraMap A A1 0 := by
              simpa using (show algebraMap A A1 x = 0 from hx)
            exact (algebraMap_injective_of_field_isFractionRing A A1 K K1) hx0
          · intro hx
            simpa using congrArg (algebraMap A A1) hx
    exact IsDiscreteValuationRing.not_a_field A this
  simpa using
    (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A1 hp
      (Localization.AtPrime p))

/-- Helper for Lemma 15.115.3: under formal smoothness, the canonical tensor comparison
`A₁ ⊗[A] B → B₁` should be an `A₁`-algebra equivalence. -/
private noncomputable def tensor_base_change_comparison_equiv_of_formally_smooth
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    A1 ⊗[A] B ≃ₐ[A1] B1 := sorry

/-- Helper for Lemma 15.115.3: the tensor comparison equivalence respects the canonical
`A₁`-algebra maps. -/
private theorem tensor_base_change_comparison_comp_algebraMap
    (e : A1 ⊗[A] B ≃ₐ[A1] B1)
    :
    e.toRingHom.comp (algebraMap A1 (A1 ⊗[A] B)) = algebraMap A1 B1 := by
  -- Evaluate the algebra-compatibility relation of the comparison equivalence elementwise.
  ext x
  simpa using (e.commutes x)

/-- Helper for Lemma 15.115.3: pulling a maximal branch ideal of `B₁` back across the tensor
comparison equivalence gives a maximal ideal on the tensor side. -/
private theorem tensor_branch_comap_isMaximal_of_equiv
    (e : A1 ⊗[A] B ≃ₐ[A1] B1)
    (n : Ideal B1) [n.IsMaximal] :
    (Ideal.comap e.toRingHom n).IsMaximal := by
  -- Contract maximality along the surjective ring equivalence.
  exact Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective (K := n)

/-- Helper for Lemma 15.115.3: pulling a branch ideal of `B₁` back across the tensor comparison
equivalence preserves the lies-over relation to `A₁`. -/
private theorem tensor_branch_comap_liesOver_of_equiv
    (e : A1 ⊗[A] B ≃ₐ[A1] B1)
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] :
    (Ideal.comap e.toRingHom n).LiesOver m := by
  -- Compare contractions through the comparison equivalence and reuse `n.over_def m`.
  rw [Ideal.liesOver_iff]
  ext x
  change x ∈ m ↔ e.toRingHom (algebraMap A1 (A1 ⊗[A] B) x) ∈ n
  have hcomp_eq :
      e.toRingHom (algebraMap A1 (A1 ⊗[A] B) x) = algebraMap A1 B1 x := by
    simpa using congrArg (fun f : A1 →+* B1 ↦ f x)
      (tensor_base_change_comparison_comp_algebraMap (e := e))
  have hcomp_mem :
      algebraMap A1 B1 x ∈ n ↔
        e.toRingHom (algebraMap A1 (A1 ⊗[A] B) x) ∈ n := by
    rw [hcomp_eq]
  have hunder_mem :
      x ∈ m ↔ algebraMap A1 B1 x ∈ n := by
    simpa [Ideal.under, Ideal.mem_comap] using
      congrArg (fun I : Ideal A1 ↦ x ∈ I) (n.over_def m)
  exact hunder_mem.trans hcomp_mem

/-- Helper for Lemma 15.115.3: the comparison equivalence produces the tensor-side branch lying
over the chosen maximal ideal `m` of `A₁`. -/
private theorem tensor_branch_exists_of_equiv
    (e : A1 ⊗[A] B ≃ₐ[A1] B1)
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] :
    ∃ qT : Ideal (A1 ⊗[A] B), qT.IsMaximal ∧ qT.LiesOver m := by
  -- The pulled-back ideal is the unique tensor-side candidate compatible with the comparison map.
  refine ⟨Ideal.comap e.toRingHom n, ?_, ?_⟩
  · exact tensor_branch_comap_isMaximal_of_equiv (A := A) (B := B) (K := K) (L := L) (K1 := K1) e n
  · exact tensor_branch_comap_liesOver_of_equiv (A := A) (B := B) (K := K) (L := L) (K1 := K1) e m n

/-- Helper for Lemma 15.115.3: transporting an ideal across a compatible ring equivalence
preserves its contraction to the base. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  -- Rewrite the target contraction through `e`; surjectivity then recovers the original ideal.
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Lemma 15.115.3: a branch ideal transported across a compatible ring equivalence
still lies over the same maximal ideal of the base. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions through the equivalence, then reuse the original lies-over equality.
  rw [Ideal.liesOver_iff]
  ext x
  have htransport :
      x ∈ Ideal.under R (Ideal.map e.toRingHom q) ↔ x ∈ Ideal.under R q := by
    simpa [Ideal.under, Ideal.mem_comap] using
      congrArg (fun I : Ideal R ↦ x ∈ I)
        (ideal_map_comap_eq_of_ringEquiv_comp
          (f := algebraMap R S) (g := algebraMap R T) e he q)
  have hover :
      x ∈ Ideal.under R q ↔ x ∈ p := by
    simpa [Ideal.under, Ideal.mem_comap] using
      congrArg (fun I : Ideal R ↦ x ∈ I) (q.over_def p).symm
  exact hover.symm.trans htransport.symm

-- Route correction: the source-faithful reduction now isolates an abstract localization-conjugation
-- step under a comparison equivalence `A₁ ⊗[A] B ≃ B₁`. The remaining blocker is to construct that
-- comparison equivalence and then finish the tensor-side closed-fiber argument.
--
-- TODO: after constructing the tensor comparison equivalence, use the ideal-transport lemmas above
-- to package the induced localization comparison `Localization.AtPrime qT ≃ Localization.AtPrime n`
-- and identify the two local branch maps by `Localization.localRingHom_unique`.
-- The remaining source-faithful gap is then to identify the tensor-side closed fiber with the
-- corresponding local factor of `κ(m) ⊗[ResidueField A] ResidueField B`, prove that factor is a
-- separable field over `κ(m)`, and close with Lemma `15.112.5`.
/-- Lemma 15.115.3: let `A → B` be an extension of discrete valuation rings, let `K` and `L` be
the fraction fields of `A` and `B`, and let `K₁ / K` be a finite extension. Writing
`A₁ = integralClosure A K₁` and `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, every localized branch
`(A₁)_m → (B₁)_n` with `m` a maximal ideal of `A₁` and `n` a maximal ideal of `B₁` lying over
`m` is formally smooth for the maximal-ideal-adic topology on `(B₁)_n`. -/
theorem formallySmoothForAdic_localization_baseChange_integralClosure
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B))
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] :
    (Localization.localRingHom m n (algebraMap A1 B1) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := by
  let e : A1 ⊗[A] B ≃ₐ[A1] B1 :=
    tensor_base_change_comparison_equiv_of_formally_smooth
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) hfs
  -- The comparison equivalence reduces the target branch to the corresponding tensor-side branch.
  let qT : Ideal (A1 ⊗[A] B) := Ideal.comap e.toRingHom n
  let _ : qT.IsMaximal :=
    tensor_branch_comap_isMaximal_of_equiv
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) e n
  have hqTl : qT.LiesOver m :=
    tensor_branch_comap_liesOver_of_equiv
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) e m n
  let _ : qT.LiesOver m := hqTl
  have hmap_over :
      (Ideal.map e.toRingHom qT).LiesOver m := by
    -- The ideal-transport API now isolates the purely equivariant part of the source proof.
    exact
      ideal_map_liesOver_of_ringEquiv
        (R := A1) (S := A1 ⊗[A] B) (T := B1)
        e.toRingEquiv
        (tensor_base_change_comparison_comp_algebraMap (e := e))
        m qT
  let _ := hmap_over
  have hbranch :=
    tensor_branch_exists_of_equiv
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) e m n
  let _ := hbranch
  -- TODO: construct the canonical comparison equivalence `e`, then on the tensor-side branch
  -- identify the closed fiber with the relevant factor of
  -- `κ(m) ⊗[ResidueField A] ResidueField B`, prove that factor is a separable field over `κ(m)`,
  -- apply Lemma `15.112.5`, and finally transport formal smoothness back to the original branch.
  sorry

end
