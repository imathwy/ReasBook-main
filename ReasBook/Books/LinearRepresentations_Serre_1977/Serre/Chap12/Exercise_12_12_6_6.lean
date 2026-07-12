import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2

open scoped BigOperators Representation SubgroupInduction

noncomputable section

universe u v w

namespace Subgroup

section

open Representation

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

private local instance : Fintype G := Fintype.ofFinite G
private local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

-- The bundled subgroup restriction `Subgroup.classFunctionRestriction` (and its `@[simp]`
-- evaluation lemma `Subgroup.classFunctionRestriction_apply`) is supplied by the imported owner
-- `Serre.Chap07.Exercise_7_7_2_5`; we reuse it directly here rather than redeclaring a local copy.

-- Source/core/bridge triage: the exercise is `source-facing`, so the owner here is the intrinsic
-- `K`-valued ring `R̄[K](G)`. The algebraic-closure realization
-- `overlineCharacterRingOverField K G` is only a bridge/view and should not own the main
-- induction API.
-- Proof sketch: if `χ ∈ R̄[K](H)`, then its coefficientwise image in `AlgebraicClosure K`
-- belongs to `R[AlgebraicClosure K](H)` by `mem_overlineCharacterRingInExtension_iff`. Theorem
-- `12-12.6-2`
-- puts the induced closure-valued class function in `R[AlgebraicClosure K](G)`, and the
-- coefficientwise embedding commutes with induction, so the induced `K`-valued class function
-- lies in `R̄[K](G)`.
/-- Inducing a virtual character in `\overline{R}_K(H)` gives an element of
`\overline{R}_K(G)`. -/
theorem inducedClassFunction_mem_overlineCharacterRing
    (H : Subgroup G) (χ : R̄[K](H)) :
    Ind[H]((χ : H → K)) ∈ R̄[K](G) := by
  -- Move the source character to the algebraic closure, where induction already preserves the
  -- honest character ring.
  let χL : H → AlgebraicClosure K := fun h ↦ algebraMap K (AlgebraicClosure K) ((χ : H → K) h)
  have hχL : χL ∈ R[AlgebraicClosure K](H) := by
    simpa [χL] using
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) (χ : H → K)).1 χ.2
  -- Coefficientwise extension commutes with the induction formula, so the target is the induced
  -- algebraic-closure-valued virtual character.
  have hInd :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
          (Ind[H]((χ : H → K))) =
        Ind[H](χL) := by
    ext g
    classical
    rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction]
    change
      algebraMap K (AlgebraicClosure K)
          ((Nat.card H : K)⁻¹ *
            ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then (χ : H → K) ⟨s⁻¹ * g * s, hsg⟩ else 0) =
        (Nat.card H : AlgebraicClosure K)⁻¹ *
          ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then χL ⟨s⁻¹ * g * s, hsg⟩ else 0
    rw [map_mul]
    have hsum :
        algebraMap K (AlgebraicClosure K)
            (∑ s : G, if hsg : s⁻¹ * g * s ∈ H then (χ : H → K) ⟨s⁻¹ * g * s, hsg⟩ else 0) =
          ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then χL ⟨s⁻¹ * g * s, hsg⟩ else 0 := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro s hs
      by_cases hsg : s⁻¹ * g * s ∈ H
      · simp [hsg, χL]
      · simp [hsg]
    rw [map_inv₀, map_natCast, hsum]
  refine (mem_overlineCharacterRingInExtension_iff
    K (AlgebraicClosure K) (Ind[H]((χ : H → K)))).2 ?_
  exact hInd ▸
    Subgroup.inducedClassFunction_mem_characterRingOverField
      (K := AlgebraicClosure K) H ⟨χL, hχL⟩

/-- The canonical `ℤ`-linear induction map `\overline{R}_K(H) → \overline{R}_K(G)`. -/
def overlineCharacterRingInduction (H : Subgroup G) (K : Type v) [Field K] [CharZero K] :
    R̄[K](H) →ₗ[ℤ] R̄[K](G) :=
  LinearMap.codRestrict
    (R̄[K](G)).toSubmodule
    ((((classFunctionSubmodule K G).subtype.comp H.classFunctionInduction).restrictScalars ℤ).comp
      (R̄[K](H)).toSubmodule.subtype)
    (inducedClassFunction_mem_overlineCharacterRing H)

-- Proof sketch: this is immediate from the definition of `H.overlineCharacterRingInduction K`.
/-- Evaluating the integral subgroup induction map recovers the induced `K`-valued class
function. -/
@[simp] theorem overlineCharacterRingInduction_apply
    (H : Subgroup G) (χ : R̄[K](H)) :
    ((H.overlineCharacterRingInduction K χ : R̄[K](G)) : G → K) =
      Ind[H]((χ : H → K)) :=
  rfl

end

end Subgroup

namespace Representation

section

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

private local instance : Fintype G := Fintype.ofFinite G

private local instance
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } :=
  Classical.decEq _

-- Proof sketch: follow the proof of Proposition `12-12.6-4`. Write the unit element of
-- `R[AlgebraicClosure K](G)` as a finite sum of inductions from `Γ_K`-elementary subgroups,
-- multiply by a given element of `R̄[K](G)`, and use closure of `R̄[K](H)` under multiplication
-- by restriction to keep every subgroup summand in the source-facing owner.
section

variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

omit [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: multiplying an induced class function by a global class
function is the same as inducing the product with the restricted factor. -/
private lemma induced_mul_eq_induced_mul_classFunctionRestriction_overField
    (H : Subgroup G) (ψ : H → K) (φ : classFunctionSubmodule K G) :
    Ind[H](ψ) * (φ : G → K) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → K) h) := by
  classical
  -- Compare the two induced class functions pointwise, replacing the global class-function value
  -- by its conjugacy-invariant value on the subgroup element contributing to induction.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  have hsum :
      ∑ s : G, (if hsx : s⁻¹ * x * s ∈ H then ψ ⟨s⁻¹ * x * s, hsx⟩ else 0) * (φ : G → K) x =
        ∑ s : G, if hsx : s⁻¹ * x * s ∈ H then
          ψ ⟨s⁻¹ * x * s, hsx⟩ * (H.classFunctionRestriction φ : H → K) ⟨s⁻¹ * x * s, hsx⟩
        else 0 := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsx : s⁻¹ * x * s ∈ H
    · have hsx' : s⁻¹ * (x * s) ∈ H := by
        simpa [mul_assoc] using hsx
      have hφ :
          (φ : G → K) (s⁻¹ * x * s) = (φ : G → K) x := by
        exact ((mem_classFunctionSubmodule_iff K _).1 φ.2).eq_of_isConj <|
          isConj_iff.2 ⟨s, by group⟩
      have hφ' :
          (φ : G → K) (s⁻¹ * (x * s)) = (φ : G → K) x := by
        simpa [mul_assoc] using hφ
      simp [hsx', Subgroup.classFunctionRestriction_apply, hφ', mul_comm, mul_assoc]
    · simp [hsx]
  rw [hsum]

omit [CharZero K] in
/-- Helper for Exercise 12-12.6-6: descent along `K ↪ AlgebraicClosure K` is injective on
coefficients. -/
private theorem algebraMap_algebraicClosure_injective :
    Function.Injective (algebraMap K (AlgebraicClosure K)) := by
  exact (algebraMap K (AlgebraicClosure K)).injective

omit [Finite G] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: precomposition along a function produces the canonical
`ℤ`-algebra hom on function spaces. -/
private def precompAlgHom {α β : Type*} (f : α → β) :
    (β → K) →ₐ[ℤ] α → K where
  toFun := LinearMap.funLeft ℤ K f
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext x
    rfl
  map_mul' χ ψ := by
    ext x
    rfl
  commutes' n := by
    ext x
    rfl

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: restricting a finite-dimensional representation preserves
finite-dimensionality. -/
private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (f : H →* J)
    (ρ : Rep.{max u v} K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  infer_instance

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: precomposition of an honest virtual character stays in the
honest character ring. -/
private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (f : H →* J) (χ : R[K](J)) :
    precompAlgHom (K := K) f χ ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res (K := K) f ρ
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: restricting an honest virtual character to a subgroup stays in
the honest character ring. -/
private theorem restrict_mem_characterRingOverField_of_mem
    (H : Subgroup G) {χ : G → K} (hχ : χ ∈ R[K](G)) :
    (fun h : H ↦ χ h) ∈ R[K](H) := by
  let χR : R[K](G) := ⟨χ, hχ⟩
  simpa [χR, precompAlgHom] using
    precomp_mem_characterRingOverField (K := K) H.subtype χR

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: every element of `\overline{R}_K(G)` is a class function. -/
private theorem isClassFunction_of_mem_overlineCharacterRing
    {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    _root_.IsClassFunction χ := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- Overline-membership is defined by honest character-ring membership after extending
    -- coefficients to the algebraic closure.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχL_class : _root_.IsClassFunction χL :=
    Representation.isClassFunction_of_mem_characterRingOverField χL hχL
  refine ⟨fun {x y} hxy ↦ ?_⟩
  -- Descend conjugacy invariance coefficientwise through the injective scalar extension.
  have hxyL :
      algebraMap K (AlgebraicClosure K) (χ x) =
        algebraMap K (AlgebraicClosure K) (χ y) := by
    change χL x = χL y
    exact hχL_class.factorsThrough hxy
  exact algebraMap_algebraicClosure_injective (K := K) hxyL

omit [Finite G] [CharZero K] in
/-- Helper for Exercise 12-12.6-6: restricting an overline virtual character to a subgroup stays
in the overline character ring. -/
private theorem restrict_mem_overlineCharacterRing
    (H : Subgroup G) {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    (fun h : H ↦ χ h) ∈ R̄[K](H) := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- First lift to the algebraic closure, where the restriction theorem is already available.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχLH : (fun h : H ↦ χL h) ∈ R[AlgebraicClosure K](H) := by
    -- The lifted character remains a virtual character after restricting to the subgroup.
    exact restrict_mem_characterRingOverField_of_mem (K := AlgebraicClosure K) H hχL
  -- Descend the restricted algebraic-closure-valued virtual character back to the source-facing
  -- owner `R̄[K](H)`.
  rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) (fun h : H ↦ χ h)]
  simpa [χL] using hχLH

variable (K : IntermediateField ℚ L)

local notation "ΓK" => Γ[K](G)

/-- Helper for Exercise 12-12.6-6: classical decidability on the overline direct-sum
coefficients. -/
private local instance
    (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) (χ : R̄[K](H.1)) :
    Decidable (χ ≠ 0) := by
  classical
  infer_instance

set_option maxHeartbeats 400000 in
-- The endgame expands a `DFinsupp` witness into a finite sum and then rewrites each summand
-- through induction-restriction identities; the extra heartbeats keep that normalization stable.
/-- Exercise 12-12.6-6: the induction map
`Ind : ⨁_{H ∈ X_K} \overline{R}_K(H) → \overline{R}_K(G)`
is surjective, where
`Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ` and `X_K` is the set of `Γ_K`-elementary
subgroups of `G`. -/
theorem gammaElementarySubgroupOverlineCharacterRingInduction_surjective
    :
    Function.Surjective
      (DFinsupp.lsum ℤ
        (fun H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } ↦
          H.1.overlineCharacterRingInduction K)) := by
  intro χ
  obtain ⟨ξ, hξ⟩ := gammaElementarySubgroupInductionOverField_surjective (G := G) (L := L)
    K (1 : R[K](G))
  have hχcf_mem : (χ : G → K) ∈ classFunctionSubmodule K G := by
    -- Package the source function into the canonical class-function owner before replaying the
    -- Proposition `12-12.6-4` induction identity.
    rw [mem_classFunctionSubmodule_iff K]
    exact isClassFunction_of_mem_overlineCharacterRing (K := K) χ.2
  let χcf : classFunctionSubmodule K G := ⟨(χ : G → K), hχcf_mem⟩
  let ηFun :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R̄[K](H.1) :=
    fun H ↦
      let hη_mem :
          (fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction χcf : H.1 → K) h) ∈
            R̄[K](H.1) := by
        -- Each summand is the product of an honest subgroup virtual character with the restricted
        -- overline virtual character.
        refine (R̄[K](H.1)).mul_mem ?_ ?_
        · exact (characterRingOverField_le_overlineCharacterRing K H.1) (ξ H).2
        · exact restrict_mem_overlineCharacterRing (K := K) H.1 χ.2
      ⟨fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction χcf : H.1 → K) h,
        hη_mem⟩
  let η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R̄[K](H.1) :=
    DFinsupp.equivFunOnFintype.symm ηFun
  have hone :
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
        (1 : G → K) := by
    -- Rewrite the Brauer-induction witness as an equality of ambient functions.
    have hξ_fun :
        ((gammaElementarySubgroupInductionOverField K ΓK ξ : R[K](G)) : G → K) =
          (1 : G → K) := by
      simpa using congrArg ((↑) : R[K](G) → G → K) hξ
    rw [gammaElementarySubgroupInductionOverField_apply] at hξ_fun
    simpa [Subgroup.characterRingOverFieldInduction_apply] using hξ_fun
  have hη_sum :
      η.sum (fun H ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom) =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.overlineCharacterRingInduction K (ηFun H) := by
    -- Convert the `DFinsupp` witness to the equivalent finite family before expanding the sum.
    have hη :
        DFinsupp.equivFunOnFintype η = ηFun := by
      funext H
      simpa [η] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply ηFun) H
    calc
      η.sum (fun H ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (DFinsupp.equivFunOnFintype η H) := by
              exact DFinsupp.sum_eq_sum_fintype
                (v := η)
                (f := fun H ψH ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom ψH)
                (hf := fun H ↦ by simp)
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (ηFun H) := by
              rw [hη]
  refine ⟨η, ?_⟩
  let ψG : R̄[K](G) :=
    DFinsupp.lsum ℤ
      (fun H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } ↦
        H.1.overlineCharacterRingInduction K) η
  have hψG_bundled :
      ψG =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.overlineCharacterRingInduction K (ηFun H) := by
    -- Expand the direct-sum induction map only after normalizing the owner from `DFinsupp` to a
    -- finite family.
    calc
      ψG =
          (DFinsupp.sumAddHom fun H =>
            (H.1.overlineCharacterRingInduction K).toAddMonoidHom) η := by
            rfl
      _ = η.sum (fun H ψH ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom ψH) := by
            rw [DFinsupp.sumAddHom_apply]
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (ηFun H) := hη_sum
  have hψG_pointwise (g : G) :
      (ψG : G → K) g =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g := by
    -- Evaluate the bundled equality termwise using the explicit formula for subgroup induction.
    have hcoerce :
        (ψG : G → K) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((ηFun H : H.1 → K)) := by
      simpa [Subgroup.overlineCharacterRingInduction_apply] using
        congrArg ((↑) : R̄[K](G) → G → K) hψG_bundled
    simpa using congrFun hcoerce g
  have hψG :
      (ψG : G → K) = (χ : G → K) := by
    -- Multiply the decomposition of `1` by `χ`, then push the factor inside each induction using
    -- the Proposition `12-12.6-4` class-function identity.
    funext g
    rw [hψG_pointwise g]
    apply Subtype.ext
    change
      (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g : K) : L) =
        (((χ : G → K) g : K) : L))
    calc
      (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g : K) : L))
          =
            ((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
                (Ind[H.1]((ξ H : H.1 → K)) * (χ : G → K)) g : K) : L) := by
              refine congrArg (fun z : K => (z : L)) ?_
              refine Finset.sum_congr rfl ?_
              intro H hH
              have hterm :
                  Ind[H.1]((ηFun H : H.1 → K)) =
                    Ind[H.1]((ξ H : H.1 → K)) * (χcf : G → K) := by
                simpa [ηFun, χcf, Subgroup.classFunctionRestriction_apply] using
                  (induced_mul_eq_induced_mul_classFunctionRestriction_overField
                    (H := H.1) (ψ := (ξ H : H.1 → K)) (φ := χcf)).symm
              rw [hterm]
        _ =
            ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
                Ind[H.1]((ξ H : H.1 → K))) * (χ : G → K)) g : K) : L) := by
              refine congrArg (fun z : K => (z : L)) ?_
              simp [Pi.mul_apply, Finset.sum_mul]
        _ = ((((1 : G → K) * (χ : G → K)) g : K) : L) := by
              rw [hone]
        _ = (((χ : G → K) g : K) : L) := by
              simp
  exact Subtype.ext hψG

end

end

end Representation
