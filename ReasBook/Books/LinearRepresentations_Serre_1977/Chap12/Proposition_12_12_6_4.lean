import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2

noncomputable section

universe u v

open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

namespace Subgroup

section

variable {G : Type u} [Group G]

/-- Internal owner for precomposition on function algebras. The public mathematical content of
this file is the induced restriction on `R[K](G)`, not this raw function-space bridge. -/
private def precompAlgHom {α β : Type*} (K : Type v) [Field K] (f : α → β) :
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

private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (K : Type v) [Field K]
    (f : H →* J) (ρ : Rep.{max u v} K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  -- Restriction does not change the underlying `K`-vector space, so finite-dimensionality is
  -- inherited by instance search.
  infer_instance

private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (K : Type v) [Field K]
    (f : H →* J) (χ : R[K](J)) :
    precompAlgHom K f χ ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res K f ρ
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

-- Proof sketch: write `χ` as an integral linear combination of irreducible `K`-characters of
-- `G`. Restrict each generator along `H.subtype`; this is the character of the restricted
-- representation, hence lies in `R_K(H)`. The result follows by `ℤ`-linearity of the span
-- defining `characterRingOverField K`.
/-- Restricting an element of LinearRepresentations_Serre_1977's representation ring `R_K(G)` to a subgroup `H` gives an
element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverField
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) :
    (fun h : H ↦ (χ : G → K) h) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K H.subtype χ

/-- The canonical restriction algebra hom `R_K(G) → R_K(H)` attached to a subgroup `H ≤ G`. -/
def characterRingOverFieldRestriction (H : Subgroup G) (K : Type v) [Field K] :
    R[K](G) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K H.subtype).comp (R[K](G)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverField K H))

scoped[Representation] notation:max H " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestriction H K

-- Proof sketch: `(H ↾R[K])` is defined by pointwise evaluation along `H.subtype`.
/-- Evaluating `(H ↾R[K]) χ` at `h ∈ H` just evaluates `χ` at the same group element. -/
@[simp] theorem characterRingOverFieldRestriction_apply
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) (h : H) :
    (((H ↾R[K]) χ : R[K](H)) : H → K) h = (χ : G → K) h :=
  rfl

-- Proof sketch: this is the same precomposition argument as
-- `restrict_mem_characterRingOverField`, now applied to the subgroup inclusion `H ↪ J`.
/-- Restricting an element of `R_K(J)` along an inclusion `H ≤ J` gives an element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverFieldOfLe
    (K : Type v) [Field K] {H J : Subgroup G} (h : H ≤ J) (χ : R[K](J)) :
    (fun x : H ↦ (χ : J → K) (Subgroup.inclusion h x)) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K (Subgroup.inclusion h) χ

/-- The canonical restriction map `R_K(J) → R_K(H)` attached to an inclusion `H ≤ J`. -/
def characterRingOverFieldRestrictionOfLe
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] :
    R[K](J) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K (Subgroup.inclusion h)).comp (R[K](J)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverFieldOfLe K h))

scoped[Representation] notation:max h " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestrictionOfLe h K

-- Proof sketch: `(h ↾R[K])` is defined by evaluating `χ` on `H` through the inclusion `H ↪ J`.
/-- Evaluating `(h ↾R[K]) χ` at `x ∈ H` evaluates `χ` at the same group element viewed in `J`. -/
@[simp] theorem characterRingOverFieldRestrictionOfLe_apply
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] (χ : R[K](J)) (x : H) :
    (((h ↾R[K]) χ : R[K](H)) : H → K) x =
      (χ : J → K) (Subgroup.inclusion h x) :=
  rfl

end

end Subgroup

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

local instance instFintypeGammaElementaryRestriction : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 12-12.6-4: multiplying an induced `K`-valued class function by a
global bundled class function is the same as inducing the product with the canonical restriction
of the global factor. -/
lemma induced_mul_eq_induced_mul_classFunctionRestriction_overField
    {K : Type v} [Field K] (H : Subgroup G) (ψ : H → K) (φ : classFunctionSubmodule K G) :
    Ind[H](ψ) * (φ : G → K) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → K) h) := by
  classical
  -- Compare both sides pointwise and replace the ambient value of `φ` by its conjugacy-invariant
  -- value on the subgroup element contributing to the induction summand.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
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
    simp [hsx', hφ', mul_comm, mul_assoc]
  · simp [hsx]

omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-4: normalize the `DFinsupp` witness for gamma-elementary
induction into the corresponding ordinary finite sum over gamma-elementary subgroups. -/
lemma gamma_elementary_induction_sum_as_fintype_sum
    {K : IntermediateField ℚ L}
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    [Fintype { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    [DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    [(H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) →
      (χ : R[K](H.1)) → Decidable (χ ≠ 0)]
    (χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1))
    (η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R[K](H.1))
    (hη : DFinsupp.equivFunOnFintype η = χ) :
    η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        H.1.characterRingOverFieldInduction K (χ H) := by
  classical
  -- Replace the direct-sum object by the equivalent finitely indexed family before applying
  -- induction termwise on the gamma-elementary support.
  calc
    η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.characterRingOverFieldInduction K (DFinsupp.equivFunOnFintype η H) := by
          exact DFinsupp.sum_eq_sum_fintype
            (v := η)
            (f := fun H ψH ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom ψH)
            (hf := fun H => by simp)
    _ =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.characterRingOverFieldInduction K (χ H) := by
          rw [hη]

omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-4: multiplying Brauer's decomposition of `1` by `φ` turns the
induced sum of the modified subgroup terms back into `φ`. -/
lemma psi_eq_phi_from_brauer_decomposition
    {K : IntermediateField ℚ L}
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    [Fintype { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    (φ : classFunctionSubmodule K G)
    (ξ χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1))
    (hχ :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        (χ H : H.1 → K) =
          fun h : H.1 ↦
            (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h)
    (hone :
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
        (1 : G → K)) :
    ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((χ H : H.1 → K)) =
      (φ : G → K) := by
  classical
  -- Route correction: first prove the ambient function identity obtained by multiplying the
  -- Brauer decomposition of `1`, and only afterwards package it back into `R[K](G)`.
  funext g
  apply Subtype.ext
  calc
    ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        Ind[H.1]((χ H : H.1 → K))) g : K) : L))
        =
          (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              Ind[H.1]((χ H : H.1 → K)) g : K) : L)) := by
            -- Expand the evaluation of the finite sum before rewriting each summand.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            simp [Finset.sum_apply]
    _ =
          ((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              (Ind[H.1]((ξ H : H.1 → K)) * (φ : G → K)) g : K) : L) := by
            -- Rewrite each summand using the induction-restriction compatibility lemma.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            refine Finset.sum_congr rfl ?_
            intro H hH
            rw [hχ H]
            rw [← induced_mul_eq_induced_mul_classFunctionRestriction_overField
              (H := H.1) (ψ := (ξ H : H.1 → K)) (φ := φ)]
    _ =
        ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((ξ H : H.1 → K))) * (φ : G → K)) g : K) : L) := by
            -- Factor the common multiplicative term `φ` out of the finite sum.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            simp [Pi.mul_apply, Finset.sum_mul]
    _ = ((((1 : G → K) * (φ : G → K)) g : K) : L) := by
          rw [hone]
    _ = (((φ : G → K) g : K) : L) := by
          simp

-- Proof sketch: the forward implication is `restrict_mem_characterRingOverField`. For the reverse
-- implication, use Theorem `12-12.6-2` to write the unit element of `R_K(G)` as a finite sum of
-- inductions from `Γ_K`-elementary subgroups, multiply by the class function `φ`, and use the
-- class-function induction identity `φ ⋅ Ind = Ind (Res φ ⋅ -)` to conclude from the restriction
-- hypothesis that every summand lies in `R_K(G)`.
--
-- Source/core/bridge triage:
-- * source-facing: the detection criterion for membership in `R_K(G)`.
-- * core/canonical owner: bundled `K`-valued class functions `classFunctionSubmodule K G`.
-- * bridge/view: the underlying function coercion `classFunctionSubmodule K G → G → K`.
--
-- Primitive data are the bundled class function `φ` and the restriction-membership hypotheses on
-- `Γ_K`-elementary subgroups. The raw function `(φ : G → K)` and the pointwise restrictions
-- `H.classFunctionRestriction φ` are derived API.
/-- Proposition 12-12.6-4: let `L / ℚ` be a cyclotomic realization for the exponent of `G`, and
let `K ⊆ L` be an intermediate field, with associated subgroup
`Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ`, where `m = Monoid.exponent G`. A `K`-valued class
function on `G` belongs to `R[K](G)` if and only if, for every `Γ_K`-elementary subgroup `H ≤ G`,
its restriction to `H` belongs to `R[K](H)`. -/
theorem classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L) (φ : classFunctionSubmodule K G) :
    (φ : G → K) ∈ R[K](G) ↔
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K](G)) H →
        (H.classFunctionRestriction φ : H → K) ∈ R[K](H) := by
  let ΓK := Γ[K](G)
  constructor
  · intro hφ H hH
    -- Apply the canonical restriction map to the ambient virtual character and identify the
    -- resulting function with the canonical class-function restriction.
    have hrestrict : (fun h : H ↦ (φ : G → K) h) ∈ R[K](H) :=
      (((H ↾R[K]) ⟨(φ : G → K), hφ⟩ : R[K](H)) : R[K](H)).2
    simpa [Subgroup.classFunctionRestriction_apply] using hrestrict
  · intro hres
    classical
    obtain ⟨ξ, hξ⟩ := gammaElementarySubgroupInductionOverField_surjective (G := G) (L := L)
      K (1 : R[K](G))
    let _ : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } := Classical.decEq _
    let _ :
        (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) →
          (χ : R[K](H.1)) → Decidable (χ ≠ 0) := fun H χ => by
      classical
      infer_instance
    let χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1) := fun H ↦
      ⟨fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h,
        (R[K](H.1)).mul_mem (ξ H).2 (hres H.1 H.2)⟩
    let η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R[K](H.1) :=
      DFinsupp.equivFunOnFintype.symm χ
    have hone :
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
          (1 : G → K) := by
      -- Re-express the surjective Brauer-induction witness as an equality of ambient functions.
      have hξ_fun :
          ((gammaElementarySubgroupInductionOverField K (Γ[K](G)) ξ : R[K](G)) : G → K) =
            (1 : G → K) := by
        simpa using congrArg ((↑) : R[K](G) → G → K) hξ
      rw [gammaElementarySubgroupInductionOverField_apply] at hξ_fun
      simpa [Subgroup.characterRingOverFieldInduction_apply] using hξ_fun
    have hχ :
        ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          (χ H : H.1 → K) =
            fun h : H.1 ↦
              (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h := by
      -- The modified subgroup family `χ` was defined exactly by multiplying `ξ H` with the
      -- restricted class function on `H`.
      intro H
      rfl
    have hη : DFinsupp.equivFunOnFintype η = χ := by
      -- `η` is the direct-sum packaging of the finitely indexed family `χ`.
      funext H
      simpa [η] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply χ) H
    let ψG : R[K](G) := gammaElementarySubgroupInductionOverField K ΓK η
    have hψG_sum :
        η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.characterRingOverFieldInduction K (χ H) :=
      gamma_elementary_induction_sum_as_fintype_sum (K := K) (ΓK := ΓK) χ η hη
    have hψG_bundled :
        ψG =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.characterRingOverFieldInduction K (χ H) := by
      -- Expand the direct-sum Brauer witness only after the `DFinsupp` owner has been normalized.
      simpa [ψG, gammaElementarySubgroupInductionOverField_apply] using hψG_sum
    have hψG_pointwise (g : G) :
        (ψG : G → K) g =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((χ H : H.1 → K)) g :=
        by
      -- Evaluate the bundled equality at `g` after each summand is in canonical induced form.
      have hcoerce :
          ((ψG : R[K](G)) : G → K) =
            ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              Ind[H.1]((χ H : H.1 → K)) := by
        simpa [Subgroup.characterRingOverFieldInduction_apply] using
          congrArg ((↑) : R[K](G) → G → K) hψG_bundled
      simpa using congrFun hcoerce g
    have hsum_eq_phi :
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((χ H : H.1 → K)) =
          (φ : G → K) :=
      psi_eq_phi_from_brauer_decomposition (ΓK := ΓK) φ ξ χ hχ hone
    have hψG : (ψG : G → K) = (φ : G → K) := by
      -- Compare `ψG` with the normalized finite sum, then use the Brauer-multiplication helper to
      -- identify that sum with `φ`.
      funext g
      rw [hψG_pointwise g]
      simpa using congrFun hsum_eq_phi g
    -- Package the reconstructed ambient function back into `R[K](G)`.
    simpa [ψG, hψG] using ψG.2

end

end Representation
