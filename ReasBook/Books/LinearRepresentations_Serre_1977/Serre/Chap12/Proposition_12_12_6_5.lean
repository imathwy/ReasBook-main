import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

section

variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

-- Proof sketch: for each `Γ_K`-elementary subgroup `H`, quasisplitness identifies
-- `characterRingOverFieldInExtension K (AlgebraicClosure K)` with
-- `overlineCharacterRingOverField K` on `H` by
-- Corollary `12-12.2-2`. If `φ ∈ \overline{R}_K(G)`, then every restriction `φ|_H` lies in
-- `R_K(H)`, so Proposition `12-12.6-4` implies `φ ∈ R_K(G)`. Hence
-- `\overline{R}_K(G) = R_K(G)`, and another application of Corollary `12-12.2-2` gives that
-- `K[G]` is quasisplit.
--
-- Source/core/bridge triage:
-- * source-facing: Serre's quasisplitness criterion detected on `Γ_K`-elementary subgroups.
-- * core/canonical owners: `IsQuasisplitGroupAlgebra`, `R[K](G)`, `R̄[K](G)`.
-- * bridge/view: `mem_overlineCharacterRingInExtension_iff` and
--   `classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups`.
--
-- The primitive input data are the intermediate field `K` and the subgroupwise quasisplitness
-- hypothesis `hquasi`; the class-function packaging used below is derived API needed only to apply
-- Proposition `12-12.6-4`.
/-- Helper for Proposition 12-12.6-5: in the present item, Serre's quasisplitness condition is
tracked through the equivalent equality `R[K](G) = \overline{R}_K(G)`. -/
private abbrev IsQuasisplitGroupAlgebra (K : Type*) [Field K] (G : Type*) [Group G] : Prop :=
  R[K](G) = R̄[K](G)

/-- Helper for Proposition 12-12.6-5: the ring-equality formulation is the quasisplitness owner
used throughout this file. -/
private theorem characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra
    (K : Type*) [Field K] (G : Type*) [Group G] :
    R[K](G) = R̄[K](G) ↔ IsQuasisplitGroupAlgebra K G := by
  -- Route correction: use the equivalent ring-equality owner directly to avoid an upstream import
  -- incompatibility unrelated to the present proposition.
  rfl

/-- Helper for Proposition 12-12.6-5: precomposition along a map of finite groups preserves the
ambient function algebra structure. -/
private def precompAlgHom {α β : Type*} (K : Type*) [Field K] (f : α → β) :
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

/-- Helper for Proposition 12-12.6-5: restricting a finite-dimensional representation does not
change the underlying vector-space finiteness. -/
private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (K : Type*) [Field K]
    (f : H →* J) (ρ : Rep K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  -- Restriction keeps the same underlying vector space, so instance search closes the goal.
  infer_instance

/-- Helper for Proposition 12-12.6-5: precomposing a virtual `K`-character with a subgroup
inclusion stays inside the character ring. -/
private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (K : Type*) [Field K]
    (f : H →* J) (χ : R[K](J)) :
    precompAlgHom K f χ ∈ R[K](H) := by
  -- Build the claim on generators of the algebraic adjunction defining `R[K](J)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res K f ρ
    -- Characters of restricted finite-dimensional representations are still virtual characters.
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

omit [Finite G] in
/-- Helper for Proposition 12-12.6-5: restricting an element of `R[K](G)` to a subgroup stays in
the subgroup character ring. -/
private theorem restrict_mem_characterRingOverField
    (K : Type*) [Field K] (H : Subgroup G) (χ : R[K](G)) :
    (fun h : H ↦ (χ : G → K) h) ∈ R[K](H) := by
  -- Restriction is just precomposition with the subgroup inclusion.
  simpa using precomp_mem_characterRingOverField K H.subtype χ

omit [Finite G] in
/-- Helper for Proposition 12-12.6-5: restricting a bundled class function to a subgroup still
gives a bundled class function. -/
private theorem classFunctionRestriction_mem
    {K : Type*} [Field K] [CharZero K] (H : Subgroup G) (χ : classFunctionSubmodule K G) :
    ((LinearMap.funLeft K K H.subtype).comp (classFunctionSubmodule K G).subtype) χ ∈
      classFunctionSubmodule K H := by
  -- Conjugacy in `H` maps to conjugacy in `G`, so the class-function property descends.
  refine (mem_classFunctionSubmodule_iff K _).2 ?_
  let hχClass : _root_.IsClassFunction (χ : G → K) := (mem_classFunctionSubmodule_iff K _).1 χ.2
  refine ⟨fun {u v} huv ↦ ?_⟩
  have huvH : IsConj u v := (ConjClasses.mk_eq_mk_iff_isConj).1 huv
  have huvG : IsConj (u : G) (v : G) := by
    rw [isConj_iff] at huvH ⊢
    rcases huvH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact hχClass.eq_of_isConj huvG

/-- Helper for Proposition 12-12.6-5: the linear restriction map on bundled class functions. -/
private def classFunctionRestriction
    {K : Type*} [Field K] [CharZero K] (H : Subgroup G) :
    classFunctionSubmodule K G →ₗ[K] classFunctionSubmodule K H :=
  LinearMap.codRestrict (classFunctionSubmodule K H)
    ((LinearMap.funLeft K K H.subtype).comp (classFunctionSubmodule K G).subtype)
    (classFunctionRestriction_mem H)

omit [Finite G] in
/-- Helper for Proposition 12-12.6-5: evaluating the bundled restriction map only changes the
ambient type from `G` to `H`. -/
@[simp] private theorem classFunctionRestriction_apply
    {K : Type*} [Field K] [CharZero K] (H : Subgroup G) (χ : classFunctionSubmodule K G) (h : H) :
    (classFunctionRestriction H χ : H → K) h = (χ : G → K) h :=
  rfl

omit [Finite G] in
/-- Helper for Proposition 12-12.6-5: the local restriction map agrees pointwise with the
canonical subgroup restriction imported from Proposition `12-12.6-4`. -/
@[simp] private theorem classFunctionRestriction_eq_subgroupClassFunctionRestriction
    {K : Type*} [Field K] [CharZero K] (H : Subgroup G) (χ : classFunctionSubmodule K G) :
    classFunctionRestriction H χ = H.classFunctionRestriction χ := by
  -- Both bundled restrictions are defined by the same underlying function on `H`.
  ext h
  rfl

/-- Helper for Proposition 12-12.6-5: a bundled class function lies in `R[K](G)` exactly when all
of its restrictions to `Γ[K](G)`-elementary subgroups lie in the corresponding subgroup character
rings. -/
private theorem
    classFunction_mem_characterRingOverField_iff_local_restrict_mem_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L) (φ : classFunctionSubmodule K G) :
    (φ : G → K) ∈ R[K](G) ↔
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K](G)) H →
        (classFunctionRestriction H φ : H → K) ∈ R[K](H) := by
  -- Route correction: reuse the imported Proposition `12-12.6-4` directly and only translate
  -- between its canonical subgroup restriction and the local restriction wrapper used below.
  simpa [classFunctionRestriction_eq_subgroupClassFunctionRestriction] using
    (Representation.classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups
      (G := G) (L := L) K φ)

/-- Helper for Proposition 12-12.6-5: the canonical coefficient map from `K` to its algebraic
closure is injective. -/
private theorem algebraMap_algebraicClosure_injective
    (K : IntermediateField ℚ L) :
    Function.Injective (algebraMap K (AlgebraicClosure K)) := by
  -- This isolates the coefficient-descent bridge used when we pull class-function equalities
  -- back from `AlgebraicClosure K` to `K`.
  exact (algebraMap K (AlgebraicClosure K)).injective

omit [Finite G] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-5: every element of `\overline{R}_K(G)` is a class function. -/
private theorem isClassFunction_of_mem_overlineCharacterRing
    (K : IntermediateField ℚ L) {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    _root_.IsClassFunction χ := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- Move `χ` to the algebraic closure, where overline-membership is defined by honest
    -- character-ring membership.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχL_class : _root_.IsClassFunction χL :=
    isClassFunction_of_mem_characterRingOverField χL hχL
  refine ⟨fun {x y} hxy ↦ ?_⟩
  -- Route correction: descend conjugacy-invariance with an explicit injectivity witness rather
  -- than asking typeclass search to synthesize it inline.
  have hxyL :
      algebraMap K (AlgebraicClosure K) (χ x) = algebraMap K (AlgebraicClosure K) (χ y) := by
    change χL x = χL y
    exact hχL_class.factorsThrough hxy
  exact algebraMap_algebraicClosure_injective (K := K) hxyL

/-- Helper for Proposition 12-12.6-5: an element of `\overline{R}_K(G)` canonically defines a
bundled `K`-valued class function on `G`. -/
private def classFunctionOfMemOverlineCharacterRing
    (K : IntermediateField ℚ L) {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    classFunctionSubmodule K G :=
  ⟨χ, (mem_classFunctionSubmodule_iff K χ).2
    (isClassFunction_of_mem_overlineCharacterRing (K := K) hχ)⟩

omit [Finite G] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-5: restricting an overline virtual character to a subgroup
stays in the overline character ring. -/
private theorem restrict_mem_overlineCharacterRing
    (K : IntermediateField ℚ L) (H : Subgroup G) {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    (fun h : H ↦ χ h) ∈ R̄[K](H) := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- First lift `χ` to the algebraic closure, where overline-membership becomes honest
    -- character-ring membership.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχLH : (fun h : H ↦ χL h) ∈ R[AlgebraicClosure K](H) := by
    -- Restricting the lifted character stays inside the honest character ring on `H`.
    simpa [χL] using restrict_mem_characterRingOverField
      (AlgebraicClosure K) H ⟨χL, hχL⟩
  -- Descend the restricted lifted character back to the source-facing overline owner.
  rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) (fun h : H ↦ χ h)]
  simpa [χL] using hχLH

/-- Helper for Proposition 12-12.6-5: subgroupwise quasisplitness turns each
restriction of an overline-character into an honest `K`-character. -/
private theorem gammaElementary_restriction_mem_characterRing_of_mem_overline
    (K : IntermediateField ℚ L)
    (hquasi :
      ∀ H : Subgroup G,
        Subgroup.IsGammaElementary (Γ[K](G)) H → IsQuasisplitGroupAlgebra K H)
    {χ : G → K} (hχ : χ ∈ R̄[K](G))
    (H : Subgroup G) (hH : Subgroup.IsGammaElementary (Γ[K](G)) H) :
    (fun h : H ↦ χ h) ∈ R[K](H) := by
  have hχH_overline : (fun h : H ↦ χ h) ∈ R̄[K](H) := by
    -- First keep the restricted function inside the subgroup overline owner.
    exact restrict_mem_overlineCharacterRing (K := K) H hχ
  have hH_eq : R[K](H) = R̄[K](H) :=
    (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra K H).2 (hquasi H hH)
  -- Use quasisplitness of `K[H]` to replace the overline ring by the honest character ring.
  simpa [hH_eq] using hχH_overline

/-- Helper for Proposition 12-12.6-5: if all `Γ[K](G)`-elementary subgroups are quasisplit, then
every element of `\overline{R}_K(G)` already lies in `R_K(G)`. -/
private theorem overlineCharacterRing_le_characterRing_of_quasisplit_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L)
    (hquasi :
      ∀ H : Subgroup G,
        Subgroup.IsGammaElementary (Γ[K](G)) H → IsQuasisplitGroupAlgebra K H) :
    R̄[K](G) ≤ R[K](G) := by
  let ΓK := Γ[K](G)
  intro χ hχ
  let χcf : classFunctionSubmodule K G :=
    classFunctionOfMemOverlineCharacterRing (K := K) hχ
  have hχcf :
      ((χcf : G → K) ∈ R[K](G)) ↔
        ∀ H : Subgroup G, Subgroup.IsGammaElementary ΓK H →
          (classFunctionRestriction H χcf : H → K) ∈ R[K](H) := by
    -- Package the source function as a bundled class function so Proposition `12-12.6-4`
    -- applies exactly.
    simpa [ΓK, χcf] using
      classFunction_mem_characterRingOverField_iff_local_restrict_mem_on_gammaElementarySubgroups
        K χcf
  have hχcf_mem : ((χcf : G → K) ∈ R[K](G)) := by
    rw [hχcf]
    intro H hH
    -- The restriction step is precisely the subgroupwise Serre argument.
    simpa [classFunctionRestriction_apply, χcf] using
      gammaElementary_restriction_mem_characterRing_of_mem_overline
        (K := K) hquasi hχ H hH
  simpa [χcf, classFunctionOfMemOverlineCharacterRing] using hχcf_mem

/-- Helper for Proposition 12-12.6-5: subgroupwise quasisplitness forces the honest and overline
character rings of `G` to coincide. -/
private theorem characterRing_eq_overlineCharacterRing_of_quasisplit_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L)
    (hquasi :
      ∀ H : Subgroup G,
        Subgroup.IsGammaElementary (Γ[K](G)) H → IsQuasisplitGroupAlgebra K H) :
    R[K](G) = R̄[K](G) := by
  -- The forward inclusion is always available, while the reverse inclusion is the Serre
  -- subgroup-detection argument established just above.
  apply le_antisymm
  · simpa using (characterRingOverField_le_overlineCharacterRing K G : R[K](G) ≤ R̄[K](G))
  · exact
      overlineCharacterRing_le_characterRing_of_quasisplit_on_gammaElementarySubgroups
        (K := K) hquasi

/-- Proposition 12-12.6-5: let `L / ℚ` be a cyclotomic realization for the exponent of `G`, and
let `K ⊆ L` be an intermediate field, with associated subgroup
`Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ`, where `m = Monoid.exponent G`. If the
group algebra `K[H]` is quasisplit for every `Γ_K`-elementary subgroup `H ≤ G`, then `K[G]` is
quasisplit. -/
theorem isQuasisplitGroupAlgebra_of_quasisplit_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L)
    (hquasi :
      ∀ H : Subgroup G,
        Subgroup.IsGammaElementary (Γ[K](G)) H → IsQuasisplitGroupAlgebra K H) :
    IsQuasisplitGroupAlgebra K G := by
  -- Reduce quasisplitness to the ring equality packaged by the previous helper.
  have hEq : R[K](G) = R̄[K](G) :=
    characterRing_eq_overlineCharacterRing_of_quasisplit_on_gammaElementarySubgroups
      (K := K) hquasi
  -- Corollary `12-12.2-2` converts the ring equality into Serre's quasisplitness condition.
  exact (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra K G).1 hEq

end

end Representation
