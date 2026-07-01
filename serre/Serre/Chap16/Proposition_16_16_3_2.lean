import Mathlib
import Serre.Chap16.Lemma_16_16_3_1
import Serre.Chap16.Theorem_16_16_2_2

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {A' : Type u} [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [Module.Finite A A']
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
variable [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A
local notation "k'" => IsLocalRing.ResidueField A'
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P_k'(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k' G
local notation "eA" => (projectiveGrothendieckBaseChangeHom K' : P₀[A](G) →+ R₀[K'](G))
local notation "eA'" => (projectiveGrothendieckBaseChangeHom K' : P₀[A'](G) →+ R₀[K'](G))

/- Domain-style sampling for Proposition 16-16.3-2:
* primary domain: projective Grothendieck classes under scalar extension to the common fraction
  field `K'`, with Serre's source-facing actual-projective images over the finite local extension
  `A ⟶ A'`;
* relevant owner declarations inspected in this domain:
  `FiniteProjectiveGroupAlgebraModule`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`,
  `projectiveGrothendieckBaseChangeHom`,
  `projectiveGrothendieckReductionEquiv`;
* best owner abstraction: the Chapter `16` scalar-extension owners
  `projectiveGrothendieckScalarExtensionHom A K' : P₀[k](G) →+ R₀[K'](G)` and
  `projectiveGrothendieckScalarExtensionHom A' K' : P₀[k'](G) →+ R₀[K'](G)`, with the
  source-facing actual projective images over `A` and `A'` mapped into them through the reduction
  equivalences `P₀[A](G) ≃+ P₀[k](G)` and `P₀[A'](G) ≃+ P₀[k'](G)`.
* source/core/bridge triage:
  source-facing: Serre's conclusion that `x` comes from an actual projective `A[G]`-module;
  core/canonical: the scalar-extension maps
    `projectiveGrothendieckScalarExtensionHom A K'`,
    `projectiveGrothendieckScalarExtensionHom A' K'`, and the positive subsets
    `P⁺[k](G)`, `P⁺[k'](G)`;
  bridge/view: this proposition, which keeps the source-facing image statements
    `eA '' P⁺[A](G)` and `eA' '' P⁺[A'](G)` as the public surface while treating the residue-field
    scalar-extension owners as the underlying canonical layer.
Primitive data vs derived API:
* primitive data: membership in the canonical scalar-extension positive images
  `(projectiveGrothendieckScalarExtensionHom A K' : P₀[k](G) →+ R₀[K'](G)) '' P⁺[k](G)` and
  `(projectiveGrothendieckScalarExtensionHom A' K' : P₀[k'](G) →+ R₀[K'](G)) '' P⁺[k'](G)`;
* derived API: the source-facing projective `A[G]`- and `A'[G]`-module witnesses extracted via
  `mem_projectivePositiveSubset_iff` and the reduction equivalences.
This file therefore keeps the image-membership theorem as the main entry and does not introduce a
parallel existential/uniqueness owner.
-/

-- Proof sketch: the helper theorem below sends the source-facing positive-image hypothesis
-- `n • x ∈ eA' '' P⁺[A'](G)` into the canonical residue-field scalar-extension positive image over
-- `A'`. Theorem `16-16.2-2` then forces the character of `x` to vanish on `p`-singular
-- elements, and the `K`-valuedness hypothesis descends `x` from `R_K'(G)` to the corresponding
-- projective scalar-extension range over `A`. Lemma `16-16.3-1` is the source-facing bridge that
-- turns the resulting canonical positivity back into the image `eA '' P⁺[A](G)`.
variable (K)

/-- The source-facing image of actual projective `A[G]`-classes in `R_K'(G)` lies in the canonical
residue-field scalar-extension positive image. -/
theorem projectivePositiveImage_subset_scalarExtensionPositiveImage
    [HenselianLocalRing A] :
    eA '' P⁺[A](G) ⊆
      (projectiveGrothendieckScalarExtensionHom A K' : P_k(G) →+ R₀[K'](G)) '' P⁺[k](G) := by
  rintro x ⟨y, hy, rfl⟩
  rcases (mem_projectivePositiveSubset_iff A G).1 hy with ⟨P, rfl⟩
  refine ⟨[P.residueFieldReduction]ₚ₀, ?_, ?_⟩
  · exact (mem_projectivePositiveSubset_iff k G).2 ⟨P.residueFieldReduction, rfl⟩
  · have hred' :
        projectiveGrothendieckReductionEquiv (A := A) (G := G) [P]ₚ₀ =
          [P.residueFieldReduction]ₚ₀ := by
      -- On generators, reduction identifies an actual projective class with its residue-field
      -- reduction class.
      change
        projectiveGrothendieckReductionHom (A := A) (G := G) [P]ₚ₀ =
          [P.residueFieldReduction]ₚ₀
      exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) P
    have hred :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
            [P.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
      rw [← hred']
      exact
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_apply [P]ₚ₀
    simp [projectiveGrothendieckScalarExtensionHom_apply,
      projectiveGrothendieckBaseChangeHom_projectiveClass_eq, hred]

/-- Helper for Proposition 16-16.3-2: the residue field of the finite local extension `A → A'`
still has characteristic `p`. -/
private theorem charP_residueField_of_local_extension
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A']
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
    [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    CharP (IsLocalRing.ResidueField A') p := by
  -- Embed `A` into `A'` by composing with the injective maps into the common fraction field `K'`.
  have hAK : Function.Injective (algebraMap A K) := by
    simpa [faithfulSMul_iff_algebraMap_injective] using
      (inferInstance : FaithfulSMul A K)
  have hKK' : Function.Injective (algebraMap K K') := RingHom.injective _
  have hAK' : Function.Injective (algebraMap A K') := by
    simpa [IsScalarTower.algebraMap_eq A K K'] using hKK'.comp hAK
  have hcomp : Function.Injective ((algebraMap A' K') ∘ (algebraMap A A')) := by
    simpa [IsScalarTower.algebraMap_eq A A' K'] using hAK'
  have hAA' : Function.Injective (algebraMap A A') := Function.Injective.of_comp hcomp
  -- The integral finite extension `A → A'` is therefore a local ring homomorphism, so it induces
  -- an injective map on residue fields.
  let _ : FaithfulSMul A A' :=
    (faithfulSMul_iff_algebraMap_injective A A').2 hAA'
  let _ : IsLocalHom (algebraMap A A') := by
    infer_instance
  let f : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A' :=
    IsLocalRing.ResidueField.map (algebraMap A A')
  exact charP_of_injective_ringHom f.injective p

/-- Helper for Proposition 16-16.3-2: on an actual projective generator, scalar extension from
`K` to `K'` after base change agrees with direct base change to `K'`. -/
private theorem finiteRepGrothendieckScalarExtension_projectiveClass_eq_direct
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    finiteRepGrothendieckScalarExtensionHom K K' G [P.scalarExtension K]₀ =
      [P.scalarExtension K']₀ := by
  -- Reassociate the iterated tensor product and collapse the redundant middle `K`-factor.
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk
    ((TensorProduct.AlgebraTensorModule.assoc A K K' K' K P.V).symm.trans
      (TensorProduct.AlgebraTensorModule.congr
        (TensorProduct.AlgebraTensorModule.rid K K' K')
        (LinearEquiv.refl A P.V))) ?_
  intro g
  ext x
  rfl

/-- Helper for Proposition 16-16.3-2: further scalar extension commutes with the source-facing
projective base-change map. -/
private theorem finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq :
    (finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) =
        projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' := by
  -- Check the identity on projective generators before extending additively to the quotient.
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp [projectiveGrothendieckBaseChangeHom]
  · intro P
    -- On generators, reuse the direct scalar-extension comparison before descending additively.
    simp [projectiveGrothendieckBaseChangeHom,
      finiteRepGrothendieckScalarExtension_projectiveClass_eq_direct
        (A := A) (K := K) (K' := K') (G := G) P]
  · intro y' hy'
    simpa using congrArg Neg.neg hy'
  · intro y₁ y₂ hy₁ hy₂
    simp [map_add, hy₁, hy₂]

/-- Helper for Proposition 16-16.3-2: if a positive multiple of `x` already comes from an actual
projective `A'[G]`-module, then the character of `x` vanishes on `p`-singular elements. -/
private theorem character_eq_zero_on_pSingular_of_nsmul_mem_projectivePositiveImage
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A']
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
    [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [HenselianLocalRing A']
    {x : R₀[K'](G)} {n : ℕ} (hn : 1 ≤ n)
    (hx :
      n • x ∈
        (projectiveGrothendieckBaseChangeHom (A := A') (G := G) K') '' P⁺[A'](G)) :
    ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := by
  -- Route correction: the residue-field characteristic bridge is now available, so the only
  -- remaining work is the source-faithful cancellation from the vanishing of `χ_(n • x)` to the
  -- vanishing of `χ_x`.
  let _ := hn
  let _ := hx
  let _ : CharP (IsLocalRing.ResidueField A') p :=
    charP_residueField_of_local_extension (A := A) (A' := A') (K := K) (K' := K') (p := p)
  sorry

/-- Helper for Proposition 16-16.3-2: the source-facing base-change map over the actual fraction
field `K` is injective. -/
private theorem projective_baseChange_injective
    [HenselianLocalRing A] :
    Function.Injective (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) := by
  -- Reflect equality of source-facing base-change classes through the split injectivity of the
  -- residue-field scalar-extension map and then back across the reduction equivalence.
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  intro x y hxy
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) x =
        projectiveGrothendieckReductionEquiv (A := A) (G := G) y := by
    apply hs.injective
    simpa [projectiveGrothendieckScalarExtensionHom_apply] using hxy
  exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).injective hred

/-- Helper for Proposition 16-16.3-2: restricting a projective `A'[G]`-module along
`A[G] → A'[G]` and comparing characters produces the expected
`[K' : K]`-multiple in `R_K'(G)`. -/
private theorem restricted_projective_witness_class_eq_extension_degree_nsmul
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    {n : ℕ} (P' : FiniteProjectiveGroupAlgebraModule A' G)
    (hP' : projectiveGrothendieckBaseChangeHom (A := A') (G := G) K' [P']ₚ₀ = n • x) :
    ∃ E : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀ =
        ((n * Module.finrank K K' : ℕ) • x) := by
  -- Route correction: the remaining gap is exactly Serre's restricted-witness comparison over the
  -- actual fraction field `K`; the K'-level placeholder route was discarded.
  let _ := x
  let _ := hchar
  let _ := P'
  let _ := hP'
  sorry

/-- Proposition 16-16.3-2: if `K' / K` is finite, the ordinary character of
`x ∈ R_K'(G)` is `K`-valued, and some positive multiple of `x` lies in the image
`eA' '' P⁺[A'](G)`, then `x` itself lies in the source-facing positive image
`eA '' P⁺[A](G)`. This is the bridge form of the canonical Chapter `16` scalar-extension
criterion. -/
theorem mem_projectivePositiveImage_of_character_valuedInBaseField
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    (hnsmul : ∃ n : ℕ, 1 ≤ n ∧ n • x ∈ eA' '' P⁺[A'](G))
    : x ∈ eA '' P⁺[A](G) := by
  -- Route correction: the injectivity bridge is now in place. The remaining source-faithful work
  -- is to descend from the `A'`-witness by proving p-singular vanishing for `x` itself and then
  -- comparing the restricted witness over `K`.
  let _ := x
  let _ := hchar
  let _ := hnsmul
  sorry

end

end Representation
