import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_2_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_2_2

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
  [Algebra A A'] [Module.Finite A A']
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
variable [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
variable [Algebra.IsPushout A K A' K']
variable [CharZero K] [CharZero K']
variable [HenselianLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [HenselianLocalRing A'] [IsNoetherianRing A']
  [IsAdicComplete (IsLocalRing.maximalIdeal A') A']
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
    [HenselianLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
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

/-- Helper for Proposition 16-16.3-2: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class. -/
private noncomputable def fdRepIsoOfRho_for_identityScalarExtension
    {F : Type u} [Field F] {G : Type u} [Group G] [Finite G]
    (V : FDRep F G) : V ≅ FDRep.of V.ρ :=
  Action.mkIso (CategoryTheory.Iso.refl _) fun g ↦ by
    -- Rebundling preserves the carrier and action literally.
    ext x
    rfl

/-- Helper for Proposition 16-16.3-2: ordinary scalar extension along the identity coefficient
field does not change a finite-representation Grothendieck class. -/
private theorem finiteRepGrothendieckScalarExtensionHom_self
    {F : Type u} [Field F] {G : Type u} [Group G] [Finite G]
    (y : R₀[F](G)) :
    finiteRepGrothendieckScalarExtensionHom F F G y = y := by
  -- Check the identity on honest representation classes, then descend through additivity.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    change finiteRepGrothendieckScalarExtensionHom F F G [V]₀ = [V]₀
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
    refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
    let eScalar :=
      fdRepIsoOfRho_for_identityScalarExtension
        (F := F) (G := G) (FDRep.scalarExtension V : FDRep F G)
    let eBase := fdRepIsoOfRho_for_identityScalarExtension (F := F) (G := G) V
    let eRep : FDRep.of (FDRep.scalarExtension V : FDRep F G).ρ ≅ FDRep.of V.ρ := by
      refine Representation.Equiv.toFDRepIso ?_
      refine Representation.Equiv.mk (_root_.TensorProduct.lid F V.V) ?_
      intro g
      apply LinearMap.ext
      intro x
      induction x using _root_.TensorProduct.induction_on with
      | zero =>
          simp [FDRep.scalarExtension, Representation.scalarExtension]
      | tmul c v =>
          simp only [LinearMap.comp_apply, FDRep.scalarExtension, Representation.scalarExtension]
          change (_root_.TensorProduct.lid F V.V)
              ((LinearMap.baseChange F (V.ρ g)) (c ⊗ₜ[F] v)) =
            (V.ρ g) ((_root_.TensorProduct.lid F V.V) (c ⊗ₜ[F] v))
          rw [LinearMap.baseChange_tmul, _root_.TensorProduct.lid_tmul,
            _root_.TensorProduct.lid_tmul, map_smul]
      | add x y hx hy =>
          rw [map_add, map_add, hx, hy]
    exact ⟨eScalar.trans (eRep.trans eBase.symm)⟩
  · intro y hy
    simpa using congrArg Neg.neg hy
  · intro y z hy hz
    simp [map_add, hy, hz]

/-- Helper for Proposition 16-16.3-2: ordinary Grothendieck characters commute pointwise with
finite scalar extension of coefficients. -/
private theorem finiteRepGrothendieckCharacter_scalarExtensionHom_apply_local
    (y : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g =
      algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g) := by
  -- Prove the compatibility on generators and descend additively through the quotient.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    change
      (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) [V]₀) : G → K') g =
        algebraMap K K' ((finiteRepGrothendieckCharacter K G [V]₀ : G → K) g)
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq,
      finiteRepGrothendieckCharacter_class, finiteRepGrothendieckCharacter_class]
    simpa [FDRep.scalarExtension] using
      congrFun
        (ProjectiveScalarExtensionSplitInjective.scalarExtension_character_eq_map_local
          (G := G) (F := K) (E := K') (τ := V.ρ))
        g
  · intro y hy
    simpa using congrArg Neg.neg hy
  · intro y z hy hz
    simpa [map_add] using congrArg₂ HAdd.hAdd hy hz

/-- Helper for Proposition 16-16.3-2: ordinary scalar extension of virtual representations is
injective in characteristic zero. -/
private theorem finiteRepGrothendieckScalarExtensionHom_injective_local :
    Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  -- Characters detect equality over `K`; after scalar extension their values agree in `K'`.
  intro x y hxy
  apply (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).1
  ext g
  apply (algebraMap K K').injective
  calc
    algebraMap K K' ((finiteRepGrothendieckCharacter K G x : G → K) g) =
        (finiteRepGrothendieckCharacter K' G
          ((finiteRepGrothendieckScalarExtensionHom K K' G) x) : G → K') g := by
          exact (finiteRepGrothendieckCharacter_scalarExtensionHom_apply_local
            (K := K) (K' := K') (G := G) x g).symm
    _ = (finiteRepGrothendieckCharacter K' G
          ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g := by
          rw [hxy]
    _ = algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g) := by
          exact finiteRepGrothendieckCharacter_scalarExtensionHom_apply_local
            (K := K) (K' := K') (G := G) y g

/-- Helper for Proposition 16-16.3-2: if a positive multiple of `x` already comes from an actual
projective `A'[G]`-module, then the character of `x` vanishes on `p`-singular elements. -/
private theorem character_eq_zero_on_pSingular_of_nsmul_mem_projectivePositiveImage
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Algebra A A'] [Module.Finite A A']
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
    [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    -- `[CharZero K']` is essential: the conclusion is derived from `χ_(n•x) = n·χ_x = 0` by
    -- dividing by `n ≥ 1`, which requires `n` invertible, i.e. `char K' = 0` (Serre's setting).
    -- In characteristic `p` (e.g. `A = A' = 𝔽₂[[t]]`, `K' = 𝔽₂((t))`, `n = p`) one has
    -- `χ_(n•x) = 0` for ALL `x`, so `χ_x` need not vanish and the statement is false.
    [CharZero K']
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [HenselianLocalRing A'] [IsNoetherianRing A']
    [IsAdicComplete (IsLocalRing.maximalIdeal A') A']
    -- Serre's standing Chapter-16 hypothesis (algebraically closed residue field) applied to the
    -- finite local extension `A'`.  Mathematically `ResidueField A'` is a finite extension of the
    -- algebraically closed `ResidueField A`, hence equal to it and again algebraically closed; it is
    -- spelled out here because Theorem `16-16.2-1`/`16-16.2-2` (invoked below over `A'`) carry it.
    [IsAlgClosed (IsLocalRing.ResidueField A')]
    {x : R₀[K'](G)} {n : ℕ} (hn : 1 ≤ n)
    (hx :
      n • x ∈
        (projectiveGrothendieckBaseChangeHom (A := A') (G := G) K') '' P⁺[A'](G)) :
    ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := by
  -- Route correction: the residue-field characteristic bridge is now available, so the only
  -- remaining work is the source-faithful cancellation from the vanishing of `χ_(n • x)` to the
  -- vanishing of `χ_x`.
  let _ : CharP (IsLocalRing.ResidueField A') p :=
    charP_residueField_of_local_extension (A := A) (A' := A') (K := K) (K' := K') (p := p)
  let _ : HasEnoughRootsOfUnity K' (Monoid.exponent G) :=
    ProjectiveScalarExtensionSplitInjective.hasEnoughRootsOfUnity_extension_local
      (K := K) (L := K') (G := G)
  -- `K'` is characteristic `0` with enough roots of unity for the exponent of `G`, so it is a
  -- splitting field: Serre's Theorem 24 gives the quasisplit identity `R[K'](G) = R̄[K'](G)`,
  -- which Theorem `16-16.2-2` consumes as a `Fact`.
  haveI : Fact (R[K'](G) = R̄[K'](G)) :=
    ⟨characterRing_eq_overlineCharacterRing_of_isSplittingField⟩
  have hpositive :
      n • x ∈
        (projectiveGrothendieckScalarExtensionHom A' K' :
          P₀[IsLocalRing.ResidueField A'](G) →+ R₀[K'](G)) '' P⁺[IsLocalRing.ResidueField A'](G) := by
    exact
      projectivePositiveImage_subset_scalarExtensionPositiveImage
        (A := A') (K' := K') (G := G) hx
  have hrange :
      n • x ∈
        (projectiveGrothendieckScalarExtensionHom A' K' :
          P₀[IsLocalRing.ResidueField A'](G) →+ R₀[K'](G)).range := by
    rcases hpositive with ⟨y, _hy, hyx⟩
    exact ⟨y, hyx⟩
  have hrange_comp :
      n • x ∈
        ((finiteRepGrothendieckScalarExtensionHom K' K' G).comp
          (projectiveGrothendieckScalarExtensionHom A' K') :
            P₀[IsLocalRing.ResidueField A'](G) →+ R₀[K'](G)).range := by
    -- The identity scalar-extension map lets Theorem `16-16.2-2` read the same range witness.
    rcases hrange with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [AddMonoidHom.comp_apply, finiteRepGrothendieckScalarExtensionHom_self] using hy
  have hzero_n :
      ∀ g : G, ¬ IsPRegular p g →
        finiteRepGrothendieckCharacter K' G (n • x) g = 0 :=
    (mem_projectiveScalarExtensionOverExtension_range_iff_valuedInBaseField_zero_on_pSingular
      (A := A') (K := K') (K' := K') (G := G) (p := p) (n • x)).1 hrange_comp |>.2
  intro g hg
  have hmap :
      finiteRepGrothendieckCharacter K' G (n • x) =
        n • finiteRepGrothendieckCharacter K' G x := by
    exact map_nsmul (finiteRepGrothendieckCharacter K' G) n x
  have hnchar :
      ((n : ℕ) • finiteRepGrothendieckCharacter K' G x : R[K'](G)) g = 0 := by
    rw [← hmap]
    exact hzero_n g hg
  have hmul :
      (n : K') * finiteRepGrothendieckCharacter K' G x g = 0 := by
    simpa [nsmul_eq_mul] using hnchar
  have hn_ne : (n : K') ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hn))
  exact (mul_eq_zero.mp hmul).resolve_left hn_ne

/-- Helper for Proposition 16-16.3-2: the source-facing base-change map over the actual fraction
field `K` is injective. -/
private theorem projective_baseChange_injective
    [HenselianLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [PerfectField (IsLocalRing.ResidueField A)] :
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

/-- Helper for Proposition 16-16.3-2: the source-facing base-change map remains injective after
passing from `K` to the finite extension field `K'`. -/
private theorem projective_baseChange_injective_over_extension
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Injective (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K') := by
  -- Direct base change to `K'` factors as base change to `K` followed by ordinary scalar
  -- extension, and both factors are injective.
  intro x y hxy
  apply projective_baseChange_injective (A := A) (K := K) (G := G)
  apply finiteRepGrothendieckScalarExtensionHom_injective_local
    (K := K) (K' := K') (G := G)
  have hx :=
    congrArg (fun f : P₀[A](G) →+ R₀[K'](G) => f x)
      (finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq
        (A := A) (K := K) (K' := K') (G := G))
  have hy :=
    congrArg (fun f : P₀[A](G) →+ R₀[K'](G) => f y)
      (finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq
        (A := A) (K := K) (K' := K') (G := G))
  calc
    finiteRepGrothendieckScalarExtensionHom K K' G
        (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K x) =
        projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' x := by
          exact hx
    _ = projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' y := hxy
    _ = finiteRepGrothendieckScalarExtensionHom K K' G
        (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K y) := by
          exact hy.symm

/-- Helper for Proposition 16-16.3-2: restricting scalars preserves the identity endomorphism. -/
private theorem restrictScalarsEnd_map_one_local
    {K : Type u} [Field K]
    {L : Type u} [Field L] [Algebra K L]
    {V : Type u} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    LinearMap.restrictScalars K (1 : Module.End L V) = (1 : Module.End K V) := by
  ext x
  rfl

/-- Helper for Proposition 16-16.3-2: restricting scalars preserves composition of
endomorphisms. -/
private theorem restrictScalarsEnd_map_mul_local
    {K : Type u} [Field K]
    {L : Type u} [Field L] [Algebra K L]
    {V : Type u} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (f g : Module.End L V) :
    LinearMap.restrictScalars K (f * g) =
      LinearMap.restrictScalars K f * LinearMap.restrictScalars K g := by
  ext x
  rfl

/-- Helper for Proposition 16-16.3-2: a representation over `L` viewed as one over `K`. -/
private def restrictScalarsRepresentation_local
    {K : Type u} [Field K]
    {L : Type u} [Field L] [Algebra K L]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) : Representation K G V :=
  { toFun := fun g ↦ LinearMap.restrictScalars K (ρ g)
    map_one' := by
      ext x
      simpa using congrArg (fun f : Module.End L V ↦ f x) ρ.map_one
    map_mul' := by
      intro g h
      ext x
      simpa using congrArg (fun f : Module.End L V ↦ f x) (ρ.map_mul g h) }

/-- Helper for Proposition 16-16.3-2: the trace of a flattened block matrix is the trace of the
matrix of block traces. -/
private theorem matrix_trace_comp_local
    {I J R : Type u} [Fintype I] [Fintype J] [Semiring R]
    (A : Matrix I I (Matrix J J R)) :
    Matrix.trace (Matrix.comp I I J J R A) = Matrix.trace (A.trace) := by
  classical
  simp only [Matrix.trace]
  calc
    ∑ x : I × J, A x.1 x.1 x.2 x.2 = ∑ i, ∑ j, A i i j j := by
      simpa [Finset.univ_product_univ] using
        (Finset.sum_product (s := (Finset.univ : Finset I)) (t := (Finset.univ : Finset J))
          (f := fun x : I × J ↦ A x.1 x.1 x.2 x.2))
    _ = ∑ j, ∑ i, A i i j j := by
      rw [Finset.sum_comm]
    _ = ∑ j, (∑ i, A i i) j j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      calc
        ∑ i, A i i j j = (∑ i, A i i j) j := by
          exact (Finset.sum_apply (a := j) (s := (Finset.univ : Finset I))
            (g := fun i ↦ A i i j)).symm
        _ = (∑ i, A i i) j j := by
          exact (congrFun (Finset.sum_apply (a := j) (s := (Finset.univ : Finset I))
            (g := fun i ↦ A i i)) j).symm
    _ = Matrix.trace (A.trace) := by
      rfl

/-- Helper for Proposition 16-16.3-2: the character of the restricted representation is the
pointwise field trace of the original character. -/
private theorem trace_character_restrictScalars_eq_fieldTrace_local
    {K : Type u} [Field K]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) :
    (restrictScalarsRepresentation_local (K := K) (L := L) (G := G) ρ).character g =
      Algebra.trace K L (ρ.character g) := by
  classical
  let bK := Module.Free.chooseBasis K L
  let bV := Module.Free.chooseBasis L V
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex K L)
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex L V)
  change LinearMap.trace K V ((ρ g).restrictScalars K) =
    Algebra.trace K L (LinearMap.trace L V (ρ g))
  rw [LinearMap.trace_eq_matrix_trace K (bK.smulTower' bV)]
  rw [LinearMap.trace_eq_matrix_trace L bV]
  rw [Algebra.trace_eq_matrix_trace bK]
  rw [LinearMap.restrictScalars_toMatrix bK bV]
  let M := (ρ g).toMatrix bV bV
  let A := M.map (Algebra.leftMulMatrix bK)
  change Matrix.trace (Matrix.comp _ _ _ _ _ A) =
    Matrix.trace (Algebra.leftMulMatrix bK (Matrix.trace M))
  rw [matrix_trace_comp_local]
  congr
  ext i j
  simp [A, M, Matrix.trace]

/-- Helper for Proposition 16-16.3-2: the coefficient-restricted `A[G]`-action is compatible
with the coefficient `A`-action. -/
private theorem coefficient_compHom_isScalarTower
    {M : Type u} [AddCommGroup M] [Module A' M] [Module (MonoidAlgebra A' G) M]
    [IsScalarTower A' (MonoidAlgebra A' G) M] :
    let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
      MonoidAlgebra.mapRingHom G (algebraMap A A')
    letI : Module A M := Module.compHom M (algebraMap A A')
    letI : Module (MonoidAlgebra A G) M := Module.compHom M σ
    IsScalarTower A (MonoidAlgebra A G) M := by
  let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
    MonoidAlgebra.mapRingHom G (algebraMap A A')
  letI : Module A M := Module.compHom M (algebraMap A A')
  letI : Module (MonoidAlgebra A G) M := Module.compHom M σ
  exact IsScalarTower.of_algebraMap_smul fun a x ↦ by
    have hσalg : σ ((algebraMap A (MonoidAlgebra A G)) a) =
        algebraMap A' (MonoidAlgebra A' G) (algebraMap A A' a) := by
      simpa [σ] using
        congrArg (fun f : A →+* MonoidAlgebra A' G => f a)
          (MonoidAlgebra.mapRingHom_comp_algebraMap
            (M := G) (f := algebraMap A A'))
    change σ ((algebraMap A (MonoidAlgebra A G)) a) • x = a • x
    rw [hσalg]
    change (algebraMap A' (MonoidAlgebra A' G) (algebraMap A A' a)) • x =
      (algebraMap A A' a) • x
    exact IsScalarTower.algebraMap_smul
      (A := MonoidAlgebra A' G) (M := M) (algebraMap A A' a) x

/-- Helper for Proposition 16-16.3-2: restrict a finite projective `A'[G]`-module along
`A[G] → A'[G]`. The freeness hypothesis is the formal version of Serre's finite-free extension
of coefficient group algebras. -/
private noncomputable def coefficientRestrictedProjectiveOwner
    (hfreeAG :
      let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
        MonoidAlgebra.mapRingHom G (algebraMap A A')
      letI : Module (MonoidAlgebra A G) (MonoidAlgebra A' G) :=
        Module.compHom (MonoidAlgebra A' G) σ
      Module.Free (MonoidAlgebra A G) (MonoidAlgebra A' G))
    (P' : FiniteProjectiveGroupAlgebraModule A' G) :
    FiniteProjectiveGroupAlgebraModule A G := by
  let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
    MonoidAlgebra.mapRingHom G (algebraMap A A')
  letI : Module (MonoidAlgebra A G) (MonoidAlgebra A' G) :=
    Module.compHom (MonoidAlgebra A' G) σ
  haveI : Module.Free (MonoidAlgebra A G) (MonoidAlgebra A' G) := hfreeAG
  letI : Module (MonoidAlgebra A G) P'.V := Module.compHom P'.V σ
  letI : Module A P'.V := Module.compHom P'.V (algebraMap A (MonoidAlgebra A G))
  letI : IsScalarTower A (MonoidAlgebra A G) P'.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower A A' P'.V := by
    refine ⟨?_⟩
    intro a a' m
    have hσalg : σ ((algebraMap A (MonoidAlgebra A G)) a) =
        algebraMap A' (MonoidAlgebra A' G) (algebraMap A A' a) := by
      simpa [σ] using
        congrArg (fun f : A →+* MonoidAlgebra A' G => f a)
          (MonoidAlgebra.mapRingHom_comp_algebraMap
            (M := G) (f := algebraMap A A'))
    rw [Algebra.smul_def]
    change ((algebraMap A A' a) * a') • m =
      σ ((algebraMap A (MonoidAlgebra A G)) a) • (a' • m)
    rw [hσalg]
    rw [← IsScalarTower.algebraMap_smul (A := MonoidAlgebra A' G) (M := P'.V) a' m]
    rw [← smul_assoc]
    rw [smul_eq_mul]
    rw [← map_mul]
    exact (IsScalarTower.algebraMap_smul (A := MonoidAlgebra A' G) (M := P'.V)
      ((algebraMap A A' a) * a') m).symm
  haveI : Module.Finite A P'.V := Module.Finite.trans A' P'.V
  haveI : Module.Finite (MonoidAlgebra A G) P'.V :=
    Module.Finite.of_restrictScalars_finite A (MonoidAlgebra A G) P'.V
  haveI : Module.Projective (MonoidAlgebra A G) P'.V := by
    letI : IsScalarTower (MonoidAlgebra A G) (MonoidAlgebra A' G) P'.V := by
      refine ⟨?_⟩
      intro r s x
      change (σ r * s) • x = σ r • s • x
      rw [mul_smul]
    exact
      projective_restrictScalars_of_free_hom
        (R := MonoidAlgebra A G) (S := MonoidAlgebra A' G) (σ := σ) (M := P'.V)
        (fun (r : MonoidAlgebra A G) (s : MonoidAlgebra A' G) => rfl)
  exact ⟨FGModuleCat.of (MonoidAlgebra A G) P'.V, inferInstance⟩

/-- Helper for Proposition 16-16.3-2: restricting a projective `A'[G]`-module along
`A[G] → A'[G]` and comparing characters produces the expected
`[K' : K]`-multiple in `R_K'(G)`. -/
private theorem restricted_projective_witness_class_eq_extension_degree_nsmul
    (hfreeAG :
      let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
        MonoidAlgebra.mapRingHom G (algebraMap A A')
      letI : Module (MonoidAlgebra A G) (MonoidAlgebra A' G) :=
        Module.compHom (MonoidAlgebra A' G) σ
      Module.Free (MonoidAlgebra A G) (MonoidAlgebra A' G))
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    {n : ℕ} (P' : FiniteProjectiveGroupAlgebraModule A' G)
    (hP' : projectiveGrothendieckBaseChangeHom (A := A') (G := G) K' [P']ₚ₀ = n • x) :
    ∃ E : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀ =
        ((n * Module.finrank K K' : ℕ) • x) := by
  classical
  let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
    MonoidAlgebra.mapRingHom G (algebraMap A A')
  letI : Module (MonoidAlgebra A G) (MonoidAlgebra A' G) :=
    Module.compHom (MonoidAlgebra A' G) σ
  haveI : Module.Free (MonoidAlgebra A G) (MonoidAlgebra A' G) := hfreeAG
  letI : Module (MonoidAlgebra A G) P'.V := Module.compHom P'.V σ
  letI : Module A P'.V := Module.compHom P'.V (algebraMap A (MonoidAlgebra A G))
  letI : IsScalarTower A (MonoidAlgebra A G) P'.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower A A' P'.V := by
    refine ⟨?_⟩
    intro a a' y
    have hσalg : σ ((algebraMap A (MonoidAlgebra A G)) a) =
        algebraMap A' (MonoidAlgebra A' G) (algebraMap A A' a) := by
      simpa [σ] using
        congrArg (fun f : A →+* MonoidAlgebra A' G => f a)
          (MonoidAlgebra.mapRingHom_comp_algebraMap
            (M := G) (f := algebraMap A A'))
    rw [Algebra.smul_def]
    change ((algebraMap A A' a) * a') • y =
      σ ((algebraMap A (MonoidAlgebra A G)) a) • (a' • y)
    rw [hσalg]
    rw [← IsScalarTower.algebraMap_smul (A := MonoidAlgebra A' G) (M := P'.V) a' y]
    rw [← smul_assoc]
    rw [smul_eq_mul]
    rw [← map_mul]
    exact (IsScalarTower.algebraMap_smul (A := MonoidAlgebra A' G) (M := P'.V)
      ((algebraMap A A' a) * a') y).symm
  haveI : Module.Finite A P'.V := Module.Finite.trans A' P'.V
  haveI : Module.Finite (MonoidAlgebra A G) P'.V :=
    Module.Finite.of_restrictScalars_finite A (MonoidAlgebra A G) P'.V
  haveI : Module.Projective (MonoidAlgebra A G) P'.V := by
    letI : IsScalarTower (MonoidAlgebra A G) (MonoidAlgebra A' G) P'.V := by
      refine ⟨?_⟩
      intro r s y
      change (σ r * s) • y = σ r • s • y
      rw [mul_smul]
    exact
      projective_restrictScalars_of_free_hom
        (R := MonoidAlgebra A G) (S := MonoidAlgebra A' G) (σ := σ) (M := P'.V)
        (fun (r : MonoidAlgebra A G) (s : MonoidAlgebra A' G) => rfl)
  let E : FiniteProjectiveGroupAlgebraModule A G :=
    ⟨FGModuleCat.of (MonoidAlgebra A G) P'.V, inferInstance⟩
  refine ⟨E, ?_⟩
  rw [← (finiteRepGrothendieckCharacter_eq_iff (K := K') (G := G))]
  ext g
  rw [map_nsmul]
  have hchar_range := hchar
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hchar_range
  rcases hchar_range with ⟨χK, hχK⟩
  have hxg :
      algebraMap K K' (χK g) =
        (finiteRepGrothendieckCharacter K' G x : G → K') g := by
    simpa using congrFun hχK g
  have hP'char :
      (P'.scalarExtension K').character g =
        (n : K') * (finiteRepGrothendieckCharacter K' G x : G → K') g := by
    have hp0a := congrArg (finiteRepGrothendieckCharacter K' G) hP'
    have hp0b :
        (finiteRepGrothendieckCharacter K' G)
            (projectiveGrothendieckBaseChangeHom (A := A') (G := G) K' [P']ₚ₀) =
          (finiteRepGrothendieckCharacter K' G) (n • x) := by
      simpa [projectiveGrothendieckBaseChangeHom_projectiveClass_eq] using hp0a
    have hp0c :
        (finiteRepGrothendieckCharacter K' G) (n • x) =
          n • finiteRepGrothendieckCharacter K' G x :=
      map_nsmul (finiteRepGrothendieckCharacter K' G) n x
    have hp := congrArg (fun χ : R[K'](G) => (χ : G → K') g) (hp0b.trans hp0c)
    simpa [projectiveGrothendieckBaseChangeHom_projectiveClass_eq,
      finiteRepGrothendieckCharacter_class, nsmul_eq_mul] using hp
  have hEtrace :
      (E.scalarExtension K).character g =
        Algebra.trace K K' ((P'.scalarExtension K').character g) := by
    let ρres : Representation K G (TensorProduct A' K' P'.V) :=
      restrictScalarsRepresentation_local (K := K) (L := K') (G := G)
        ((P'.scalarExtension K').ρ)
    let ρA' : Representation A' G P'.V := Representation.ofModule' P'.V
    let ρA : Representation A G P'.V := Representation.ofModule' P'.V
    let ρEK : Representation K G (TensorProduct A K P'.V) :=
      Representation.scalarExtension ρA
    have hρA_apply : ∀ t m, ρA t m = ρA' t m := by
      intro t m
      change σ (MonoidAlgebra.single t (1 : A)) • m =
        (MonoidAlgebra.single t (1 : A')) • m
      rw [MonoidAlgebra.mapRingHom_single]
      simp
    let eK : TensorProduct A K P'.V ≃ₗ[K] TensorProduct A' K' P'.V :=
      (Algebra.IsPushout.cancelBaseChange A K A' K' P'.V).symm
    let eSource : (E.scalarExtension K).V ≃ₗ[K] TensorProduct A K P'.V :=
      by
        dsimp [E, FiniteProjectiveGroupAlgebraModule.scalarExtension, ρEK, ρA]
        exact LinearEquiv.refl K (TensorProduct A K P'.V)
    have hEquiv : Representation.Equiv (E.scalarExtension K).ρ ρres := by
      refine Representation.Equiv.mk (eSource.trans eK) ?_
      intro t
      refine LinearMap.ext (fun z : (E.scalarExtension K).V => ?_)
      have hsource :
          eSource (((E.scalarExtension K).ρ t) z) = ρEK t (eSource z) := by
        rfl
      have hraw : ∀ y : TensorProduct A K P'.V, eK (ρEK t y) = ρres t (eK y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero =>
            simp [ρres, restrictScalarsRepresentation_local]
        | tmul c m =>
            calc
              eK (ρEK t (c ⊗ₜ[A] m)) =
                  eK (c ⊗ₜ[A] ρA t m) := by
                    change eK ((LinearMap.baseChange K (ρA t)) (c ⊗ₜ[A] m)) =
                      eK (c ⊗ₜ[A] ρA t m)
                    rw [LinearMap.baseChange_tmul]
              _ = (algebraMap K K') c ⊗ₜ[A'] ρA t m := by
                    simp [eK, Algebra.IsPushout.cancelBaseChange_symm_tmul]
              _ = (algebraMap K K') c ⊗ₜ[A'] ρA' t m := by
                    rw [hρA_apply t m]
              _ = ρres t (eK (c ⊗ₜ[A] m)) := by
                    change (algebraMap K K') c ⊗ₜ[A'] ρA' t m =
                      ρres t ((Algebra.IsPushout.cancelBaseChange A K A' K' P'.V).symm
                        (c ⊗ₜ[A] m))
                    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
                    change (algebraMap K K') c ⊗ₜ[A'] ρA' t m =
                      (LinearMap.baseChange K' (ρA' t))
                        ((algebraMap K K') c ⊗ₜ[A'] m)
                    rw [LinearMap.baseChange_tmul]
        | add y₁ y₂ hy₁ hy₂ =>
            simpa [map_add] using congrArg₂ HAdd.hAdd hy₁ hy₂
      calc
        (eSource.trans eK) (((E.scalarExtension K).ρ t) z) =
            eK (ρEK t (eSource z)) := by
              simpa [LinearEquiv.trans_apply] using congrArg eK hsource
        _ = ρres t ((eSource.trans eK) z) := by
              simpa [LinearEquiv.trans_apply] using hraw (eSource z)
    calc
      (E.scalarExtension K).character g = ρres.character g := by
        exact congrFun (Representation.char_iso hEquiv) g
      _ = Algebra.trace K K' ((P'.scalarExtension K').character g) := by
        exact trace_character_restrictScalars_eq_fieldTrace_local
          (K := K) (L := K') (G := G) ((P'.scalarExtension K').ρ) g
  calc
    (finiteRepGrothendieckCharacter K' G
        (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀) : G → K') g
        =
      algebraMap K K' ((E.scalarExtension K).character g) := by
        have hfactor :=
          congrArg
            (fun f : P₀[A](G) →+ R₀[K'](G) => f [E]ₚ₀)
            (finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq
              (A := A) (K := K) (K' := K') (G := G))
        have hfactor' :
            finiteRepGrothendieckScalarExtensionHom K K' G
              (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K [E]ₚ₀) =
              projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀ := by
          simpa [AddMonoidHom.comp_apply] using hfactor
        rw [← hfactor']
        simpa [projectiveGrothendieckBaseChangeHom_projectiveClass_eq] using
          finiteRepGrothendieckCharacter_scalarExtensionHom_apply_local
            (K := K) (K' := K') (G := G)
            (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K [E]ₚ₀) g
    _ = algebraMap K K' (Algebra.trace K K' ((P'.scalarExtension K').character g)) := by
        rw [hEtrace]
    _ = ((n * Module.finrank K K' : ℕ) • finiteRepGrothendieckCharacter K' G x : R[K'](G)) g := by
        rw [hP'char, ← hxg]
        have htrace_arg :
            (n : K') * algebraMap K K' (χK g) =
              algebraMap K K' ((n : K) * χK g) := by
          simp
        rw [htrace_arg, Algebra.trace_algebraMap]
        simpa [hxg, nsmul_eq_mul, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Proposition 16-16.3-2: if `K' / K` is finite, the ordinary character of
`x ∈ R_K'(G)` is `K`-valued, and some positive multiple of `x` lies in the image
`eA' '' P⁺[A'](G)`, then `x` itself lies in the source-facing positive image
`eA '' P⁺[A](G)`. This is the bridge form of the canonical Chapter `16` scalar-extension
criterion. -/
theorem mem_projectivePositiveImage_of_character_valuedInBaseField
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    -- Serre's standing Chapter-16 hypothesis: the residue field is algebraically closed.  This is
    -- the setting of Theorem `16-16.2-1`/`16-16.2-2` invoked below (over `A` and over `A'`).  For
    -- the finite local extension `A → A'`, `ResidueField A'` is a finite extension of the
    -- algebraically closed `ResidueField A`, hence again algebraically closed; it is listed
    -- explicitly because the formalization does not derive residue-field finiteness automatically.
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAlgClosed (IsLocalRing.ResidueField A')]
    (hfreeAG :
      let σ : MonoidAlgebra A G →+* MonoidAlgebra A' G :=
        MonoidAlgebra.mapRingHom G (algebraMap A A')
      letI : Module (MonoidAlgebra A G) (MonoidAlgebra A' G) :=
        Module.compHom (MonoidAlgebra A' G) σ
      Module.Free (MonoidAlgebra A G) (MonoidAlgebra A' G))
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    (hnsmul : ∃ n : ℕ, 1 ≤ n ∧ n • x ∈ eA' '' P⁺[A'](G))
    : x ∈ eA '' P⁺[A](G) := by
  -- Route correction: follow Serre's proof. First get p-singular vanishing from the positive
  -- `A'`-multiple, then use Theorem `16-16.2-2` to descend `x` to a projective class over `A`.
  -- `K` is characteristic `0` with enough roots of unity for the exponent of `G`, so it is a
  -- splitting field: Serre's Theorem 24 gives the quasisplit identity `R[K](G) = R̄[K](G)`, the
  -- `Fact` consumed by Theorem `16-16.2-2` over `A`.
  haveI : Fact (R[K](G) = R̄[K](G)) :=
    ⟨characterRing_eq_overlineCharacterRing_of_isSplittingField⟩
  rcases hnsmul with ⟨n, hn, hxpositive⟩
  have hxzero :
      ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 :=
    character_eq_zero_on_pSingular_of_nsmul_mem_projectivePositiveImage
      (A := A) (A' := A') (K := K) (K' := K') (G := G) (p := p) hn hxpositive
  have hxrange :
      x ∈ ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
        (projectiveGrothendieckScalarExtensionHom A K) : P_k(G) →+ R₀[K'](G)).range :=
    (mem_projectiveScalarExtensionOverExtension_range_iff_valuedInBaseField_zero_on_pSingular
      (A := A) (K := K) (K' := K') (G := G) (p := p) x).2 ⟨hchar, hxzero⟩
  rcases hxrange with ⟨z, hz⟩
  let yA : P₀[A](G) :=
    (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm z
  have hyA_eq :
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' yA = x := by
    -- Rewrite direct base change to `K'` as base change to `K` followed by ordinary scalar
    -- extension, then use the range witness `z`.
    have hcomp :=
      congrArg (fun f : P₀[A](G) →+ R₀[K'](G) => f yA)
        (finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq
          (A := A) (K := K) (K' := K') (G := G))
    calc
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' yA =
          finiteRepGrothendieckScalarExtensionHom K K' G
            (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K yA) := by
            exact hcomp.symm
      _ = finiteRepGrothendieckScalarExtensionHom K K' G
            ((projectiveGrothendieckScalarExtensionHom A K) z) := by
            rw [projectiveGrothendieckScalarExtensionHom_apply]
      _ = x := by
            simpa [AddMonoidHom.comp_apply] using hz
  -- Unpack the positive `A'`-witness so Serre's restriction-of-scalars comparison can be applied.
  rcases hxpositive with ⟨w, hwpositive, hwx⟩
  rcases (mem_projectivePositiveSubset_iff A' G).1 hwpositive with ⟨P', hP'w⟩
  have hP' :
      projectiveGrothendieckBaseChangeHom (A := A') (G := G) K' [P']ₚ₀ = n • x := by
    rw [hP'w]
    exact hwx
  obtain ⟨E, hE⟩ :=
    restricted_projective_witness_class_eq_extension_degree_nsmul
      (A := A) (A' := A') (K := K) (K' := K') (G := G) hfreeAG x hchar P' hP'
  let m : ℕ := n * Module.finrank K K'
  have hE_class :
      [E]ₚ₀ = m • yA := by
    -- Injectivity of direct base change to `K'` turns Serre's character comparison into equality
    -- in `P_A(G)`.
    apply projective_baseChange_injective_over_extension
      (A := A) (K' := K') (G := G) K
    calc
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀ =
          m • x := by
          simpa [m] using hE
      _ = m • projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' yA := by
          rw [hyA_eq]
      _ = projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' (m • yA) := by
          rw [map_nsmul]
  have hm : 1 ≤ m := by
    have hnpos : 0 < n := Nat.succ_le_iff.mp hn
    have hNpos : 0 < Module.finrank K K' :=
      Module.finrank_pos (R := K) (M := K')
    exact Nat.succ_le_iff.mpr (Nat.mul_pos hnpos hNpos)
  have hmy_positive : m • yA ∈ P⁺[A](G) := by
    -- The class `m • yA` is represented by the restricted projective module `E`.
    rw [← hE_class]
    exact (mem_projectivePositiveSubset_iff A G).2 ⟨E, rfl⟩
  have hyA_positive : yA ∈ P⁺[A](G) :=
    mem_projectivePositiveSubset_of_nsmul_mem
      (A := A) (G := G) (x := yA) (n := m) hm hmy_positive
  exact ⟨yA, hyA_positive, hyA_eq⟩

end

end Representation
