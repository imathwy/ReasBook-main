import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_134_1
import stacks_proof.stacks_project.Chap15.Lemma_15_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

noncomputable section

universe u x y

/- Domain triage:
* primary domain: underived base change for presentationwise naive cotangent complexes and their
  degree `-1` and `0` homology in commutative algebra;
* sampled owner declarations:
  - `Presentation.baseChange`,
  - `Presentation.baseChangeFromBaseChange`,
  - `Extension.naiveCotangentChainComplex`,
  - `Extension.CotangentSpace.map_comp_cotangentComplex`,
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  - `KaehlerDifferential.tensorKaehlerEquivBase`;
* best owner abstraction: the source-facing owner is the comparison chain map between the
  canonical two-term complexes
  `P.toExtension.baseChange.naiveCotangentChainComplex` and
  `(P.baseChange R').toExtension.naiveCotangentChainComplex`; the owner-level public comparison on
  `H^{-1}` is the canonical composite
  `H1Cotangent.baseChangeComparison R R' S`,
  `S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S'`,
  the degree `0` owner is already the canonical equivalence
  `KaehlerDifferential.tensorKaehlerEquivBase R R' S`;
* primitive data: the ring maps `R → S`, `R → R'`, and the chosen presentation `P`;
* derived API: the source-facing surjectivity theorem for the explicit presentation-level
  `H^{-1}` comparison composite, the owner-level comparison
  `H1Cotangent.baseChangeComparison R R' S` and its surjectivity statement, and direct reuse of
  `KaehlerDifferential.tensorKaehlerEquivBase` for degree `0`.

Source/core/bridge triage:
* `source-facing`: the comparison `NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')` for a chosen
  presentation `P`;
* `core/canonical`: `Presentation.baseChange`, `Presentation.baseChangeFromBaseChange`,
  `Extension.naiveCotangentChainComplex`, `H1Cotangent.baseChangeComparison`, and
  `KaehlerDifferential.tensorKaehlerEquivBase`;
* `bridge/view`: the explicit presentation-level composite of
  `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  `H1Cotangent.map`, and `equivH1Cotangent.symm` used in the surjectivity theorem below.
-/

section

variable {R S R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable {ι : Type x} {σ : Type y}

local notation "S'" => R' ⊗[R] S

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

variable (R R' S)

/-- Helper for Lemma 15.86.2: the source-side map from the tensorized `H^{-1}` term of
`NL_{S/R}` into `H^{-1}(L_{S'/R})`. This is the first half of the owner-level base-change
comparison before changing the base ring from `R` to `R'`. -/
noncomputable abbrev baseChangeSourceMap :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R S' :=
  -- First extend scalars on `H₁(L_{S/R})`, then apply the owner change-of-target map over `R`.
  LinearMap.liftBaseChange S' (H1Cotangent.map R R S S')

/-- Helper for Lemma 15.86.2: the degree `0` comparison
`S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R']`. -/
noncomputable abbrev baseChangeDegreeZeroComparison :
    S' ⊗[S] Ω[S⁄R] →ₗ[S'] Ω[S'⁄R'] :=
  -- First base-change differentials from `R` to `S'`, then change the source ring to `R'`.
  (KaehlerDifferential.map R R' S' S').comp
    (KaehlerDifferential.mapBaseChange R S S')

/-- Helper for Lemma 15.86.2: the degree `0` comparison is injective because it is the linear map
underlying the canonical Kähler base-change equivalence. -/
theorem baseChangeDegreeZeroComparison_injective :
    Function.Injective (baseChangeDegreeZeroComparison R R' S) := by
  -- TODO: restate the exact owner specialization of `tensorKaehlerEquivBase` used here and
  -- identify its underlying linear map with `baseChangeDegreeZeroComparison`.
  sorry

/-- Helper for Lemma 15.86.2: tensoring the self-presentation kernel of `S/R` up to `S'` still
lands in the kernel of the tensorized self-presentation differential. -/
theorem self_presentation_source_to_kernel_mem
    (x : S' ⊗[S] H1Cotangent R S) :
    (((LinearMap.ker (Generators.self R S).toExtension.cotangentComplex).subtype).baseChange S'
        ((LinearMap.baseChange S'
          ((Generators.self R S).equivH1Cotangent.symm.toLinearMap)) x)) ∈
      LinearMap.ker
        (LinearMap.baseChange S' (Generators.self R S).toExtension.cotangentComplex) := by
  let d := (Generators.self R S).toExtension.cotangentComplex
  let i : LinearMap.ker d →ₗ[S] (Generators.self R S).toExtension.Cotangent :=
    (LinearMap.ker d).subtype
  have hzero : d ∘ₗ i = 0 := by
    -- The subtype inclusion of a kernel always composes trivially with the ambient map.
    ext y
    exact y.2
  have hbase :
      (LinearMap.baseChange S' d) ∘ₗ (LinearMap.baseChange S' i) = 0 := by
    -- Tensor the zero composite once, then rewrite it as a composite of tensorized maps.
    have hbase' : LinearMap.baseChange S' (d ∘ₗ i) = 0 := by
      simpa [hzero] using congrArg (LinearMap.baseChange S') hzero
    rw [← LinearMap.baseChange_comp]
    exact hbase'
  rw [LinearMap.mem_ker]
  -- Apply the tensorized zero-composite identity to the transported source element.
  simpa [d, i, LinearMap.comp_apply] using
    LinearMap.congr_fun hbase
      ((LinearMap.baseChange S'
        ((Generators.self R S).equivH1Cotangent.symm.toLinearMap)) x)

/-- Helper for Lemma 15.86.2: the tensorized owner source term maps canonically into the kernel
of the tensorized self-presentation differential. -/
noncomputable def self_presentation_source_to_kernel_baseChange :
    S' ⊗[S] H1Cotangent R S →ₗ[S']
      LinearMap.ker (LinearMap.baseChange S' (Generators.self R S).toExtension.cotangentComplex) :=
  LinearMap.codRestrict
    (LinearMap.ker (LinearMap.baseChange S' (Generators.self R S).toExtension.cotangentComplex))
    ((((LinearMap.ker (Generators.self R S).toExtension.cotangentComplex).subtype).baseChange S')
      ∘ₗ
        (LinearMap.baseChange S' ((Generators.self R S).equivH1Cotangent.symm.toLinearMap)))
    (self_presentation_source_to_kernel_mem (R := R) (R' := R') (S := S))

/-- Helper for Lemma 15.86.2: on the self-presentation of `S/R`, the composite-presentation map
computes the owner change-of-target map `H1Cotangent.map R R S S'`. -/
theorem self_presentation_owner_map_apply (x : H1Cotangent R S) :
    ((Generators.self S S').comp (Generators.self R S)).equivH1Cotangent
        (Extension.H1Cotangent.map
          (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom)
          ((Generators.self R S).equivH1Cotangent.symm x)) =
      H1Cotangent.map R R S S' x := by
  -- Unfold only the linear-equivalence wrappers; the rest is functoriality of `H₁`.
  simp [H1Cotangent.map, Generators.equivH1Cotangent, Generators.H1Cotangent.equiv,
    Extension.H1Cotangent.equiv]
  have htoComp :
      Extension.H1Cotangent.map
          (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom)
          (Extension.H1Cotangent.map
            ((Generators.defaultHom (Generators.self R S) (Generators.self R S)).toExtensionHom)
            x) =
        Extension.H1Cotangent.map
          (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom) x := by
    -- The inverse half of the self-presentation equivalence is another map between the same
    -- self-presentations, hence it is identified with the identity by `map_eq`.
    have hcomp :
        Extension.H1Cotangent.map
            ((((Generators.self S S').toComp (Generators.self R S)).toExtensionHom).comp
              ((Generators.defaultHom (Generators.self R S)
                (Generators.self R S)).toExtensionHom))
            x =
          Extension.H1Cotangent.map
            (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom) x := by
      exact DFunLike.congr_fun (Extension.H1Cotangent.map_eq _ _) x
    exact
      (Extension.H1Cotangent.map_comp_apply
        ((Generators.defaultHom (Generators.self R S) (Generators.self R S)).toExtensionHom)
        (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom)
        x).symm.trans hcomp
  rw [htoComp]
  have hcomp :
      Extension.H1Cotangent.map
          (((Generators.defaultHom ((Generators.self S S').comp (Generators.self R S))
                (Generators.self R S')).toExtensionHom).comp
            (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom))
          x =
        Extension.H1Cotangent.map
          ((Generators.defaultHom (Generators.self R S) (Generators.self R S')).toExtensionHom)
          x := by
    -- The composite presentation morphism and the canonical direct owner map have the same source
    -- and target, so `map_eq` identifies their `H₁` actions.
    exact DFunLike.congr_fun (Extension.H1Cotangent.map_eq _ _) x
  exact
    (Extension.H1Cotangent.map_comp_apply
      (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom)
      ((Generators.defaultHom ((Generators.self S S').comp (Generators.self R S))
        (Generators.self R S')).toExtensionHom)
      x).symm.trans hcomp

/-- Helper for Lemma 15.86.2: on the self-presentation of `S/R`, the presentation-level
comparison from the tensorized source kernel to `H^{-1}(L_{S'/R})` computes `baseChangeSourceMap`
after transporting the source into that kernel. -/
theorem self_presentation_left_map_eq_baseChangeSourceMap :
    (tensor_presentation_cotangent_h1_to_h1_cotangent S' (Generators.self R S)).comp
        (self_presentation_source_to_kernel_baseChange (R := R) (R' := R') (S := S)) =
      baseChangeSourceMap (R := R) (R' := R') (S := S) := by
  -- Compare the two `S'`-linear maps on pure tensors and extend by bilinearity.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [self_presentation_source_to_kernel_baseChange, baseChangeSourceMap]
  · intro s' y
    -- On a pure tensor, the self-presentation comparison is exactly the owner target-change map.
    change
      ((Generators.self S S').comp (Generators.self R S)).equivH1Cotangent
          (s' •
            Extension.H1Cotangent.map
              (((Generators.self S S').toComp (Generators.self R S)).toExtensionHom)
              ((Generators.self R S).equivH1Cotangent.symm y)) =
        s' • H1Cotangent.map R R S S' y
    rw [map_smul]
    exact congrArg (fun z : H1Cotangent R S' ↦ s' • z)
      (self_presentation_owner_map_apply (R := R) (R' := R') (S := S) y)
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 15.86.2: in a commuting square of linear maps, a cycle for the target
differential lifts to a cycle for the source differential if the degree `-1` map is surjective
and the degree `0` map is injective. -/
theorem exists_preimage_in_kernel_of_two_term_comparison
    {K M₁ M₀ N₁ N₀ : Type*}
    [CommRing K]
    [AddCommGroup M₁] [Module K M₁]
    [AddCommGroup M₀] [Module K M₀]
    [AddCommGroup N₁] [Module K N₁]
    [AddCommGroup N₀] [Module K N₀]
    (d : M₁ →ₗ[K] M₀)
    (d' : N₁ →ₗ[K] N₀)
    (f₁ : M₁ →ₗ[K] N₁)
    (f₀ : M₀ →ₗ[K] N₀)
    (hcomm : f₀ ∘ₗ d = d' ∘ₗ f₁)
    (hf₁ : Function.Surjective f₁)
    (hf₀ : Function.Injective f₀) :
    ∀ y, d' y = 0 → ∃ x, f₁ x = y ∧ d x = 0 := by
  intro y hy
  rcases hf₁ y with ⟨x, rfl⟩
  -- Apply injectivity in degree `0` to transport the cycle condition back across the square.
  have hx : d x = 0 := by
    apply hf₀
    have hfx : f₀ (d x) = 0 := by
      calc
        f₀ (d x) = d' (f₁ x) := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun g : M₁ →ₗ[K] N₀ ↦ g x) hcomm
        _ = 0 := hy
    simpa using hfx
  exact ⟨x, rfl, hx⟩

/- The canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})`. -/
noncomputable abbrev baseChangeComparison :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S' :=
  -- Apply the source-side comparison into `H₁(L_{S'/R})`, then change the base ring to `R'`.
  (map R R' S' S').comp (baseChangeSourceMap (R := R) (R' := R') (S := S))

/-- Helper for Lemma 15.86.2: the owner-level comparison is the composite of the source-side
base-change map into `H^{-1}(L_{S'/R})` and the change-of-base map into `H^{-1}(L_{S'/R'})`. -/
theorem baseChangeComparison_factorization :
    baseChangeComparison (R := R) (R' := R') (S := S) =
      (map R R' S' S').comp (baseChangeSourceMap (R := R) (R' := R') (S := S)) := by
  -- The owner comparison was defined by this factorization.
  rfl

/-- Helper for Lemma 15.86.2: after transporting the tensorized owner source into the
self-presentation kernel, the source-faithful presentation comparison computes the public owner
base-change map. -/
theorem self_presentation_comparison_comp_source_to_kernel_eq_baseChangeComparison :
    ((map R R' S' S' ∘ₗ
        tensor_presentation_cotangent_h1_to_h1_cotangent S' (Generators.self R S)).comp
          (self_presentation_source_to_kernel_baseChange (R := R) (R' := R') (S := S))) =
      baseChangeComparison (R := R) (R' := R') (S := S) := by
  -- First rewrite the source comparison through `baseChangeSourceMap`, then fold the public owner
  -- factorization back in.
  rw [LinearMap.comp_assoc]
  rw [self_presentation_left_map_eq_baseChangeSourceMap (R := R) (R' := R') (S := S)]

/-- Helper for Lemma 15.86.2: surjectivity of the self-presentation comparison after transporting
the owner source into the tensorized kernel is exactly surjectivity of the public owner map. -/
theorem self_presentation_comparison_surjective_iff_owner :
    Function.Surjective
        ((map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' (Generators.self R S)).comp
            (self_presentation_source_to_kernel_baseChange
              (R := R) (R' := R') (S := S))) ↔
      Function.Surjective (baseChangeComparison (R := R) (R' := R') (S := S)) := by
  -- This is only a transport step: the two maps agree by the self-presentation comparison lemma.
  simpa [self_presentation_comparison_comp_source_to_kernel_eq_baseChangeComparison
    (R := R) (R' := R') (S := S)]

/- Lemma 15.86.2 (in particular): the canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})` is surjective. -/
theorem baseChangeComparison_surjective
    :
    Function.Surjective (baseChangeComparison R R' S) := by
  -- Route correction: isolate the owner transport first, so the remaining blocker is only the
  -- source-faithful surjectivity of the self-presentation comparison on tensorized cycles.
  -- TODO: prove surjectivity of the actual self-presentation comparison on tensorized cycles by
  -- the underived two-term square whose degree `0` map is injective and degree `-1` map is
  -- surjective.
  sorry

end Algebra.H1Cotangent

namespace Algebra.Presentation

/-- Helper for Lemma 15.86.2: the genuine two-term base-change comparison on naive cotangent
complexes induced by `P.baseChangeFromBaseChange R'`. This is the source-faithful underived map
whose degreewise properties should drive the `H^{-1}` surjectivity argument. -/
noncomputable abbrev base_change_underived_chain_map
    (P : Presentation R S ι σ) :
    P.toExtension.baseChange.naiveCotangentChainComplex ⟶
      (Generators.baseChange R' P.toGenerators).toExtension.naiveCotangentChainComplex :=
  Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R')

/-- Helper for Lemma 15.86.2: the degree `0` component of the genuine underived base-change
comparison is the cotangent-space map induced by `P.baseChangeFromBaseChange R'`. -/
theorem base_change_underived_chain_map_degree_zero
    (P : Presentation R S ι σ) :
    ((base_change_underived_chain_map (R := R) (S := S) (R' := R') P).f 0).hom =
      Extension.CotangentSpace.map (P.baseChangeFromBaseChange R') := by
  -- The chain map was defined from the extension-level cotangent-space map in degree `0`.
  rfl

/-- Helper for Lemma 15.86.2: the degree `1` component of the genuine underived base-change
comparison is the ULift-packaged conormal map induced by `P.baseChangeFromBaseChange R'`. -/
theorem base_change_underived_chain_map_degree_one
    (P : Presentation R S ι σ) :
    ((base_change_underived_chain_map (R := R) (S := S) (R' := R') P).f 1).hom =
      ((ULift.moduleEquiv :
          ULift (Generators.baseChange R' P.toGenerators).toExtension.Cotangent ≃ₗ[S']
            (Generators.baseChange R' P.toGenerators).toExtension.Cotangent).symm.toLinearMap) ∘ₗ
        Extension.Cotangent.map (P.baseChangeFromBaseChange R') ∘ₗ
          ((ULift.moduleEquiv :
            ULift P.toExtension.baseChange.Cotangent ≃ₗ[S'] P.toExtension.baseChange.Cotangent)).toLinearMap := by
  -- The chain map was defined from the extension-level cotangent map in degree `1`.
  rfl

/-- Helper for Lemma 15.86.2: the canonical self-presentation of `S` over `R`, with variables
indexed by elements of `S` and relations indexed by the kernel of the canonical evaluation map
from `R[S]` to `S`. This packages the owner algebra `S` into the presentation language needed for
the presentation-level base-change comparison. -/
noncomputable def canonical_self_presentation :
    Presentation R S S (Generators.self R S).ker where
  __ := Generators.self R S
  relation i := i.1
  span_range_relation_eq_ker := by
    -- The displayed relations are literally all elements of the kernel ideal.
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      rcases hx with ⟨x, rfl⟩
      exact x.2
    · intro x hx
      -- Each kernel element appears as one of the indexed relations.
      exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Lemma 15.86.2: the presentation-level `H^{-1}` comparison map from
`H^{-1}(NL(P/R) ⊗[S] S')` to `H^{-1}(NL(P.baseChange R'/R'))`. -/
noncomputable abbrev generator_baseChangeComparison
    (P : Presentation R S ι σ) :
    LinearMap.ker (LinearMap.baseChange S' P.toGenerators.toExtension.cotangentComplex) →ₗ[S']
      (P.baseChange R').toGenerators.toExtension.H1Cotangent :=
  ((P.baseChange R').toGenerators.equivH1Cotangent.symm).toLinearMap ∘ₗ
    H1Cotangent.map R R' S' S' ∘ₗ
      tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators

/-- Helper for Lemma 15.86.2: a file-local name for the displayed presentation-level
`H^{-1}` comparison map. This isolates the remaining source-faithful blocker to proving
surjectivity of the comparison itself, rather than to local transport boilerplate. -/
noncomputable def base_change_raw_h1_map
    (P : Presentation R S ι σ) :
    LinearMap.ker (LinearMap.baseChange S' P.toGenerators.toExtension.cotangentComplex) →ₗ[S']
      (P.baseChange R').toGenerators.toExtension.H1Cotangent :=
  -- Route correction: package the displayed comparison behind a dedicated file-local name first,
  -- so the remaining blocker is the source-faithful surjectivity proof rather than an interface
  -- mismatch between two equivalent map descriptions.
  generator_baseChangeComparison (R := R) (S := S) (R' := R') P

/-- Helper for Lemma 15.86.2: under the temporary file-local packaging above, the displayed
presentation-level `H^{-1}` comparison agrees definitionally with `base_change_raw_h1_map`. -/
theorem generator_baseChangeComparison_eq_base_change_raw_h1_map
    (P : Presentation R S ι σ) :
    generator_baseChangeComparison (R := R) (S := S) (R' := R') P =
      base_change_raw_h1_map (R := R) (S := S) (R' := R') P := by
  -- The current file-local packaging makes this identification definitional.
  rfl

/-- Helper for Lemma 15.86.2: postcomposing the presentation-level comparison with the canonical
target identification removes the final transport through the chosen base-changed presentation. -/
theorem generator_baseChangeComparison_postcomp_equivH1Cotangent
    (P : Presentation R S ι σ) :
    (P.baseChange R').toGenerators.equivH1Cotangent.toLinearMap ∘ₗ
        generator_baseChangeComparison (R := R) (S := S) (R' := R') P =
      H1Cotangent.map R R' S' S' ∘ₗ
        tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators := by
  -- Expand the displayed comparison and cancel the inverse target equivalence.
  ext x
  simp [generator_baseChangeComparison]

/-- Helper for Lemma 15.86.2: surjectivity of the presentation-level comparison is equivalent to
surjectivity after transporting the target to `H^{-1}(L_{S'/R'})`. -/
theorem generator_baseChangeComparison_surjective_iff_owner
    (P : Presentation R S ι σ) :
    Function.Surjective (generator_baseChangeComparison (R := R) (S := S) (R' := R') P) ↔
      Function.Surjective
        (H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) := by
  constructor
  · intro hsurj y
    -- Pull the target element back through the presentation equivalence, then push it forward
    -- again using the postcomposition identity.
    let y' := (P.baseChange R').toGenerators.equivH1Cotangent.symm y
    rcases hsurj y' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hpost :
        (P.baseChange R').toGenerators.equivH1Cotangent
            (generator_baseChangeComparison (R := R) (S := S) (R' := R') P x) =
          (H1Cotangent.map R R' S' S' ∘ₗ
            tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) x := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun
          (generator_baseChangeComparison_postcomp_equivH1Cotangent
            (R := R) (S := S) (R' := R') (P := P)) x
    simpa [y', hx] using hpost.symm
  · intro hsurj y
    -- Surjectivity after transporting the target means surjectivity before transport as well.
    let y' := (P.baseChange R').toGenerators.equivH1Cotangent y
    rcases hsurj y' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (P.baseChange R').toGenerators.equivH1Cotangent.injective
    have hpost :
        (P.baseChange R').toGenerators.equivH1Cotangent
            (generator_baseChangeComparison (R := R) (S := S) (R' := R') P x) =
          (H1Cotangent.map R R' S' S' ∘ₗ
            tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) x := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun
          (generator_baseChangeComparison_postcomp_equivH1Cotangent
            (R := R) (S := S) (R' := R') (P := P)) x
    simpa [y', hx] using hpost

/-- Helper for Lemma 15.86.2: specializing the presentation-level surjectivity bridge to the
canonical self-presentation of `S/R` leaves exactly the source-faithful comparison map appearing
before the final owner transport. -/
theorem canonical_self_presentation_generator_baseChangeComparison_surjective_iff_source :
    Function.Surjective
        (generator_baseChangeComparison (R := R) (S := S) (R' := R')
          (canonical_self_presentation (R := R) (S := S))) ↔
      Function.Surjective
        (H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' (Generators.self R S)) := by
  -- The canonical self-presentation has `toGenerators = Generators.self R S`, so specializing the
  -- generic target-transport bridge only removes the final presentation equivalence.
  simpa [canonical_self_presentation] using
    (generator_baseChangeComparison_surjective_iff_owner
      (R := R) (S := S) (R' := R')
      (P := canonical_self_presentation (R := R) (S := S)))

/-- Helper for Lemma 15.86.2: surjectivity of the file-local raw comparison is exactly
surjectivity of the owner comparison after transporting the target by the chosen presentation
equivalence. -/
theorem base_change_raw_h1_map_surjective_iff_owner
    (P : Presentation R S ι σ) :
    Function.Surjective (base_change_raw_h1_map (R := R) (S := S) (R' := R') P) ↔
      Function.Surjective
        (H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) := by
  -- The raw map is just the presentation-level comparison with a local name.
  simpa [generator_baseChangeComparison_eq_base_change_raw_h1_map (P := P)] using
    (generator_baseChangeComparison_surjective_iff_owner
      (R := R) (S := S) (R' := R') (P := P))

/-- Helper for Lemma 15.86.2: the file-local packaged comparison map is surjective once the
source-faithful raw comparison has been proved surjective. -/
theorem base_change_raw_h1_map_surjective
    (P : Presentation R S ι σ) :
    Function.Surjective (base_change_raw_h1_map (R := R) (S := S) (R' := R') P) := by
  -- Route correction: first remove the target transport, so the remaining blocker is precisely
  -- the source-faithful surjectivity of the genuine two-term comparison on `H^{-1}`.
  refine (base_change_raw_h1_map_surjective_iff_owner
    (R := R) (S := S) (R' := R') (P := P)).2 ?_
  -- Proof comment: the source-faithful object is now fixed as
  -- `base_change_underived_chain_map`; its degree `0` and degree `1` formulas are recorded above,
  -- so the remaining work is only the actual surjectivity argument on cycles.
  -- TODO: replace the local alias by the actual `H^{-1}` map induced from the underived
  -- base-change comparison square for `P`, then apply
  -- `exists_preimage_in_kernel_of_two_term_comparison` using
  -- `base_change_underived_chain_map_degree_zero` for the degree `0` map and the missing
  -- degree `1` surjectivity statement for the map in
  -- `base_change_underived_chain_map_degree_one`.
  sorry

/-- Lemma 15.86.2: for a chosen presentation `P` of `S` over `R`, the comparison
`NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')`
is surjective on `H^{-1}`. This is the source-facing presentation-level comparison whose target is
identified with `H1Cotangent R' S'` via the canonical presentation equivalence. -/
@[stacks 0FUZ]
theorem naiveCotangentBaseChangeH1Comparison_surjective
    (P : Presentation R S ι σ) :
    Function.Surjective
      (((P.baseChange R').toGenerators.equivH1Cotangent.symm).toLinearMap ∘ₗ
        H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) := by
  -- Route correction: the target transport is already normalized by
  -- `generator_baseChangeComparison_surjective_iff_owner`, so the remaining source-faithful work
  -- is entirely on the raw cycle map induced by the base-changed comparison square.
  -- Reduce the displayed comparison to the file-local raw kernel map; the only remaining
  -- source-faithful blocker is surjectivity of that raw map itself.
  simpa [generator_baseChangeComparison_eq_base_change_raw_h1_map (P := P)] using
    base_change_raw_h1_map_surjective (R := R) (S := S) (R' := R') P

end Algebra.Presentation

/- The degree `0` part of Lemma 15.86.2 is the canonical Kähler-differential base-change
equivalence, i.e. the degree-`0` comparison for the owner chain map
`Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R')`. -/
recall KaehlerDifferential.tensorKaehlerEquivBase

end
