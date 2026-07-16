import Mathlib
import stacks_proof.stacks_project.Chap10.Proposition_10_89_3
import stacks_proof.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum TensorProduct

universe u v w x y

namespace Module

namespace MittagLeffler

section DirectSum

/- Domain-style sampling:
- primary domain: the owner class `Module.MittagLeffler` and its closure properties;
- sampled declarations of the same kind:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`,
  `CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂` from `Lemma_10_89_7`,
  `Module.mittagLeffler_colimit_of_directedSystem` from `Lemma_10_89_9`,
  together with the owner-shaped mathlib declarations `Module.Flat.directSum_iff`,
  `Module.Flat.directSum`, and the definitional companion `Module.Flat.dfinsupp_iff`.
- best owner abstraction: `Module.MittagLeffler`; the direct-sum statement is derived API of this
  owner, not a separate local wrapper notion.
- layer: `source-facing` theorem stated through the canonical owner.
- primitive data: the family of summands `M`.
- derived API: the direct-sum characterization/instance, with the `Π₀` formulation only as a thin
  definitional companion.
-/

section

variable {R : Type u} [CommRing R]
variable {I : Type v} {M : I → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Helper for Chap10 Lemma 10 89 10: a split summand of a Mittag-Leffler module is
Mittag-Leffler. -/
private lemma of_split {P : Type v} [AddCommGroup P] [Module R P]
    {N : Type w} [AddCommGroup N] [Module R N]
    [MittagLeffler R N] (i : P →ₗ[R] N) (p : N →ₗ[R] P)
    (hp : p.comp i = LinearMap.id) : MittagLeffler R P := by
  -- Use the tensor-product product comparison criterion for the summand.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective (R := R) (M := P)).2 ?_
  intro (A : Type (max v w)) (Q : A → Type (max v w)) _ _
  have hN : Function.Injective (TensorProduct.piRightHom R R N Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1
      (inferInstance : MittagLeffler R N)) A Q
  have hsplit_tensor :
      (p.rTensor (∀ a, Q a)).comp (i.rTensor (∀ a, Q a)) = LinearMap.id := by
    -- Tensoring preserves the retraction identity `p.comp i = id`.
    rw [← LinearMap.rTensor_comp, hp, LinearMap.rTensor_id]
  have hi_tensor : Function.Injective (i.rTensor (∀ a, Q a)) :=
    LinearMap.injective_of_comp_eq_id _ _ hsplit_tensor
  intro x y hxy
  -- Compare after the split inclusion, where the ambient Mittag-Leffler hypothesis applies.
  apply hi_tensor
  apply hN
  rw [piRightHom_rTensor_apply_linear i x, piRightHom_rTensor_apply_linear i y, hxy]

/-- Helper for Chap10 Lemma 10 89 10: the canonical map from a direct sum of products to the
product of the corresponding direct sums. -/
private noncomputable def directSumPiComparison {A : Type x}
    (N : I → A → Type y)
    [∀ i a, AddCommGroup (N i a)] [∀ i a, Module R (N i a)] :
    (⨁ i, ∀ a, N i a) →ₗ[R] ∀ a, ⨁ i, N i a :=
  LinearMap.pi fun a => DirectSum.lmap (fun _ => LinearMap.proj a)

/-- Helper for Chap10 Lemma 10 89 10: the direct sum/product comparison map is injective. -/
private lemma directSumPiComparison_injective {A : Type x}
    (N : I → A → Type y)
    [∀ i a, AddCommGroup (N i a)] [∀ i a, Module R (N i a)] :
    Function.Injective (directSumPiComparison (R := R) N) := by
  intro x y hxy
  -- Recover a direct-sum element from all component functions, one coordinate at a time.
  apply DirectSum.ext_component R
  intro i
  ext a
  simpa [DirectSum.component, directSumPiComparison, DirectSum.lmap_apply] using
    congrArg (fun z => (z a : ⨁ i, N i a) i) hxy

/-- Helper for Chap10 Lemma 10 89 10: the direct sum/product comparison is compatible with
`TensorProduct.piRightHom` and the direct-sum tensor equivalence. -/
private lemma directSumPiComparison_lmap_piRightHom {A : Type x} [DecidableEq I]
    {Q : A → Type y} [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (z : (⨁ i, M i) ⊗[R] (∀ a, Q a)) :
    directSumPiComparison (R := R) (fun i a => M i ⊗[R] Q a)
        (DirectSum.lmap (fun i => TensorProduct.piRightHom R R (M i) Q)
          ((TensorProduct.directSumLeft R R M (∀ a, Q a)) z)) =
      fun a => TensorProduct.directSumLeft R R M (Q a)
        ((TensorProduct.piRightHom R R (⨁ i, M i) Q z) a) := by
  -- Tensor induction reduces the compatibility square to the defining computation on pure tensors.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · ext a i
    simp [directSumPiComparison]
  · intro m q
    ext a i
    simp [directSumPiComparison, TensorProduct.piRightHom_tmul, DirectSum.lmap_apply]
  · intro z₁ z₂ hz₁ hz₂
    ext a i
    simp [hz₁, hz₂]

-- Proof sketch: for the forward implication, each summand is a direct summand of the direct sum,
-- so apply Lemma `10.89.7 (1)` to the split universally exact sequence coming from the projection
-- onto the `i`-th summand. For the reverse implication, express `Π₀ i, M i` as the directed
-- colimit of its finite partial sums; each finite partial sum is Mittag-Leffler by repeated use of
-- Lemma `10.89.7 (2)`, and Lemma `10.89.9` finishes the passage to the full direct sum.
/-- Chap10 Lemma 10 89 10: a direct sum `⨁ i, M i` of `R`-modules is Mittag-Leffler if and only if each
summand `M i` is Mittag-Leffler. -/
@[stacks 059P]
theorem directSum_iff :
    Module.MittagLeffler R (⨁ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) := by
  -- Route correction: instead of the source filtered-colimit route, use the already proved
  -- tensor-product product-comparison criterion and the direct-sum tensor equivalence.
  constructor
  · intro h i
    classical
    letI : Module.MittagLeffler R (⨁ i, M i) := h
    -- Each summand is split by the canonical inclusion and projection.
    refine of_split (DirectSum.lof R I M i) (DirectSum.component R I M i) ?_
    ext x
    simpa using (DirectSum.component.of (R := R) (M := M) i i x)
  · intro h
    classical
    -- It suffices to prove injectivity of the product comparison map for the whole direct sum.
    refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective
      (R := R) (M := ⨁ i, M i)).2 ?_
    intro (A : Type (max v w)) (Q : A → Type (max v w)) _ _ x y hxy
    apply (TensorProduct.directSumLeft R R M (∀ a, Q a)).injective
    have hcomp :
        DirectSum.lmap (fun i => TensorProduct.piRightHom R R (M i) Q)
            ((TensorProduct.directSumLeft R R M (∀ a, Q a)) x) =
          DirectSum.lmap (fun i => TensorProduct.piRightHom R R (M i) Q)
            ((TensorProduct.directSumLeft R R M (∀ a, Q a)) y) := by
      -- The comparison map into the product of direct sums detects equality after rewriting
      -- both sides to the original `piRightHom` equality.
      apply directSumPiComparison_injective (R := R) (fun i a => M i ⊗[R] Q a)
      rw [directSumPiComparison_lmap_piRightHom (R := R) (M := M) (Q := Q) x,
        directSumPiComparison_lmap_piRightHom (R := R) (M := M) (Q := Q) y]
      ext a
      rw [hxy]
    have hlmap : Function.Injective
        (DirectSum.lmap (fun i => TensorProduct.piRightHom R R (M i) Q)) :=
      (DirectSum.lmap_injective (fun i => TensorProduct.piRightHom R R (M i) Q)).2
        (fun i => (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1 (h i)) A Q)
    -- Componentwise Mittag-Leffler injectivity recovers equality after the direct-sum tensor
    -- equivalence, which finishes by injectivity of that equivalence.
    exact hlmap hcomp

/-- The `Π₀` presentation is a definitional companion to `directSum_iff`. -/
theorem dfinsupp_iff :
    Module.MittagLeffler R (Π₀ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) :=
  directSum_iff ..

/-- A direct sum of Mittag-Leffler `R`-modules is Mittag-Leffler. -/
instance directSum [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (⨁ i, M i) :=
  directSum_iff.2 ‹_›

instance dfinsupp [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (Π₀ i, M i) :=
  dfinsupp_iff.2 ‹_›

end

end DirectSum

end MittagLeffler

end Module
