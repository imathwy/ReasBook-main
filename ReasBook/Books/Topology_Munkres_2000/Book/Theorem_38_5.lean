module

public import Topology_Munkres_2000.Book.Definition_38_1.Equivalence
public import Topology_Munkres_2000.Book.Theorem_38_4

public section

universe u v w

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 38.5: the dense embedding of a compactification as a continuous map. -/
private def embeddingContinuousMap (C : Compactification.{u, v} X) : ContinuousMap X C :=
  -- Bundle the stored embedding with the continuity supplied by its embedding property.
  ⟨C, C.isDenseEmbedding.continuous⟩

/-- Helper for Theorem 38.5: extension maps in both directions are left inverses when the
source compactification has the bounded-real extension property. -/
private lemma extensionMapsLeftInverse (C : Compactification.{u, v} X)
    (D : Compactification.{u, w} X) (hC : C.ExtendsBoundedContinuousReal)
    (f : ContinuousMap C D) (g : ContinuousMap D C)
    (hf : ∀ x : X, f (C x) = D x) (hg : ∀ x : X, g (D x) = C x) :
    Function.LeftInverse g f := by
  -- Compare both the composite and the identity with the unique extension of the embedding.
  obtain ⟨extension, _, unique⟩ :=
    extendsContinuousMap C hC (embeddingContinuousMap C)
  have hComposite : ∀ x : X, (g.comp f) (C x) = embeddingContinuousMap C x := by
    intro x
    simp only [ContinuousMap.comp_apply, hf x, hg x, embeddingContinuousMap,
      ContinuousMap.coe_mk]
  have hIdentity : ∀ x : X,
      ContinuousMap.id C (C x) = embeddingContinuousMap C x := by
    intro x
    simp only [ContinuousMap.id_apply, embeddingContinuousMap, ContinuousMap.coe_mk]
  have hComposite_eq : g.comp f = extension := unique (g.comp f) hComposite
  have hIdentity_eq : ContinuousMap.id C = extension :=
    unique (ContinuousMap.id C) hIdentity
  have hMaps : g.comp f = ContinuousMap.id C := hComposite_eq.trans hIdentity_eq.symm
  -- Evaluate the equality of continuous maps to obtain the pointwise inverse equation.
  intro y
  exact DFunLike.congr_fun hMaps y

/-- Helper for Theorem 38.5: mutually inverse continuous maps determine a homeomorphism. -/
private def homeomorphOfContinuousMapInverses {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (f : ContinuousMap A B)
    (g : ContinuousMap B A) (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f) : A ≃ₜ B :=
  -- Use the inverse laws for the equivalence and the bundled maps for continuity.
  Homeomorph.mk (_root_.Equiv.mk f g hleft hright) f.continuous g.continuous

/-- Theorem 38.5. Two compactifications satisfying the bounded-real extension property are
equivalent over the original space. -/
theorem equivalent_of_extendsBoundedContinuousReal (Y₁ : Compactification.{u, v} X)
    (Y₂ : Compactification.{u, w} X) (hY₁ : Y₁.ExtendsBoundedContinuousReal)
    (hY₂ : Y₂.ExtendsBoundedContinuousReal) : Equivalent Y₁ Y₂ := by
  -- Extend each compactification embedding continuously across the other compactification.
  obtain ⟨f, hf, _⟩ := extendsContinuousMap Y₁ hY₁ (embeddingContinuousMap Y₂)
  obtain ⟨g, hg, _⟩ := extendsContinuousMap Y₂ hY₂ (embeddingContinuousMap Y₁)
  have hfEmbedding : ∀ x : X, f (Y₁ x) = Y₂ x := by
    intro x
    simpa only [embeddingContinuousMap, ContinuousMap.coe_mk] using hf x
  have hgEmbedding : ∀ x : X, g (Y₂ x) = Y₁ x := by
    intro x
    simpa only [embeddingContinuousMap, ContinuousMap.coe_mk] using hg x
  -- Uniqueness of extension makes the two maps mutual inverses.
  have hleft : Function.LeftInverse g f :=
    extensionMapsLeftInverse Y₁ Y₂ hY₁ f g hfEmbedding hgEmbedding
  have hright : Function.RightInverse g f :=
    extensionMapsLeftInverse Y₂ Y₁ hY₂ g f hgEmbedding hfEmbedding
  -- Package the inverse maps and retain the forward extension equation over `X`.
  apply (equivalent_iff Y₁ Y₂).2
  refine ⟨homeomorphOfContinuousMapInverses f g hleft hright, ?_⟩
  intro x
  simpa only [homeomorphOfContinuousMapInverses, Homeomorph.homeomorph_mk_coe,
    _root_.Equiv.coe_fn_mk] using hfEmbedding x

end Compactification

end
