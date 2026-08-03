module

public import Topology_Munkres_2000.Book.Theorem_38_2.RealExtension
public import Mathlib.Topology.Homeomorph.Lemmas

public section

universe u v w

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 38.4: a family of bounded continuous real functions extends
coordinatewise to a continuous product-valued map. -/
private lemma existsContinuousPiExtension (Y : Compactification.{u, v} X)
    (hY : Y.ExtendsBoundedContinuousReal) {J : Type w}
    (F : J → BoundedContinuousFunction X ℝ) :
    ∃ G : ContinuousMap Y (J → ℝ), ∀ x : X, ∀ j : J, G (Y x) j = F j x := by
  classical
  -- Choose one extension per coordinate and assemble them using the product topology.
  choose G hG using fun j ↦ (hY (F j)).exists
  refine ⟨ContinuousMap.pi G, ?_⟩
  intro x j
  exact hG j x

/-- Helper for Theorem 38.4: evaluation by all continuous unit-interval-valued functions,
viewed as real coordinates, is a closed embedding of a compact Hausdorff space. -/
private lemma isClosedEmbedding_realEvaluation {C : Type w} [TopologicalSpace C]
    [CompactSpace C] [T2Space C] :
    Topology.IsClosedEmbedding
      (fun c (f : ContinuousMap C (Set.Icc (0 : ℝ) 1)) ↦ (f c : ℝ)) := by
  -- Each coordinate is continuous, so evaluation is continuous into the product.
  have hContinuous : Continuous
      (fun c (f : ContinuousMap C (Set.Icc (0 : ℝ) 1)) ↦ (f c : ℝ)) :=
    continuous_pi fun f ↦ continuous_subtype_val.comp f.continuous
  apply hContinuous.isClosedEmbedding
  intro c₁ c₂ hEvaluation
  -- Complete regularity supplies a unit-interval coordinate separating distinct points.
  by_contra hc
  obtain ⟨f, hf, hSeparate⟩ := separatesPoints_continuous_of_t35Space_Icc hc
  have hReal := congrFun hEvaluation
    (⟨f, hf⟩ : ContinuousMap C (Set.Icc (0 : ℝ) 1))
  exact hSeparate (Subtype.ext hReal)

/-- Helper for Theorem 38.4: a continuous map that lands in the range of a closed embedding
on a dense set factors continuously through that embedding. -/
private lemma existsContinuousFactorizationThroughClosedEmbedding
    {A : Type u} {D : Type v} {E Z : Type w}
    [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace Z]
    (i : A → D) (e : E → Z) (hi : DenseRange i) (he : Topology.IsClosedEmbedding e)
    (G : ContinuousMap D Z) (f : A → E) (h : ∀ a, G (i a) = e (f a)) :
    ∃ g : ContinuousMap D E, (∀ a, g (i a) = f a) ∧ ∀ d, e (g d) = G d := by
  classical
  -- Closedness of the embedded range propagates membership from the dense subset to all of `D`.
  have hRangeClosed : IsClosed {d | G d ∈ Set.range e} :=
    he.isClosed_range.preimage G.continuous
  have hRange : ∀ d, G d ∈ Set.range e := by
    intro d
    refine hi.induction_on d hRangeClosed ?_
    intro a
    exact ⟨f a, (h a).symm⟩
  have hRestrictedContinuous :
      Continuous (fun d ↦ (⟨G d, hRange d⟩ : Set.range e)) :=
    G.continuous.subtype_mk _
  let restricted : ContinuousMap D (Set.range e) :=
    ⟨fun d ↦ ⟨G d, hRange d⟩, hRestrictedContinuous⟩
  let g : ContinuousMap D E :=
    (he.isEmbedding.toHomeomorph.symm : ContinuousMap (Set.range e) E).comp restricted
  -- The inverse homeomorphism recovers the original product-valued map after re-embedding.
  have hImage : ∀ d, e (g d) = G d := by
    intro d
    have hInverse := Homeomorph.apply_symm_apply he.isEmbedding.toHomeomorph (restricted d)
    exact congrArg Subtype.val hInverse
  refine ⟨g, ?_, hImage⟩
  intro a
  apply he.injective
  exact (hImage (i a)).trans (h a)

/-- Theorem 38.4. A compactification with the bounded-real extension property uniquely extends
every continuous map into a compact Hausdorff space. -/
theorem extendsContinuousMap (Y : Compactification.{u, v} X)
    (hY : Y.ExtendsBoundedContinuousReal) {C : Type w}
    [TopologicalSpace C] [CompactSpace C] [T2Space C] (f : ContinuousMap X C) :
    ∃! g : ContinuousMap Y C, ∀ x : X, g (Y x) = f x := by
  -- Regard each unit-interval coordinate on `C` as a bounded real coordinate on `X`.
  let intervalVal : ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let coordinates : ContinuousMap C (Set.Icc (0 : ℝ) 1) →
      BoundedContinuousFunction X ℝ := fun φ ↦
    (BoundedContinuousFunction.mkOfCompact (intervalVal.comp φ)).compContinuous f
  obtain ⟨G, hG⟩ := existsContinuousPiExtension Y hY coordinates
  have hEvaluation : ∀ x : X,
      G (Y x) = (fun φ : ContinuousMap C (Set.Icc (0 : ℝ) 1) ↦ (φ (f x) : ℝ)) := by
    intro x
    funext φ
    exact hG x φ
  -- Closed-range factorization converts the product extension back into a map to `C`.
  obtain ⟨g, hg, _⟩ := existsContinuousFactorizationThroughClosedEmbedding
    Y (fun c (phi : ContinuousMap C (Set.Icc (0 : ℝ) 1)) ↦ (phi c : ℝ))
    Y.isDenseEmbedding.toIsDenseInducing.dense isClosedEmbedding_realEvaluation G f hEvaluation
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  -- Two extensions agree because their restrictions agree on the dense copy of `X`.
  apply ContinuousMap.ext
  intro y
  apply congrFun
    (Y.isDenseEmbedding.toIsDenseInducing.dense.equalizer g'.continuous g.continuous ?_) y
  funext x
  exact (hg' x).trans (hg x).symm

end Compactification
