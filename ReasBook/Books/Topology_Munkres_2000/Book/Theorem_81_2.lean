module

public import Topology_Munkres_2000.Book.Theorem_81_2.ComparisonCore

public section

universe u v

open scoped CoveringTransformation

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [hE : PathConnectedSpace E] [hB : PathConnectedSpace B]
variable [hlE : LocallyPathConnectedSpace E] [hlB : LocallyPathConnectedSpace B]
variable {p : E → B}

/-- Theorem 81.2: evaluation at `e₀`, followed by inverse monodromy and restriction to the
normalizer quotient. -/
@[expose]
noncomputable def normalizerQuotientComparison (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    𝒞(E, p, B) →* normalizerQuotient hp he₀ :=
  MonoidHom.mk' (normalizerQuotientComparisonValue hp e₀ b₀ he₀)
    (normalizerQuotientComparisonValue_mul hp e₀ b₀ he₀)

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The comparison homomorphism is the composite `Φ⁻¹ ∘ Ψ` from the source. -/
theorem normalizerQuotientComparison_apply (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (h : 𝒞(E, p, B)) :
    normalizerQuotientComparison hp e₀ b₀ he₀ h =
      Function.invFun (normalizerQuotientRightCoset hp he₀)
        (Function.invFun (hp.monodromyRightCosetMap he₀) (evalInFiber b₀ e₀ he₀ h)) := rfl

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The comparison homomorphism is characterized by applying monodromy to its canonical
right-coset image. -/
theorem monodromyRightCosetMap_normalizerQuotientComparison (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (h : 𝒞(E, p, B)) :
    hp.monodromyRightCosetMap he₀
        (normalizerQuotientRightCoset hp he₀ (normalizerQuotientComparison hp e₀ b₀ he₀ h)) =
      evalInFiber b₀ e₀ he₀ h := by
  -- The bundled homomorphism has the comparison value as its underlying function.
  exact normalizerQuotientComparisonValue_spec hp e₀ b₀ he₀ h

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The comparison homomorphism is bijective. -/
theorem normalizerQuotientComparison_bijective (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Function.Bijective (normalizerQuotientComparison hp e₀ b₀ he₀) := by
  constructor
  · intro h k hhk
    -- Evaluation is injective, and the characterization transports equality to evaluation.
    apply evalInFiber_injective hp b₀ e₀ he₀
    calc
      evalInFiber b₀ e₀ he₀ h = hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀
            (normalizerQuotientComparison hp e₀ b₀ he₀ h)) :=
        (monodromyRightCosetMap_normalizerQuotientComparison hp e₀ b₀ he₀ h).symm
      _ = hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀
            (normalizerQuotientComparison hp e₀ b₀ he₀ k)) :=
        congrArg (fun q ↦ hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀ q)) hhk
      _ = evalInFiber b₀ e₀ he₀ k :=
        monodromyRightCosetMap_normalizerQuotientComparison hp e₀ b₀ he₀ k
  · intro q
    -- Lemma 81.1 supplies a transformation evaluating at the monodromy endpoint of `q`.
    have hq_range : hp.monodromyRightCosetMap he₀
        (normalizerQuotientRightCoset hp he₀ q) ∈
        Set.range (evalInFiber b₀ e₀ he₀) := by
      rw [hp.range_evalInFiber_eq_image_normalizer p e₀ b₀ he₀]
      exact ⟨normalizerQuotientRightCoset hp he₀ q,
        normalizerQuotientRightCoset_mem hp he₀ q, rfl⟩
    obtain ⟨h, hh⟩ := hq_range
    refine ⟨h, ?_⟩
    apply normalizerQuotientRightCoset_injective hp he₀
    apply (hp.monodromyRightCosetMap_bijective he₀).1
    exact (monodromyRightCosetMap_normalizerQuotientComparison
      hp e₀ b₀ he₀ h).trans hh

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The comparison homomorphism is the unique homomorphism with its monodromy
characterization. -/
theorem normalizerQuotientComparison_unique (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    (f : 𝒞(E, p, B) →* normalizerQuotient hp he₀)
    (hf : ∀ h, hp.monodromyRightCosetMap he₀ (normalizerQuotientRightCoset hp he₀ (f h)) =
      evalInFiber b₀ e₀ he₀ h) :
    f = normalizerQuotientComparison hp e₀ b₀ he₀ := by
  -- Injectivity of the two canonical maps turns the shared characterization into equality.
  ext h
  apply normalizerQuotientRightCoset_injective hp he₀
  apply (hp.monodromyRightCosetMap_bijective he₀).1
  exact (hf h).trans
    (monodromyRightCosetMap_normalizerQuotientComparison hp e₀ b₀ he₀ h).symm

end CoveringTransformation
