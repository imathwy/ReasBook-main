module

public import Topology_Munkres_2000.Book.Theorem_81_2.Comparison

public section

universe u v

open scoped CoveringTransformation

/-- Helper for Corollary 81.3: right cosets represented by an intermediate subgroup fill
the quotient exactly when that subgroup is the whole group. -/
private lemma rightCosetImage_eq_univ_iff_eq_top {G : Type*} [Group G]
    (H K : Subgroup G) (hHK : H ≤ K) :
    (Quotient.mk'' : G → G ⧸ᵣ H) '' (K : Set G) = Set.univ ↔ K = ⊤ := by
  constructor
  · intro hcosets
    -- A representative in `K` of the coset of `g` differs from `g` by an element of `H`.
    apply (Subgroup.eq_top_iff' K).mpr
    intro g
    have hgCoset : (Quotient.mk'' : G → G ⧸ᵣ H) g ∈
        (Quotient.mk'' : G → G ⧸ᵣ H) '' (K : Set G) := by
      rw [hcosets]
      exact Set.mem_univ _
    obtain ⟨k, hk, hkg⟩ := hgCoset
    have hgk : g * k⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hkg)
    -- Multiplying the difference by `k` puts `g` itself in `K`.
    have hg : g * k⁻¹ * k ∈ K := K.mul_mem (hHK hgk) hk
    simpa only [inv_mul_cancel_right] using hg
  · intro hK
    subst K
    -- Surjectivity of the quotient map supplies a representative of every right coset.
    ext q
    constructor
    · intro _
      exact Set.mem_univ q
    · intro _
      obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
      exact ⟨g, Subgroup.mem_top g, rfl⟩

namespace CoveringTransformation

/-- Helper for Corollary 81.3: evaluation at one point is surjective precisely when the
covering-transformation action is transitive on its fiber. -/
theorem evalInFiber_surjective_iff_fiber_transitive
    {E : Type u} {B : Type v} [TopologicalSpace E]
    (p : E → B) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Function.Surjective (evalInFiber b₀ e₀ he₀) ↔
      ∀ e₁ e₂ : p ⁻¹' {b₀}, ∃ h : 𝒞(E, p, B), h e₁ = e₂ := by
  constructor
  · intro heval e₁ e₂
    -- Move the basepoint separately to `e₁` and `e₂`, then compare the two moves.
    obtain ⟨h₁, hh₁⟩ := heval e₁
    obtain ⟨h₂, hh₂⟩ := heval e₂
    have hh₁Value : h₁ • e₀ = (e₁ : E) := by
      simpa only [evalInFiber_apply] using congrArg Subtype.val hh₁
    have hh₂Value : h₂ • e₀ = (e₂ : E) := by
      simpa only [evalInFiber_apply] using congrArg Subtype.val hh₂
    refine ⟨h₂ * h₁⁻¹, ?_⟩
    calc
      (h₂ * h₁⁻¹) e₁ = (h₂ * h₁⁻¹) • (e₁ : E) := rfl
      _ = (h₂ * h₁⁻¹) • (h₁ • e₀) :=
        congrArg (fun e ↦ (h₂ * h₁⁻¹) • e) hh₁Value.symm
      _ = h₂ • e₀ := by
        simp only [mul_smul, inv_smul_smul]
      _ = e₂ := hh₂Value
  · intro htrans e
    -- Transitivity from the chosen basepoint produces a preimage of an arbitrary fiber point.
    obtain ⟨h, hh⟩ := htrans ⟨e₀, he₀⟩ e
    refine ⟨h, ?_⟩
    apply Subtype.ext
    calc
      (evalInFiber b₀ e₀ he₀ h : E) = h • e₀ := evalInFiber_apply b₀ e₀ he₀ h
      _ = h e₀ := rfl
      _ = e := hh

end CoveringTransformation

namespace IsCoveringMap

/-- Helper for Corollary 81.3: evaluation at the chosen point is surjective exactly when
the covering subgroup is normal. -/
theorem evalInFiber_surjective_iff_fundamentalGroupMapRange_normal
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (p : E → B) (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Function.Surjective (CoveringTransformation.evalInFiber b₀ e₀ he₀) ↔
      (hp.fundamentalGroupMapRange he₀).Normal := by
  -- Replace surjectivity by a range equality and use Lemma 81.1's normalizer description.
  rw [← Set.range_eq_univ, hp.range_evalInFiber_eq_image_normalizer p e₀ b₀ he₀]
  have hmonodromy := hp.monodromyRightCosetMap_bijective he₀
  calc
    hp.monodromyRightCosetMap he₀ ''
          ((Quotient.mk'' : FundamentalGroup B b₀ →
              FundamentalGroup B b₀ ⧸ᵣ hp.fundamentalGroupMapRange he₀) '' Subgroup.normalizer
            (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀))) =
        Set.univ ↔
      hp.monodromyRightCosetMap he₀ ''
          ((Quotient.mk'' : FundamentalGroup B b₀ →
              FundamentalGroup B b₀ ⧸ᵣ hp.fundamentalGroupMapRange he₀) '' Subgroup.normalizer
            (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀))) =
        hp.monodromyRightCosetMap he₀ '' Set.univ := by
          rw [Set.image_univ_of_surjective hmonodromy.2]
    _ ↔ (Quotient.mk'' : FundamentalGroup B b₀ →
            FundamentalGroup B b₀ ⧸ᵣ hp.fundamentalGroupMapRange he₀) '' Subgroup.normalizer
          (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀)) = Set.univ :=
      Set.image_eq_image hmonodromy.1
    _ ↔ Subgroup.normalizer
          (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀)) = ⊤ :=
      rightCosetImage_eq_univ_iff_eq_top
        (hp.fundamentalGroupMapRange he₀)
        (Subgroup.normalizer
          (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀)))
        Subgroup.le_normalizer
    _ ↔ (hp.fundamentalGroupMapRange he₀).Normal :=
      Subgroup.normalizer_eq_top_iff

/-- Corollary 81.3: the covering subgroup is normal exactly when covering transformations
act transitively on the fiber. -/
theorem fundamentalGroupMapRange_normal_iff_fiber_transitive
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : E → B) (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    (hp.fundamentalGroupMapRange he₀).Normal ↔
      ∀ e₁ e₂ : p ⁻¹' {b₀}, ∃ h : 𝒞(E, p, B), h e₁ = e₂ := by
  -- Pass from normality to evaluation surjectivity, then to transitivity of the action.
  exact (evalInFiber_surjective_iff_fundamentalGroupMapRange_normal
    p hp e₀ b₀ he₀).symm.trans
      (CoveringTransformation.evalInFiber_surjective_iff_fiber_transitive
        p e₀ b₀ he₀)

end IsCoveringMap

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [PathConnectedSpace E] [PathConnectedSpace B]
variable [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
variable {p : E → B}

/-- Helper for Corollary 81.3: when `H` is normal, its inclusion in its normalizer maps
back to `H` under the canonical equivalence from the normalizer to the ambient group. -/
private theorem subgroupOfNormalizer_map_normalizerEquiv {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] :
    (H.subgroupOf (Subgroup.normalizer (H : Set G))).map
        ((MulEquiv.subgroupCongr (Subgroup.normalizer_eq_top H)).trans Subgroup.topEquiv) = H := by
  ext x
  constructor
  · rintro ⟨hx, hxH, rfl⟩
    exact hxH
  · intro hxH
    have hxNormalizer : x ∈ Subgroup.normalizer (H : Set G) := by
      rw [Subgroup.normalizer_eq_top H]
      exact Subgroup.mem_top x
    let hx : Subgroup.normalizer (H : Set G) := ⟨x, hxNormalizer⟩
    refine ⟨hx, hxH, ?_⟩
    rfl

/-- When the covering subgroup is normal, its normalizer quotient is canonically the full
fundamental-group quotient. -/
noncomputable def normalizerQuotientEquivFundamentalGroupQuotient (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    [(hp.fundamentalGroupMapRange he₀).Normal] :
    normalizerQuotient hp he₀ ≃*
      FundamentalGroup B b₀ ⧸ hp.fundamentalGroupMapRange he₀ :=
  let H₀ := hp.fundamentalGroupMapRange he₀
  let e : normalizerSubgroup hp he₀ ≃* FundamentalGroup B b₀ :=
    (MulEquiv.subgroupCongr (Subgroup.normalizer_eq_top H₀)).trans Subgroup.topEquiv
  QuotientGroup.congr (H₀.subgroupOf (normalizerSubgroup hp he₀)) H₀ e
    (subgroupOfNormalizer_map_normalizerEquiv H₀)

/-- Corollary 81.3: the composite `Φ⁻¹ ∘ Ψ` from covering transformations to the
fundamental group modulo the covering subgroup. -/
@[expose]
noncomputable def fundamentalGroupQuotientComparison (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    [(hp.fundamentalGroupMapRange he₀).Normal] :
    𝒞(E, p, B) →* FundamentalGroup B b₀ ⧸ hp.fundamentalGroupMapRange he₀ :=
  (normalizerQuotientEquivFundamentalGroupQuotient hp e₀ b₀ he₀).toMonoidHom.comp
    (normalizerQuotientComparison hp e₀ b₀ he₀)

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The Corollary 81.3 comparison is the normalizer-quotient comparison followed by the
canonical quotient equivalence. -/
theorem fundamentalGroupQuotientComparison_apply (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    [(hp.fundamentalGroupMapRange he₀).Normal] (h : 𝒞(E, p, B)) :
    fundamentalGroupQuotientComparison hp e₀ b₀ he₀ h =
      normalizerQuotientEquivFundamentalGroupQuotient hp e₀ b₀ he₀
        (normalizerQuotientComparison hp e₀ b₀ he₀ h) := rfl

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- The Corollary 81.3 comparison homomorphism is bijective. -/
theorem fundamentalGroupQuotientComparison_bijective (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    [(hp.fundamentalGroupMapRange he₀).Normal] :
    Function.Bijective (fundamentalGroupQuotientComparison hp e₀ b₀ he₀) :=
  (normalizerQuotientEquivFundamentalGroupQuotient hp e₀ b₀ he₀).bijective.comp
    (normalizerQuotientComparison_bijective hp e₀ b₀ he₀)

end CoveringTransformation
