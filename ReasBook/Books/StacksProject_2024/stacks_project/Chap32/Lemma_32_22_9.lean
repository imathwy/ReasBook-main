import StacksProject_2024.Chap32.Lemma_32_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed the canonical owners `IsClosedImmersion`,
-- `IsIso`, `IsPullback`, and `pullback.lift` for the stagewise fibre-product comparison.
-- Nearby Lemma 32.22.4/32.22.6 supplies the shared tail-system API used below.

/-- The canonical comparison morphism from a scheme to the pullback of two target maps,
using the two displayed maps and their commutativity. -/
abbrev stagePullbackComparison {X1 X2 X3 X4 : Scheme.{u}}
    (q : X1 ⟶ X2) (p : X1 ⟶ X3) (b : X2 ⟶ X4) (a : X3 ⟶ X4)
    (hcomm : q ≫ b = p ≫ a) : X1 ⟶ pullback b a :=
  pullback.lift q p hcomm

/-- Lemma 32.22.9 (1): in Situation 32.22.1, after moving four finite-type approximation
systems and the descended morphisms `a_i`, `b_i`, `p_i`, and `q_i` to a common tail, a
cartesian square on the limit induces, at all sufficiently large stages, a commuting square whose
comparison morphism to the stagewise fibre product is a closed immersion. -/
@[stacks 0CNW]
theorem exists_eventually_isClosedImmersion_stagePullbackComparison_of_isPullback_limitSquare
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₀ : I}
    {X1sys X2sys X3sys X4sys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
    (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
    (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
    (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
    (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
    (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
    (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
    (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
    (x1Cone_toBase : ∀ j : TailIndexCategory i₀,
      x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
    (x2Cone_toBase : ∀ j : TailIndexCategory i₀,
      x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
    (x3Cone_toBase : ∀ j : TailIndexCategory i₀,
      x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
    (x4Cone_toBase : ∀ j : TailIndexCategory i₀,
      x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
    [QuasiSeparated x1ToS] [QuasiCompact x1ToS] [LocallyOfFiniteType x1ToS]
    [QuasiSeparated x2ToS] [QuasiCompact x2ToS] [LocallyOfFiniteType x2ToS]
    [QuasiSeparated x3ToS] [QuasiCompact x3ToS] [LocallyOfFiniteType x3ToS]
    [QuasiSeparated x4ToS] [QuasiCompact x4ToS] [LocallyOfFiniteType x4ToS]
    (X1approx : FinitePresentationApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
    (X2approx : FinitePresentationApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
    (X3approx : FinitePresentationApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
    (X4approx : FinitePresentationApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
    (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
    (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
    (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
    (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
    (hcart : IsPullback q p b a)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (hφp : φp.IsLimitMorphism x1Cone x3Cone p)
    (hφq : φq.IsLimitMorphism x1Cone x2Cone q)
    (hφa : φa.IsLimitMorphism x3Cone x4Cone a)
    (hφb : φb.IsLimitMorphism x2Cone x4Cone b) :
    ∃ (i₉ : I) (hi₀i₉ : i₀ ≤ i₉), ∀ ⦃i : I⦄ (hi₉i : i₉ ≤ i),
      ∃ hcomm :
        φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
            φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) =
          φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
            φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)),
        IsClosedImmersion
          (stagePullbackComparison
            (φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
            (φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
            (φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
            (φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
            hcomm) := sorry

/-- Lemma 32.22.9 (2): in the same setup, if the two vertical maps `a` and `b` of the
cartesian square are flat and of finite presentation, then for all sufficiently large stages the
comparison morphism from `X^1_i` to `X^2_i ×_{X^4_i} X^3_i` is an isomorphism. -/
@[stacks 0CNW]
theorem exists_eventually_isIso_stagePullbackComparison_of_isPullback_limitSquare_flat_finitePresentation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₀ : I}
    {X1sys X2sys X3sys X4sys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
    (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
    (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
    (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
    (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
    (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
    (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
    (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
    (x1Cone_toBase : ∀ j : TailIndexCategory i₀,
      x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
    (x2Cone_toBase : ∀ j : TailIndexCategory i₀,
      x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
    (x3Cone_toBase : ∀ j : TailIndexCategory i₀,
      x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
    (x4Cone_toBase : ∀ j : TailIndexCategory i₀,
      x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
    [QuasiSeparated x1ToS] [QuasiCompact x1ToS] [LocallyOfFiniteType x1ToS]
    [QuasiSeparated x2ToS] [QuasiCompact x2ToS] [LocallyOfFiniteType x2ToS]
    [QuasiSeparated x3ToS] [QuasiCompact x3ToS] [LocallyOfFiniteType x3ToS]
    [QuasiSeparated x4ToS] [QuasiCompact x4ToS] [LocallyOfFiniteType x4ToS]
    (X1approx : FinitePresentationApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
    (X2approx : FinitePresentationApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
    (X3approx : FinitePresentationApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
    (X4approx : FinitePresentationApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
    (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
    (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
    (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
    (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
    (hcart : IsPullback q p b a) (ha_flat : Flat a)
    (ha_fp : Scheme.Hom.FinitePresentation a) (hb_flat : Flat b)
    (hb_fp : Scheme.Hom.FinitePresentation b)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (hφp : φp.IsLimitMorphism x1Cone x3Cone p)
    (hφq : φq.IsLimitMorphism x1Cone x2Cone q)
    (hφa : φa.IsLimitMorphism x3Cone x4Cone a)
    (hφb : φb.IsLimitMorphism x2Cone x4Cone b) :
    ∃ (i₁₀ : I) (hi₀i₁₀ : i₀ ≤ i₁₀), ∀ ⦃i : I⦄ (hi₁₀i : i₁₀ ≤ i),
      ∃ hcomm :
        φq.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
            φb.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) =
          φp.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
            φa.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)),
        IsIso
          (stagePullbackComparison
            (φq.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)))
            (φp.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)))
            (φb.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)))
            (φa.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)))
            hcomm) := sorry

end AlgebraicGeometry
