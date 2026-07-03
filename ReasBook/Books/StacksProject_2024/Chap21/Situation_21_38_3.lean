import Mathlib
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FibredCategoryOver (inheritedStructureSheaf)
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

/-- Situation 21.38.3: for a ringed site `(\mathcal D, \mathcal O_\mathcal D)`, fibred
categories `\mathcal C` and `\mathcal C'` over `\mathcal D`, and a `1`-morphism
`u : \mathcal C' \to \mathcal C`, equip `\mathcal C` and `\mathcal C'` with the inherited
topologies, choose the corresponding morphisms of topoi `\pi`, `\pi'`, and `g`, identify their
inverse-image functors with the expected pullback functors on sheaves, set
`\mathcal O_\mathcal C = \pi^{-1}\mathcal O_\mathcal D` and
`\mathcal O_{\mathcal C'} = (\pi')^{-1}\mathcal O_\mathcal D`, require the canonical
identification `g^{-1}\mathcal O_\mathcal C \cong \mathcal O_{\mathcal C'}`, and record the
commutative triangle of topoi. -/
structure inherited_ringed_topos_situation (D : RingedSite.{u, v}) where
  /-- The fibred category `\mathcal C` over the underlying site of `\mathcal D`. -/
  C : FibredCategoryOver D
  /-- The fibred category `\mathcal C'` over the underlying site of `\mathcal D`. -/
  C' : FibredCategoryOver D
  /-- The given `1`-morphism `u : \mathcal C' \to \mathcal C` over `\mathcal D`. -/
  u : FibredCategoryMor C' C
  /-- The projection `\mathcal C \to \mathcal D` is continuous for the inherited topology on
  `\mathcal C`. -/
  pC_cont :
    Functor.IsContinuous C.p (FibredCategoryOver.inheritedTopology D.siteTopology C)
      D.siteTopology
  /-- The projection `\mathcal C' \to \mathcal D` is continuous for the inherited topology on
  `\mathcal C'`. -/
  pC'_cont :
    Functor.IsContinuous C'.p (FibredCategoryOver.inheritedTopology D.siteTopology C')
      D.siteTopology
  /-- The functor underlying `u` is continuous for the inherited topologies. -/
  u_cont :
    Functor.IsContinuous u.G
      (FibredCategoryOver.inheritedTopology D.siteTopology C')
      (FibredCategoryOver.inheritedTopology D.siteTopology C)
  /-- The projection morphism of topoi `\pi : \operatorname{Sh}(\mathcal C) \to
  \operatorname{Sh}(\mathcal D)`. -/
  π : MorphismOfTopoiIn D.siteTopology (FibredCategoryOver.inheritedTopology D.siteTopology C)
  /-- The projection morphism of topoi `\pi' : \operatorname{Sh}(\mathcal C') \to
  \operatorname{Sh}(\mathcal D)`. -/
  π' : MorphismOfTopoiIn D.siteTopology (FibredCategoryOver.inheritedTopology D.siteTopology C')
  /-- The comparison morphism of topoi `g : \operatorname{Sh}(\mathcal C') \to
  \operatorname{Sh}(\mathcal C)`. -/
  g : MorphismOfTopoiIn
    (FibredCategoryOver.inheritedTopology D.siteTopology C)
    (FibredCategoryOver.inheritedTopology D.siteTopology C')
  /-- The inverse-image functor of `\pi` is the continuous pullback functor attached to the
  projection `\mathcal C \to \mathcal D`. -/
  π_inverseImage_eq :
    π⁻¹ =
      C.p.sheafPushforwardContinuous (Type (max u v))
        (FibredCategoryOver.inheritedTopology D.siteTopology C)
        D.siteTopology
  /-- The inverse-image functor of `\pi'` is the continuous pullback functor attached to the
  projection `\mathcal C' \to \mathcal D`. -/
  π'_inverseImage_eq :
    π'⁻¹ =
      C'.p.sheafPushforwardContinuous (Type (max u v))
        (FibredCategoryOver.inheritedTopology D.siteTopology C')
        D.siteTopology
  /-- The inverse-image functor of `g` is the continuous pullback functor attached to the
  comparison functor `u`. -/
  g_inverseImage_eq :
    g⁻¹ =
      u.G.sheafPushforwardContinuous (Type (max u v))
        (FibredCategoryOver.inheritedTopology D.siteTopology C')
        (FibredCategoryOver.inheritedTopology D.siteTopology C)
  /-- The canonical identification `g^{-1}\mathcal O_\mathcal C \cong
  \mathcal O_{\mathcal C'}` for the inherited structure sheaves. -/
  comparison_pullback_targetStructureSheaf_iso_sourceStructureSheaf :
    (g⁻¹).obj (inheritedStructureSheaf D C) ≅ inheritedStructureSheaf D C'
  /-- The inverse-image functors of `\pi \circ g` and `\pi'` are canonically isomorphic. -/
  comm : π⁻¹ ⋙ g⁻¹ ≅ π'⁻¹

/-- An inherited ringed-topos situation supplies continuity of the projection
`\mathcal C \to \mathcal D` for the inherited topology on `\mathcal C`. -/
instance
    {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D) :
    Functor.IsContinuous S.C.p
      (FibredCategoryOver.inheritedTopology D.siteTopology S.C)
      D.siteTopology :=
  S.pC_cont

/-- An inherited ringed-topos situation supplies continuity of the projection
`\mathcal C' \to \mathcal D` for the inherited topology on `\mathcal C'`. -/
instance
    {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D) :
    Functor.IsContinuous S.C'.p
      (FibredCategoryOver.inheritedTopology D.siteTopology S.C')
      D.siteTopology :=
  S.pC'_cont

/-- An inherited ringed-topos situation supplies continuity of the comparison functor
`u : \mathcal C' \to \mathcal C` for the inherited topologies. -/
instance
    {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D) :
    Functor.IsContinuous S.u.G
      (FibredCategoryOver.inheritedTopology D.siteTopology S.C')
      (FibredCategoryOver.inheritedTopology D.siteTopology S.C) :=
  S.u_cont
