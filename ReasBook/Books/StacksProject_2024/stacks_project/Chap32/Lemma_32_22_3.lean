import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: no `lean_leansearch` tool was exposed in this session. Local checks fixed the
-- canonical scheme-limit surface as `OrderDual I ⥤ Scheme`, `Cone D`, and
-- `Over.post D ⋙ Over.pullback _ ⋙ Over.forget _`; the Stacks source tag evidence for this item
-- is consistent with tag `0CNQ`.

/-- The inverse system `i' ↦ S_{i'} ×_{S_i} W` over the stages `i' ≥ i`. -/
abbrev finiteTypeApproximationBaseChangeDiagram {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i : OrderDual I) {W : Scheme.{u}}
    (toSi : W ⟶ D.obj i) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback toSi ⋙ Over.forget _

/-- A factorization of a morphism through its scheme-theoretic image. -/
structure IsSchemeTheoreticImageFactorization {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop where
  /-- The factorization composes back to the original morphism. -/
  fac : toImage ≫ ι = g
  /-- The image object is a closed subscheme of the target. -/
  isClosedImmersion : IsClosedImmersion ι
  /-- Minimality among closed subschemes through which the morphism factors. -/
  universal : ∀ ⦃Z' : Scheme.{u}⦄ (toZ' : X ⟶ Z') (closed : Z' ⟶ Y),
    IsClosedImmersion closed → toZ' ≫ closed = g →
      ∃! lift : Z ⟶ Z', lift ≫ closed = ι ∧ toImage ≫ lift = toZ'

/-- Lemma 32.22.3: in Situation 32.22.1, let `X ⟶ S` be quasi-separated and of
finite type. Given a stage `i` and a diagram `X ⟶ W` over `S ⟶ S_i` as in (32.22.2.1),
with `W ⟶ S_i` finite type and the induced map `X ⟶ S ×_{S_i} W` a closed immersion, if
`X_{i'}` is the scheme-theoretic image of `X ⟶ S_{i'} ×_{S_i} W` for every stage
`i' ≥ i`, then `X` is the limit of the inverse system of these `X_{i'}`. -/
@[stacks 0CNQ]
theorem exists_isLimit_schemeTheoreticImages_finiteTypeApproximation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) {X W : Scheme.{u}} (f : X ⟶ c.pt)
    [QuasiSeparated f] [Scheme.Hom.FiniteType f]
    (toW : X ⟶ W) (toSi : W ⟶ D.obj i) [Scheme.Hom.FiniteType toSi]
    (square : CommSq toW f toSi (c.π.app i))
    (toLimitBaseChange : X ⟶ pullback (c.π.app i) toSi)
    (toLimitBaseChange_fst :
      toLimitBaseChange ≫ pullback.fst (c.π.app i) toSi = f)
    (toLimitBaseChange_snd :
      toLimitBaseChange ≫ pullback.snd (c.π.app i) toSi = toW)
    [IsClosedImmersion toLimitBaseChange]
    (Xi : Over (show OrderDual I from i) ⥤ Scheme.{u})
    (π : (Functor.const (Over (show OrderDual I from i))).obj X ⟶ Xi)
    (toBaseChange : (Functor.const (Over (show OrderDual I from i))).obj X ⟶
      finiteTypeApproximationBaseChangeDiagram D (show OrderDual I from i) toSi)
    (toBaseChange_fst : ∀ j : Over (show OrderDual I from i),
      toBaseChange.app j ≫ pullback.fst (D.map j.hom) toSi = f ≫ c.π.app j.left)
    (toBaseChange_snd : ∀ j : Over (show OrderDual I from i),
      toBaseChange.app j ≫ pullback.snd (D.map j.hom) toSi = toW)
    (ι : Xi ⟶ finiteTypeApproximationBaseChangeDiagram D (show OrderDual I from i) toSi)
    (himage : ∀ j : Over (show OrderDual I from i),
      IsSchemeTheoreticImageFactorization (toBaseChange.app j) (π.app j) (ι.app j)) :
    Nonempty (IsLimit (⟨X, π⟩ : Cone Xi)) := sorry

end AlgebraicGeometry
