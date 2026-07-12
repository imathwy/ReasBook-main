import StacksProject_2024.Chap08.Lemma_8_8_1.CartesianComposition

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace DescentCompletionObjectOver

/-- Source stage 3.11: an arrow of the pullback cover is viewed as an arrow of the original
cover by composing its structural map with the base-change arrow. -/
abbrev pullbackCoverBaseArrow
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I : (D.cover.pullback h).Arrow) : D.cover.Arrow :=
  I.base

@[simp]
theorem pullbackCoverBaseArrow_f
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I : (D.cover.pullback h).Arrow) :
    (pullbackCoverBaseArrow (J := J) D h I).f = I.f ≫ h :=
  rfl

/-- Source stage 3.11: pull back a descent-completion object over `U` along `h : T ⟶ U`.
The cover is the pullback cover and the descent datum is the original datum with all base maps
postcomposed by `h`. -/
noncomputable def pullback
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U) :
    DescentCompletionObjectOver (J := J) X T where
  cover := D.cover.pullback h
  datum :=
    { obj := fun I => D.datum.obj (pullbackCoverBaseArrow (J := J) D h I)
      hom := fun {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ =>
        D.datum.hom (q := q ≫ h)
          (i₁ := pullbackCoverBaseArrow (J := J) D h I₁)
          (i₂ := pullbackCoverBaseArrow (J := J) D h I₂) f₁ f₂
          (by
            simpa [pullbackCoverBaseArrow, Category.assoc] using
              congrArg (fun t => t ≫ h) hf₁)
          (by
            simpa [pullbackCoverBaseArrow, Category.assoc] using
              congrArg (fun t => t ≫ h) hf₂)
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        exact
          D.datum.pullHom_hom
            (i₁ := pullbackCoverBaseArrow (J := J) D h I₁)
            (i₂ := pullbackCoverBaseArrow (J := J) D h I₂)
            g (q ≫ h) (q' ≫ h)
            (by simpa [Category.assoc] using congrArg (fun t => t ≫ h) hq)
            f₁ f₂
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hf₁)
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hf₂)
            gf₁ gf₂ hgf₁ hgf₂
      hom_self := by
        intro Y q I g hg
        exact
          D.datum.hom_self
            (i := pullbackCoverBaseArrow (J := J) D h I) (q ≫ h) g
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hg)
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        exact
          D.datum.hom_comp
            (i₁ := pullbackCoverBaseArrow (J := J) D h I₁)
            (i₂ := pullbackCoverBaseArrow (J := J) D h I₂)
            (i₃ := pullbackCoverBaseArrow (J := J) D h I₃)
            (q ≫ h) f₁ f₂ f₃
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hf₁)
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hf₂)
            (by
              simpa [pullbackCoverBaseArrow, Category.assoc] using
                congrArg (fun t => t ≫ h) hf₃) }

@[simp]
theorem pullback_cover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U) :
    (pullback (J := J) D h).cover = D.cover.pullback h :=
  rfl

@[simp]
theorem pullback_localObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I : (D.cover.pullback h).Arrow) :
    (pullback (J := J) D h).localObject I =
      D.localObject (pullbackCoverBaseArrow (J := J) D h I) :=
  rfl

@[simp]
theorem pullback_restrictedLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T W : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I : (D.cover.pullback h).Arrow) (i : W ⟶ I.Y) :
    (pullback (J := J) D h).restrictedLocalObject I i =
      D.restrictedLocalObject (pullbackCoverBaseArrow (J := J) D h I) i :=
  rfl

set_option maxHeartbeats 800000 in
/-- Pullback descent transitions are the original descent transitions after composing the two
cover arrows with the base-change arrow. -/
theorem pullback_overlapIso_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T W : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I₁ I₂ : (D.cover.pullback h).Arrow)
    (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
    (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f) :
    ((pullback (J := J) D h).overlapIso i₁ i₂ hD).hom =
      (D.overlapIso
        (I₁ := pullbackCoverBaseArrow (J := J) D h I₁)
        (I₂ := pullbackCoverBaseArrow (J := J) D h I₂)
        i₁ i₂
        (by
          simpa [pullbackCoverBaseArrow, Category.assoc] using
            congrArg (fun t => t ≫ h) hD)).hom := by
  let I₁b := pullbackCoverBaseArrow (J := J) D h I₁
  let I₂b := pullbackCoverBaseArrow (J := J) D h I₂
  have hDb : i₁ ≫ I₁b.f = i₂ ≫ I₂b.f := by
    dsimp [I₁b, I₂b, pullbackCoverBaseArrow]
    simpa [Category.assoc] using congrArg (fun t => t ≫ h) hD
  dsimp [overlapIso, transitionIso, pullback, pullbackCoverBaseArrow]
  change
    D.datum.hom (q := (i₁ ≫ I₁.f) ≫ h) (i₁ := I₁b) (i₂ := I₂b) i₁ i₂ _ _ =
      D.datum.hom (q := i₁ ≫ I₁b.f) (i₁ := I₁b) (i₂ := I₂b) i₁ i₂ _ _
  exact
    datumHom_congr_base (J := J) D
      (I₁ := I₁b) (I₂ := I₂b)
      (by
        dsimp [I₁b, pullbackCoverBaseArrow]
        rw [Category.assoc])
      i₁ i₂
      (by
        dsimp [I₁b, pullbackCoverBaseArrow]
        rw [Category.assoc])
      (by
        dsimp [I₁b, I₂b, pullbackCoverBaseArrow]
        simpa [Category.assoc] using (congrArg (fun t => t ≫ h) hD).symm)
      (by rfl)
      (by exact hDb.symm)

/-- Source stage 3.11: the canonical local morphism from the base-changed object back to the
original object, written over the fixed base arrow `h : T ⟶ U`.  Its components are exactly the
original descent transition maps on the corresponding overlap. -/
noncomputable def pullbackProjectionHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U) :
    HomOver (J := J) (pullback (J := J) D h) D h where
  family I K i k hIK :=
    (D.overlapIso
      (I₁ := pullbackCoverBaseArrow (J := J) D h I) (I₂ := K) i k
      (by
        simpa [pullbackCoverBaseArrow, Category.assoc] using hIK)).hom
  compatible := by
    intro W I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hD hE h₁ h₂
    let I₁b := pullbackCoverBaseArrow (J := J) D h I₁
    let I₂b := pullbackCoverBaseArrow (J := J) D h I₂
    have hDb : i₁ ≫ I₁b.f = i₂ ≫ I₂b.f := by
      dsimp [I₁b, I₂b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using congrArg (fun t => t ≫ h) hD
    have h₁b : i₁ ≫ I₁b.f = k₁ ≫ K₁.f := by
      dsimp [I₁b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using h₁
    have h₂b : i₂ ≫ I₂b.f = k₂ ≫ K₂.f := by
      dsimp [I₂b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using h₂
    have hleft :=
      overlapIso_hom_comp (J := J) D
        (I₁ := I₁b) (I₂ := I₂b) (I₃ := K₂) i₁ i₂ k₂ hDb h₂b
    have hright :=
      overlapIso_hom_comp (J := J) D
        (I₁ := I₁b) (I₂ := K₁) (I₃ := K₂) i₁ k₁ k₂ h₁b hE
    have hpull :
        ((pullback (J := J) D h).overlapIso i₁ i₂ hD).hom =
          (D.overlapIso (I₁ := I₁b) (I₂ := I₂b) i₁ i₂ hDb).hom := by
      simpa [I₁b, I₂b, hDb] using
        pullback_overlapIso_hom (J := J) D h I₁ I₂ i₁ i₂ hD
    dsimp [pullbackCoverBaseArrow]
    rw [hpull, hleft, hright]

@[simp]
theorem pullbackProjectionHomOver_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T W : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U)
    (I : (D.cover.pullback h).Arrow) (K : D.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (hIK : i ≫ I.f ≫ h = k ≫ K.f) :
    (pullbackProjectionHomOver (J := J) D h).family I K i k hIK =
      (D.overlapIso
        (I₁ := pullbackCoverBaseArrow (J := J) D h I) (I₂ := K) i k
        (by
          simpa [Category.assoc] using hIK)).hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.11: the canonical projection from a base-changed descent object satisfies
the restriction/naturality law for morphisms. -/
theorem pullbackProjectionHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U) :
    HomOver.familyNaturality' (J := J)
      (pullbackProjectionHomOver (J := J) D h) := by
  intro W W' I K i k hIK m mi mk hmi hmk
  have hbase :
      i ≫ (pullbackCoverBaseArrow (J := J) D h I).f = k ≫ K.f := by
    simpa [Category.assoc] using hIK
  have hnat :=
    HomOver.overlapIso_pullHom (J := J) D
      (pullbackCoverBaseArrow (J := J) D h I) K i k hbase m mi mk hmi hmk
  dsimp [pullbackProjectionHomOver]
  simpa [pullbackCoverBaseArrow, Category.assoc] using hnat

/-- Source stage 3.11: bundled natural morphism from the pullback object to the original object. -/
noncomputable def pullbackProjection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U T : C}
    (D : DescentCompletionObjectOver (J := J) X U) (h : T ⟶ U) :
    NaturalHomOver (J := J) (pullback (J := J) D h) D h where
  toHomOver := pullbackProjectionHomOver (J := J) D h
  naturality := pullbackProjectionHomOver_familyNaturality' (J := J) D h

/-- Source stage 3.11: given a morphism into `D` over `g ≫ h`, construct the candidate
factorization through the pulled-back descent object over `g`.  Componentwise this is the same
local map, with the target cover arrow regarded as an arrow of the original cover. -/
noncomputable def liftToPullbackHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W U T : C}
    {A : DescentCompletionObjectOver (J := J) X W}
    {D : DescentCompletionObjectOver (J := J) X U}
    {h : T ⟶ U} {g : W ⟶ T}
    (α : NaturalHomOver (J := J) A D (g ≫ h)) :
    HomOver (J := J) A (pullback (J := J) D h) g where
  family I K i k hIK :=
    α.toHomOver.family I (pullbackCoverBaseArrow (J := J) D h K) i k
      (by
        simpa [pullbackCoverBaseArrow, Category.assoc] using
          congrArg (fun t => t ≫ h) hIK)
  compatible := by
    intro Y I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hA hK h₁ h₂
    let K₁b := pullbackCoverBaseArrow (J := J) D h K₁
    let K₂b := pullbackCoverBaseArrow (J := J) D h K₂
    have hKb : k₁ ≫ K₁b.f = k₂ ≫ K₂b.f := by
      dsimp [K₁b, K₂b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using congrArg (fun t => t ≫ h) hK
    have h₁b : i₁ ≫ I₁.f ≫ (g ≫ h) = k₁ ≫ K₁b.f := by
      dsimp [K₁b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using congrArg (fun t => t ≫ h) h₁
    have h₂b : i₂ ≫ I₂.f ≫ (g ≫ h) = k₂ ≫ K₂b.f := by
      dsimp [K₂b, pullbackCoverBaseArrow]
      simpa [Category.assoc] using congrArg (fun t => t ≫ h) h₂
    have htarget :
        ((pullback (J := J) D h).overlapIso k₁ k₂ hK).hom =
          (D.overlapIso (I₁ := K₁b) (I₂ := K₂b) k₁ k₂ hKb).hom := by
      simpa [K₁b, K₂b, hKb] using
        pullback_overlapIso_hom (J := J) D h K₁ K₂ k₁ k₂ hK
    simpa [K₁b, K₂b, htarget] using
      α.toHomOver.compatible I₁ I₂ K₁b K₂b i₁ i₂ k₁ k₂ hA hKb h₁b h₂b

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.11: the candidate base-change factorization satisfies the
restriction/naturality law. -/
theorem liftToPullbackHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W U T : C}
    {A : DescentCompletionObjectOver (J := J) X W}
    {D : DescentCompletionObjectOver (J := J) X U}
    {h : T ⟶ U} {g : W ⟶ T}
    (α : NaturalHomOver (J := J) A D (g ≫ h)) :
    HomOver.familyNaturality' (J := J)
      (liftToPullbackHomOver (J := J) (A := A) (D := D) (h := h) (g := g) α) := by
  intro Y Y' I K i k hIK m mi mk hmi hmk
  have hIKb :
      i ≫ I.f ≫ (g ≫ h) =
        k ≫ (pullbackCoverBaseArrow (J := J) D h K).f := by
    simpa [pullbackCoverBaseArrow, Category.assoc] using
      congrArg (fun t => t ≫ h) hIK
  have hnat :=
    α.naturality I (pullbackCoverBaseArrow (J := J) D h K) i k hIKb
      m mi mk hmi hmk
  simpa [liftToPullbackHomOver, pullbackCoverBaseArrow, Category.assoc] using hnat

/-- Source stage 3.11: bundled natural factorization through the base-changed descent object. -/
noncomputable def liftToPullback
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W U T : C}
    {A : DescentCompletionObjectOver (J := J) X W}
    {D : DescentCompletionObjectOver (J := J) X U}
    {h : T ⟶ U} {g : W ⟶ T}
    (α : NaturalHomOver (J := J) A D (g ≫ h)) :
    NaturalHomOver (J := J) A (pullback (J := J) D h) g where
  toHomOver := liftToPullbackHomOver (J := J) (A := A) (D := D) (h := h) (g := g) α
  naturality := liftToPullbackHomOver_familyNaturality' (J := J) α

namespace HomOver

set_option maxHeartbeats 1200000 in
/-- Source stage 3.11, existence part of base-change cartesianness: composing the candidate
factorization through `h^*D` with the canonical projection recovers the original morphism
componentwise. -/
theorem compositionFamily_liftToPullback_projection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W U T : C}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    {A : DescentCompletionObjectOver (J := J) X W}
    {D : DescentCompletionObjectOver (J := J) X U}
    {h : T ⟶ U} {g : W ⟶ T}
    (α : NaturalHomOver (J := J) A D (g ≫ h))
    {V : C} (I : A.cover.Arrow) (L : D.cover.Arrow)
    (i : V ⟶ I.Y) (l : V ⟶ L.Y)
    (hIL : i ≫ I.f ≫ (g ≫ h) = l ≫ L.f) :
    compositionFamily (J := J) hSheaf
        (liftToPullback (J := J) (A := A) (D := D) (h := h) (g := g) α).toHomOver
        (pullbackProjection (J := J) D h).toHomOver
        (liftToPullback (J := J) (A := A) (D := D) (h := h) (g := g) α).naturality
        (pullbackProjection (J := J) D h).naturality
        I L i l hIL =
      α.toHomOver.family I L i l hIL := by
  let liftHom := (liftToPullback (J := J) (A := A) (D := D) (h := h) (g := g) α).toHomOver
  let projHom := (pullbackProjection (J := J) D h).toHomOver
  let hLiftNat : familyNaturality' (J := J) liftHom :=
    (liftToPullback (J := J) (A := A) (D := D) (h := h) (g := g) α).naturality
  let hProjNat : familyNaturality' (J := J) projHom :=
    (pullbackProjection (J := J) D h).naturality
  let S := compositionMiddleCover (J := J)
    (D := A) (E := pullback (J := J) D h) (H := D)
    (f := g) (g := h) I L i l
      (by simpa [Category.assoc] using hIL)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (A.restrictedLocalObject I i) (D.restrictedLocalObject L l)
    (hSheaf V (A.restrictedLocalObject I i) (D.restrictedLocalObject L l))
  intro Kp
  let hsmall :
      (Kp.f ≫ i) ≫ I.f ≫ (g ≫ h) = (Kp.f ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hIL
  let hLiftK : (Kp.f ≫ i) ≫ I.f ≫ g = 𝟙 Kp.Y ≫ Kp.base.f := by
    dsimp [S, compositionMiddleCover]
    simp [Category.assoc]
  let hProjK : 𝟙 Kp.Y ≫ Kp.base.f ≫ h = (Kp.f ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hIL
  let localComp :=
    localComposite (J := J) liftHom projHom I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hLiftK hProjK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf liftHom projHom hLiftNat hProjNat I L i l hIL)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      liftHom projHom hLiftNat hProjNat I L i l
      (by simpa [Category.assoc] using hIL)
      (hSheaf V (A.restrictedLocalObject I i) (D.restrictedLocalObject L l))
      Kp (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl hLiftK hProjK
    simpa [compositionFamily, localComp, liftHom, projHom, hLiftNat, hProjNat, Category.assoc] using hglue
  let Kb := pullbackCoverBaseArrow (J := J) D h Kp.base
  let hLiftKb : (Kp.f ≫ i) ≫ I.f ≫ (g ≫ h) = 𝟙 Kp.Y ≫ Kb.f := by
    dsimp [Kb, pullbackCoverBaseArrow]
    simp [Category.assoc]
  let hProjKb : 𝟙 Kp.Y ≫ Kb.f = (Kp.f ≫ l) ≫ L.f := by
    dsimp [Kb, pullbackCoverBaseArrow]
    simpa [Category.assoc] using hProjK
  have hcompat := α.toHomOver.compatible I I Kb L
    (Kp.f ≫ i) (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l)
    rfl hProjKb hLiftKb hsmall
  have hsource :
      (A.overlapIso (I₁ := I) (I₂ := I) (Kp.f ≫ i) (Kp.f ≫ i) rfl).hom =
        𝟙 (A.restrictedLocalObject I (Kp.f ≫ i)) :=
    overlapIso_self_hom (J := J) A I (Kp.f ≫ i)
  have hlocal :
      localComp =
        α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    calc
      localComp =
          (A.overlapIso (I₁ := I) (I₂ := I) (Kp.f ≫ i) (Kp.f ≫ i) rfl).hom ≫
            α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
          simpa [localComp, localComposite, liftHom, projHom, liftToPullbackHomOver,
            pullbackProjectionHomOver, Kb, hLiftKb, hProjKb] using hcompat.symm
      _ = α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
          simp [hsource]
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.toHomOver.family I L i l hIL)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [hsmall] using
      α.naturality I L i l hIL Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf liftHom projHom hLiftNat hProjNat I L i l hIL)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.toHomOver.family I L i l hIL)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf liftHom projHom hLiftNat hProjNat I L i l hIL)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := α.toHomOver.family I L i l hIL)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  rw [hmapLeft, hmapRight, hpull]

set_option maxHeartbeats 1200000 in
/-- Source stage 3.11, uniqueness input: composing an arbitrary morphism into `h^*D` with the
canonical projection is locally the original component followed by the identity transition on the
pulled-back cover, hence recovers the original component. -/
theorem compositionFamily_projection_eq_local
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W U T : C}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    {A : DescentCompletionObjectOver (J := J) X W}
    {D : DescentCompletionObjectOver (J := J) X U}
    {h : T ⟶ U} {g : W ⟶ T}
    (β : NaturalHomOver (J := J) A (pullback (J := J) D h) g)
    {V : C} (I : A.cover.Arrow) (K : (D.cover.pullback h).Arrow)
    (i : V ⟶ I.Y) (k : V ⟶ K.Y)
    (hIK : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := pullbackCoverBaseArrow (J := J) D h K
    let hα : i ≫ I.f ≫ (g ≫ h) = k ≫ L.f := by
      simpa [pullbackCoverBaseArrow, Category.assoc] using
        congrArg (fun q => q ≫ h) hIK
    compositionFamily (J := J) hSheaf β.toHomOver
        (pullbackProjection (J := J) D h).toHomOver
        β.naturality
        (pullbackProjection (J := J) D h).naturality
        I L i k hα =
      β.toHomOver.family I K i k hIK := by
  intro L hα
  let projHom := (pullbackProjection (J := J) D h).toHomOver
  let hProjNat : familyNaturality' (J := J) projHom :=
    (pullbackProjection (J := J) D h).naturality
  let S := compositionMiddleCover (J := J)
    (D := A) (E := pullback (J := J) D h) (H := D)
    (f := g) (g := h) I L i k
      (by simpa [L, pullbackCoverBaseArrow, Category.assoc] using hα)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (A.restrictedLocalObject I i) ((pullback (J := J) D h).restrictedLocalObject K k)
    (by
      simpa [L, pullbackCoverBaseArrow] using
        hSheaf V (A.restrictedLocalObject I i) (D.restrictedLocalObject L k))
  intro Kp
  let hsmall : (Kp.f ≫ i) ≫ I.f ≫ g = (Kp.f ≫ k) ≫ K.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) hIK
  let hcompBase :
      (Kp.f ≫ i) ≫ I.f ≫ (g ≫ h) = (Kp.f ≫ k) ≫ L.f := by
    simpa [L, pullbackCoverBaseArrow, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hα
  let hβK : (Kp.f ≫ i) ≫ I.f ≫ g = 𝟙 Kp.Y ≫ Kp.base.f := by
    dsimp [S, compositionMiddleCover]
    simp [Category.assoc]
  let hProjK : 𝟙 Kp.Y ≫ Kp.base.f ≫ h = (Kp.f ≫ k) ≫ L.f := by
    simpa [S, compositionMiddleCover, L, pullbackCoverBaseArrow, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hα
  let localComp :=
    localComposite (J := J) β.toHomOver projHom I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ k) hβK hProjK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver projHom β.naturality hProjNat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      β.toHomOver projHom β.naturality hProjNat I L i k
      (by simpa [L, pullbackCoverBaseArrow, Category.assoc] using hα)
      (by
        simpa [L, pullbackCoverBaseArrow] using
          hSheaf V (A.restrictedLocalObject I i) (D.restrictedLocalObject L k))
      Kp (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl hβK hProjK
    simpa [compositionFamily, localComp, projHom, hProjNat, Category.assoc] using hglue
  let Kb := pullbackCoverBaseArrow (J := J) D h Kp.base
  have hKpull : 𝟙 Kp.Y ≫ Kp.base.f = (Kp.f ≫ k) ≫ K.f := by
    simpa [hβK] using hsmall
  have hKbase :
      𝟙 Kp.Y ≫ Kb.f = (Kp.f ≫ k) ≫ L.f := by
    dsimp [Kb, L, pullbackCoverBaseArrow]
    simpa [Category.assoc] using congrArg (fun q => q ≫ h) hKpull
  have htarget :
      ((pullback (J := J) D h).overlapIso (I₁ := Kp.base) (I₂ := K)
          (𝟙 Kp.Y) (Kp.f ≫ k) hKpull).hom =
        (D.overlapIso (I₁ := Kb) (I₂ := L) (𝟙 Kp.Y) (Kp.f ≫ k) hKbase).hom := by
    simpa [Kb, L, hKbase] using
      pullback_overlapIso_hom (J := J) D h Kp.base K
        (𝟙 Kp.Y) (Kp.f ≫ k) hKpull
  have hprojFamD :
      projHom.family Kp.base L (𝟙 Kp.Y) (Kp.f ≫ k) hProjK =
        (D.overlapIso (I₁ := Kb) (I₂ := L) (𝟙 Kp.Y) (Kp.f ≫ k) hKbase).hom := by
    simp [projHom, pullbackProjection, Kb, L]
  have hprojFam :
      projHom.family Kp.base L (𝟙 Kp.Y) (Kp.f ≫ k) hProjK =
        ((pullback (J := J) D h).overlapIso
          (I₁ := Kp.base) (I₂ := K) (𝟙 Kp.Y) (Kp.f ≫ k) hKpull).hom := by
    exact hprojFamD.trans htarget.symm
  have hcompat := β.toHomOver.compatible I I Kp.base K
    (Kp.f ≫ i) (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ k)
    rfl hKpull hβK hsmall
  have hsource :
      (A.overlapIso (I₁ := I) (I₂ := I) (Kp.f ≫ i) (Kp.f ≫ i) rfl).hom =
        𝟙 (A.restrictedLocalObject I (Kp.f ≫ i)) :=
    overlapIso_self_hom (J := J) A I (Kp.f ≫ i)
  have hlocal :
      localComp =
        β.toHomOver.family I K (Kp.f ≫ i) (Kp.f ≫ k) hsmall := by
    calc
      localComp =
          β.toHomOver.family I Kp.base (Kp.f ≫ i) (𝟙 Kp.Y) hβK ≫
            ((pullback (J := J) D h).overlapIso
              (I₁ := Kp.base) (I₂ := K) (𝟙 Kp.Y) (Kp.f ≫ k) hKpull).hom := by
          change
            β.toHomOver.family I Kp.base (Kp.f ≫ i) (𝟙 Kp.Y) hβK ≫
                projHom.family Kp.base L (𝟙 Kp.Y) (Kp.f ≫ k) hProjK =
              β.toHomOver.family I Kp.base (Kp.f ≫ i) (𝟙 Kp.Y) hβK ≫
                ((pullback (J := J) D h).overlapIso
                  (I₁ := Kp.base) (I₂ := K) (𝟙 Kp.Y) (Kp.f ≫ k) hKpull).hom
          rw [hprojFam]
          rfl
      _ =
          (A.overlapIso (I₁ := I) (I₂ := I) (Kp.f ≫ i) (Kp.f ≫ i) rfl).hom ≫
            β.toHomOver.family I K (Kp.f ≫ i) (Kp.f ≫ k) hsmall := by
          exact hcompat.symm
      _ = β.toHomOver.family I K (Kp.f ≫ i) (Kp.f ≫ k) hsmall := by
          simp [hsource]
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k hIK)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        β.toHomOver.family I K (Kp.f ≫ i) (Kp.f ≫ k) hsmall := by
    simpa [hsmall] using
      β.naturality I K i k hIK Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver projHom β.naturality hProjNat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k hIK)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf β.toHomOver projHom β.naturality hProjNat
        I L i k hα)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := β.toHomOver.family I K i k hIK)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
  have hmiddle :
      ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ i).op.toLoc) (by rfl)).inv.toNatTrans.app (A.localObject I) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver projHom β.naturality hProjNat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' k.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ k).op.toLoc) (by rfl)).hom.toNatTrans.app (D.localObject L) =
      ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ i).op.toLoc) (by rfl)).inv.toNatTrans.app (A.localObject I) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k hIK)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' k.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ k).op.toLoc) (by rfl)).hom.toNatTrans.app (D.localObject L) := by
    rw [hpull]
    rfl
  have hrightNorm :
      ((canonicalFiberPseudofunctor X.p).mapComp' i.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ i).op.toLoc) (by rfl)).inv.toNatTrans.app (A.localObject I) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k hIK)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl ≫
        ((canonicalFiberPseudofunctor X.p).mapComp' k.op.toLoc Kp.f.op.toLoc
          ((Kp.f ≫ k).op.toLoc) (by rfl)).hom.toNatTrans.app (D.localObject L) =
      ((canonicalFiberPseudofunctor X.p).map Kp.f.op.toLoc).toFunctor.map
          (β.toHomOver.family I K i k hIK) := by
    rw [hmapRight]
    rfl
  simpa [projHom, hProjNat] using hmapLeft.trans (hmiddle.trans hrightNorm)

end HomOver

end DescentCompletionObjectOver

namespace DescentCompletionObject

/-- Source stage 3.11: pull back a total descent-completion object along a base arrow. -/
noncomputable def pullback
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    DescentCompletionObject (J := J) X where
  base := T
  object := DescentCompletionObjectOver.pullback (J := J) D.object h

@[simp]
theorem pullback_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    (pullback (J := J) D h).base = T :=
  rfl

/-- Source stage 3.11: the canonical map `h^*D ⟶ D` over `h`. -/
noncomputable def pullbackMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    Hom (J := J) (pullback (J := J) D h) D where
  base := h
  components := DescentCompletionObjectOver.pullbackProjection (J := J) D.object h

@[simp]
theorem pullbackMap_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    (pullbackMap (J := J) D h).base = h :=
  rfl

namespace Hom

/-- Source stage 3.11: the total candidate factorization through a base-changed descent object.
The base equality is kept explicit because this is the exact shape required by the strongly
cartesian universal property. -/
noncomputable def liftToPullback
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (A D : DescentCompletionObject (J := J) X) {T : C} {h : T ⟶ D.base}
    {g : A.base ⟶ T} (α : Hom (J := J) A D)
    (hαbase : g ≫ h = α.base) :
    Hom (J := J) A (pullback (J := J) D h) := by
  cases α with
  | mk abase acomp =>
    dsimp at hαbase
    subst abase
    exact
      { base := g
        components :=
          DescentCompletionObjectOver.liftToPullback (J := J)
            (A := A.object) (D := D.object) (h := h) (g := g) acomp }

@[simp]
theorem liftToPullback_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (A D : DescentCompletionObject (J := J) X) {T : C} {h : T ⟶ D.base}
    {g : A.base ⟶ T} (α : Hom (J := J) A D)
    (hαbase : g ≫ h = α.base) :
    (liftToPullback (J := J) A D α hαbase).base = g := by
  cases α with
  | mk abase acomp =>
    dsimp at hαbase
    subst abase
    rfl

/-- Source stage 3.11, total existence part: the base-change factorization composed with the
canonical projection is the original morphism. -/
theorem liftToPullback_comp_pullbackMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (A D : DescentCompletionObject (J := J) X) {T : C} {h : T ⟶ D.base}
    {g : A.base ⟶ T} (α : Hom (J := J) A D)
    (hαbase : g ≫ h = α.base) :
    Hom.compose (J := J) hSheaf
        (liftToPullback (J := J) A D α hαbase)
        (pullbackMap (J := J) D h) =
      α := by
  cases α with
  | mk abase acomp =>
    dsimp at hαbase
    subst abase
    refine Hom.ext_base_family
      (Hom.compose (J := J) hSheaf
        (liftToPullback (J := J) A D
          ({ base := g ≫ h, components := acomp } : Hom (J := J) A D) rfl)
        (pullbackMap (J := J) D h))
      ({ base := g ≫ h, components := acomp } : Hom (J := J) A D) ?_ ?_
    · simp [Hom.compose, liftToPullback, pullbackMap]
    · intro V I L i l hIL
      simpa [Hom.compose, liftToPullback, pullbackMap,
        DescentCompletionObjectOver.NaturalHomOver.compose,
        DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
        DescentCompletionObjectOver.NaturalHomOver.composeCandidate,
        DescentCompletionObjectOver.HomOver.composeOfFamilyNaturality] using
          DescentCompletionObjectOver.HomOver.compositionFamily_liftToPullback_projection
            (J := J) hSheaf acomp I L i l hIL

/-- Source stage 3.11, total uniqueness input: lifting the composite of a morphism into `h^*D`
with the canonical projection recovers the original morphism into `h^*D`. -/
theorem liftToPullback_compose_pullbackMap_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (A D : DescentCompletionObject (J := J) X) {T : C} {h : T ⟶ D.base}
    (β : Hom (J := J) A (pullback (J := J) D h)) :
    liftToPullback (J := J) A D
        (Hom.compose (J := J) hSheaf β (pullbackMap (J := J) D h))
        (by
          simp [Hom.compose, pullbackMap]
          rfl) =
      β := by
  cases β with
  | mk bbase bcomp =>
    refine Hom.ext_base_family
      (liftToPullback (J := J) A D
        (Hom.compose (J := J) hSheaf
          ({ base := bbase, components := bcomp } :
            Hom (J := J) A (pullback (J := J) D h))
          (pullbackMap (J := J) D h))
        (by
          simp [Hom.compose, pullbackMap]))
      ({ base := bbase, components := bcomp } :
        Hom (J := J) A (pullback (J := J) D h)) ?_ ?_
    · simp [liftToPullback, Hom.compose, pullbackMap]
    · intro V I K i k hIK
      let L := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object h K
      let hα : i ≫ I.f ≫ (bbase ≫ h) = k ≫ L.f := by
        simpa [L, DescentCompletionObjectOver.pullbackCoverBaseArrow, Category.assoc] using
          congrArg (fun q => q ≫ h) hIK
      have hlocal :=
        DescentCompletionObjectOver.HomOver.compositionFamily_projection_eq_local
          (J := J) hSheaf bcomp I K i k hIK
      simpa [liftToPullback, Hom.compose, pullbackMap,
        DescentCompletionObjectOver.NaturalHomOver.compose,
        DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
        DescentCompletionObjectOver.NaturalHomOver.composeCandidate,
        DescentCompletionObjectOver.HomOver.composeOfFamilyNaturality,
        L, hα] using hlocal

end Hom

set_option maxHeartbeats 800000 in
/-- Source stage 3.11: the canonical map from the base-changed descent object is strongly
cartesian for the descent-completion projection. -/
theorem pullbackMap_isStronglyCartesian
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    (projectionFunctor (J := J) hSheaf).IsStronglyCartesian
      h (pullbackMap (J := J) D h) := by
  letI := category (J := J) hSheaf
  let p' := projectionFunctor (J := J) hSheaf
  letI : p'.IsHomLift h (pullbackMap (J := J) D h) :=
    by
      change p'.IsHomLift (p'.map (pullbackMap (J := J) D h)) (pullbackMap (J := J) D h)
      exact Functor.IsHomLift.map (p := p') (pullbackMap (J := J) D h)
  refine Functor.IsStronglyCartesian.mk ?_
  intro A g α hαlift
  have hαbase : g ≫ h = α.base := by
    letI : p'.IsHomLift (g ≫ h) α := hαlift
    have hfac := IsHomLift.fac' p' (g ≫ h) α
    simpa [p', projectionFunctor, pullbackMap, Category.assoc] using hfac.symm
  let χ := Hom.liftToPullback (J := J) A D α hαbase
  refine ⟨χ, ?_, ?_⟩
  · constructor
    · have hχbase : χ.base = g := by
        simp [χ]
      rw [hχbase.symm]
      change p'.IsHomLift (p'.map χ) χ
      exact Functor.IsHomLift.map (p := p') χ
    · simpa [χ, p'] using
        Hom.liftToPullback_comp_pullbackMap (J := J) hSheaf A D α hαbase
  · intro y hy
    rcases hy with ⟨hylift, hyfac⟩
    letI : p'.IsHomLift g y := hylift
    have hybase : g = y.base := by
      have hfac := IsHomLift.fac' p' g y
      simpa [p', projectionFunctor, pullback, Category.assoc] using hfac.symm
    cases hybase
    have hyfac' : Hom.compose (J := J) hSheaf y (pullbackMap (J := J) D h) = α := by
      simpa [p'] using hyfac
    cases hyfac'
    have hleft :=
      Hom.liftToPullback_compose_pullbackMap_self (J := J) hSheaf A D y
    simpa [χ, p'] using hleft.symm

/-- Source stage 3.11: the descent-completion projection is fibred, with pullbacks represented
by pulling back the cover and descent datum. -/
theorem projectionFunctor_isFibered
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    letI := category (J := J) hSheaf
    (projectionFunctor (J := J) hSheaf).IsFibered := by
  letI := category (J := J) hSheaf
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro D T h
  exact ⟨pullback (J := J) D h, pullbackMap (J := J) D h,
    pullbackMap_isStronglyCartesian (J := J) hSheaf D h⟩

end DescentCompletionObject
end FibredCategoryMor
end CategoryTheory
